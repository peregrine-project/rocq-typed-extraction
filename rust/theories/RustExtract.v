From MetaRocq.Utils Require Import monad_utils.
From MetaRocq.Utils Require Import MRList.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Erasure.Typed Require Import ExAst.
From MetaRocq.Erasure.Typed Require Import Extraction.
From MetaRocq.Erasure.Typed Require Import CertifyingInlining.
From MetaRocq.Erasure.Typed Require Import Optimize.
From MetaRocq.Utils Require Import ResultMonad.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import List.
From Stdlib.Program Require Import Basics.
From TypedExtraction.Rust Require Import Printing.
From TypedExtraction.Rust Require Import TopLevelFixes.
From TypedExtraction.Common Require Import StringExtra.
From TypedExtraction.Common Require Import PrettyPrinterMonad.

Module P := MetaRocq.PCUIC.PCUICAst.
Module PT := MetaRocq.PCUIC.PCUICTyping.
Module T2P := MetaRocq.TemplatePCUIC.TemplateToPCUIC.
Module E := MetaRocq.Erasure.EAst.
(* [subst] — used by [native_rec_body] to rewrite a single fixpoint's
   self-reference into a direct call to the enclosing constant. *)
From MetaRocq.Erasure Require ELiftSubst.
From MetaRocq.Erasure Require EPrimitive.
From MetaRocq.Utils Require Show.
From Stdlib.Strings Require Byte PrimStringAxioms.
Module T := MetaRocq.Template.Ast.
Module TUtil := MetaRocq.Template.AstUtils.
Module EF := MetaRocq.Erasure.ErasureFunction.
Module Ex := MetaRocq.Erasure.Typed.ExAst.

Import MonadNotation.

Open Scope bs_scope.


Local Definition indent_size := 2.

(* Maximum leading indentation. Deeply nested terms (e.g. a long unary-nat
   [S (S (... ))] spine) would otherwise accumulate O(depth^2) leading
   whitespace, since each level indents [indent_size] beyond its parent. Rust
   ignores whitespace outside tokens, so capping the indent only bounds the
   generated-source size and leaves the program semantically identical. *)
Local Definition max_indent := 40.

(* Shadow [push_indent] within this Rust printer with a capped version, anchored
   to the current nesting indent rather than the absolute column (via
   [get_indent] at each use site below). Other printers over
   [PrettyPrinterMonad] (e.g. Elm, whose output is indentation-sensitive) keep
   the uncapped behaviour. *)
Local Definition push_indent (n : nat) : PrettyPrinter unit :=
  PrettyPrinterMonad.push_indent (Nat.min n max_indent).

Local Notation "a ^ b" := (a ++ b).

Section FixEnv.
Context (Σ : Ex.global_env).
Context (remaps : remaps).
(* A printing config for Rust *)
Class RustPrintConfig :=
  { term_box_symbol : string;
    type_box_symbol : string;
    any_type_symbol : string;
    print_full_names : bool (* use fully-qualified names as identifiers to avoid name clashes *)}.

Context `{RustPrintConfig}.

Import Kernames.

Definition ind_attr_map := inductive -> string.

Context (ind_attrs : ind_attr_map).

Definition lookup_mind (name : kername) : option Ex.mutual_inductive_body :=
  match Ex.lookup_env Σ name with
  | Some (Ex.InductiveDecl mib) => Some mib
  | _ => None
  end.

Definition lookup_ind_decl (ind : inductive) : result Ex.one_inductive_body string :=
  match Ex.lookup_env Σ (inductive_mind ind) with
  | Some (Ex.InductiveDecl {| Ex.ind_bodies := oibs |}) =>
    match nth_error oibs (inductive_ind ind) with
    | Some body => Ok body
    | None => Err ("Could not find inductive "
                     ++ (string_of_nat (inductive_ind ind))
                     ++ " in mutual inductive " ++ (string_of_kername (inductive_mind ind)))
    end
  | _ => Err ("Could not find inductive "
                ++ (string_of_kername (inductive_mind ind)) ++ " in environment")
  end.

(* We clean global identifiers but do not generate any form of fresh names
   to make it straightforward to know what extracted code maps to what. *)
Definition clean_global_ident (s : string) : string :=
  replace_char "." "_" (replace_char "'" "_" s).

(* Get identifier for a global constant function given its kername, without
   taking remappings into account *)
Definition const_global_ident_of_kername (kn : kername) :=
  clean_global_ident (if print_full_names then (string_of_kername kn) else (snd kn)).

(* Get identifier for a global constant meant to be used as a type, without
   taking remappings into account. This is also used for [inductive]. *)
Definition ty_const_global_ident_of_kername (kn : kername) :=
  capitalize (clean_global_ident (if print_full_names then string_of_kername kn else (snd kn))).

(* Get identifier for a global type alias taking remappings into account *)
Definition get_ty_const_ident (name : kername) : _ :=
  match remap_inline_constant remaps name with
  | Some s => s
  | None => ty_const_global_ident_of_kername name
  end.

(* Get identifier for an inductive taking remappings into account *)
Definition get_ind_ident (ind : inductive) : PrettyPrinter _ :=
  match remap_inductive remaps ind with
  | Some rem => ret (re_ind_name rem)
  | None =>
    oib <- wrap_result (lookup_ind_decl ind) id;;
    let kn := (fst (inductive_mind ind), Ex.ind_name oib) in
    ret (ty_const_global_ident_of_kername kn)
  end.

(* Fine to remove primes here as we generate fresh names *)
Definition clean_local_ident (name : ident) : string :=
  remove_char "'" name.

Definition is_polymorphic (cst : Ex.constant_body) : bool :=
  (0 <? #|fst (Ex.cst_type cst)|)%nat.

Definition print_ind (ind : inductive) : PrettyPrinter unit :=
  get_ind_ident ind >>= fun x => append x.

Definition print_parenthesized
           (parenthesize : bool)
           (print : PrettyPrinter unit) : PrettyPrinter unit :=
  if parenthesize then
    append "(";; print;; append ")"
  else
    print.

Definition print_parenthesized_with par_start par_end :=
  fun (parenthesize : bool) (print : PrettyPrinter unit) =>
  if parenthesize then append par_start;; print;; append par_end else print.

Definition parenthesize_app_head (t : term) : bool :=
  match t with
  | tLambda _ _
  | tLetIn _ _ _
  | tCase _ _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition parenthesize_app_arg (t : term) : bool :=
  match t with
  | tLambda _ _
  | tLetIn _ _ _
  | tApp _ _
  | tCase _ _ _
  | tProj _ _
  | tFix _ _ => true
  | _ => false
  end.

Definition parenthesize_case_discriminee (t : term) : bool :=
  match t with
  | tLetIn _ _ _
  | tCase _ _ _ => true
  | _ => false
  end.

Definition fresh (name : ident) (used : list ident) : ident :=
  if existsb (bytestring.String.eqb name) used then
    (fix f n i :=
       match n with
       | 0 => "unreachable"
       | S n =>
         let numbered_name := bytestring.String.append name (MRString.string_of_nat i) in
         if existsb (bytestring.String.eqb numbered_name) used then
           f n (S i)
         else
           numbered_name
       end) (S (List.length used)) 2
  else
    name.

Import BasicAst.

Definition fresh_ident (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "x" (Γ ++ used_names))
  | nNamed name => ret (fresh (clean_local_ident name) (Γ ++ used_names))
  end.

Definition fresh_ty_arg_name (name : name) (Γ : list ident) : PrettyPrinter ident :=
  used_names <- get_used_names;;
  match name with
  | nAnon => ret (fresh "a" (Γ ++ used_names))
  | nNamed name => ret (fresh (clean_local_ident name) (Γ ++ used_names))
  end.

(* Rocq's primitive types have no declaration to print: a primitive integer is an
   [i64] (its values are below 2^63) and a primitive string, an array of bytes, is
   a byte slice. *)
Definition prim_int_kn : kername :=
  (MPfile ["PrimInt63"; "Int63"; "Cyclic"; "Numbers"; "Corelib"], "int").

Definition prim_string_kn : kername :=
  (MPfile ["PrimString"; "Strings"; "Corelib"], "string").

Definition parenthesize_ty_app_arg (t : box_type) : bool :=
  match t with
  | TApp _ _ => true
  | _ => false
  end.

Fixpoint print_type_aux (Γ : list ident) (t : box_type) (args : list (PrettyPrinter unit)) :=
  match t with
  | TBox => append type_box_symbol
  | TAny => append any_type_symbol
  | TArr dom cod =>
    append "&'a dyn Fn(";;
    print_type_aux Γ dom [];;
    append ") -> ";;
    print_type_aux Γ cod []
  | TApp head arg =>
    print_type_aux Γ head (print_type_aux Γ arg [] :: args)
  | TVar n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound TVar " ++ string_of_nat n)
    end
  | TInd ind =>
    if remap_inductive remaps ind then
      print_ind ind;;
      print_parenthesized_with
        "<" ">"
        (0 <? #|args|)%nat
        (monad_append_join (append ", ") args)
    else
      append "&'a ";;
      print_ind ind;;
      append "<";;
      monad_append_join (append ", ") (append "'a" :: args);;
      append ">"

  | TConst name =>
    if eq_kername name prim_int_kn then append "i64" else
    if eq_kername name prim_string_kn then append "&'a [u8]" else
    append ((get_ty_const_ident name) ++ "<");;
    monad_append_join (append ", ") (append "'a" :: args);;
    append ">"
  end.

Definition print_type Γ t := print_type_aux Γ t [].

(* Compare an argument list to [tRel (k-1); ...; tRel 0], i.e. the [k] outer
   lambda variables in application order (the shape of a fully eta-expanded
   fixpoint [(fix ..) x1 .. xk]).  [doms] lists the domain types of the outer
   lambdas still to be matched, outermost first. *)
Fixpoint nrb_is_eta_args (doms : list box_type) (i : nat) (args : list term) : bool :=
  match i, args with
  | 0, nil => true
  | S i', tRel j :: args' => andb (Nat.eqb j i') (nrb_is_eta_args (tl doms) i' args')
  (* An erased type/proof argument is a [()] value, interchangeable with the
     outer slot it fills only when that slot is erased too.  This covers
     polymorphic recursors [λA. (fix) box l1 ..] whose type slot erases to a
     box rather than the [A] variable.  A box in a slot of any other type would
     print a [()] where the signature expects a value. *)
  | S i', tBox :: args' =>
    match doms with
    | TBox :: doms' => nrb_is_eta_args doms' i' args'
    | _ => false
    end
  | _, _ => false
  end.

(* Native recursion.  A single (non-mutual) fixpoint constant [kn] -- possibly
   eta-wrapped as [λx1..λxk. (fix f := λ.. body) x1 .. xk] (the shape erasure
   produces) -- is compiled to a native recursive [fn].  Strip the [k] outer
   lambdas; when the core is the fixpoint applied to exactly those [k] variables
   and its body refers to none of them, drop the eta wrapper and return the
   fixpoint body with its self-variable replaced by [tConst kn].  A bare
   fixpoint under outer lambdas keeps them, and its self-variable becomes
   [kn] applied to them, so it may capture them.  Recursive calls then print as
   direct [self.<name>(..)] calls (see [print_const]) -- no heap
   [Cell<Option<&dyn Fn>>], no dynamic dispatch.  Any other shape (mutual fix, an
   eta-wrapped fix whose body captures an outer variable, or a fix applied to
   anything else) is returned unchanged and handled by [print_term]'s [tFix]
   closure-cell case.  [doms] lists the domain types of the outer lambdas. *)
Definition native_rec_body (doms : list box_type) (kn : kername) (body : term) : term :=
  let fix strip (acc : list name) (b : term) : list name * term :=
    match b with
    | tLambda na b' => strip (na :: acc) b'
    | _ => (acc, b)
    end in
  let '(acc, core) := strip nil body in
  let k := #|acc| in
  let '(hd, args) := EAstUtils.decompose_app core in
  match hd with
  | tFix (d :: nil) 0 =>
    if andb (nrb_is_eta_args doms k args) (ELiftSubst.closedn 1 (E.dbody d)) then
      ELiftSubst.subst [tConst kn] 0 (E.dbody d)
    else match args with
    | nil =>
      let inner := ELiftSubst.subst
                     [mkApps (tConst kn) (rev_map tRel (seq 0 k))] 0 (E.dbody d) in
      fold_left (fun t na => tLambda na t) acc inner
    | _ => body
    end
  | _ => body
  end.

(* Get number of arguments that a constant expects when we print it *)
Definition get_num_inline_args (kn : kername) : PrettyPrinter nat :=
  cst <- wrap_option
           (Ex.lookup_constant Σ kn)
           ("Could not find constant " ++ (string_of_kername kn));;
  (* A config-path remap keeps the erased body, but its arity is the arity of
     the constant's TYPE (the remap supplies a fixed uncurried Rust body), so
     count type arrows there rather than leading lambdas of the body. *)
  match remap_constant remaps kn with
  | Some _ => ret #|fst (decompose_arr (snd (Ex.cst_type cst)))|
  | None =>
  match Ex.cst_body cst with
  | None => ret #|fst (decompose_arr (snd (Ex.cst_type cst)))|
  | Some body =>
    (* A single (non-mutual) fixpoint is compiled as a native recursive [fn]
       (see [print_constant]); after [native_rec_body] its arity is the number
       of leading lambdas, so callers emit a direct saturated call. *)
    let body := native_rec_body (fst (decompose_arr (snd (Ex.cst_type cst)))) kn body in
    let fix count body ty :=
        match body, ty with
        | tLambda _ body, TArr dom cod => S (count body cod)
        | _, _ => 0
        end in
    ret (count body (snd (Ex.cst_type cst)))
  end
  end.

Definition print_app
           (head : PrettyPrinter unit)
           (args : list (PrettyPrinter unit)) : PrettyPrinter unit :=
  col <- get_indent;;
  head;;
  push_indent (col + indent_size);;
  append "(";;
  (if 0 <? #|args| then append_nl else ret tt)%nat;;
  monad_append_join (append ",";; append_nl) args;;
  append ")";;
  pop_indent.

Definition print_constructor
           (ind : inductive)
           (c : nat)
           (args : list (PrettyPrinter unit)) :=
  match remap_inductive remaps ind with
  | Some rem =>
    s <- wrap_option (nth_error (re_ind_ctors rem) c)
                     ((string_of_inductive ind)
                      ^ "' does not remap enough constructors ");;
    if (0 <? #|args|)%nat then
      print_app (append s) args
    else
      append s
  | None =>
    oib <- wrap_result (lookup_ind_decl ind) id;;
    '(ctor, _, _) <- wrap_option
                    (nth_error (Ex.ind_ctors oib) c)
                    ("Could not find ctor "
                     ^ string_of_nat c
                     ^ " for inductive "
                     ^ (string_of_inductive ind));;

    col <- get_indent;;
    push_indent (col + indent_size);;
    append "self.alloc(";;
    append_nl;;
    let head := print_ind ind;; append "::";; append (clean_global_ident ctor) in
    let final_args := append "PhantomData" :: args in
    print_app head final_args;;
    append ")";;
    pop_indent
  end.

(* The body of a Rust byte string literal: every byte other than an ASCII letter,
   digit or space is written as a hexadecimal escape. *)
Definition hex_digit (n : nat) : string :=
  nth n ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "a"; "b"; "c"; "d"; "e"; "f"] "0".

Fixpoint rust_bytes (s : string) : string :=
  match s with
  | String.EmptyString => ""
  | String.String b r =>
    let n := Byte.to_nat b in
    let range lo hi := andb (Nat.leb lo n) (Nat.leb n hi) in
    let plain := orb (range 32 32) (orb (range 48 57) (orb (range 65 90) (range 97 122))) in
    (if plain then String.String b String.EmptyString
     else "\x" ++ hex_digit (Nat.div n 16) ++ hex_digit (Nat.modulo n 16)) ++ rust_bytes r
  end%nat.

Definition print_prim (p : EPrimitive.prim_val term) : PrettyPrinter unit :=
  match projT2 p with
  | EPrimitive.primIntModel i => append (Show.string_of_prim_int i ++ "i64")
  | EPrimitive.primStringModel s =>
    let bytes := String.concat "" (map Show.char63_to_string (PrimStringAxioms.to_list s)) in
    append ("&b""" ++ rust_bytes bytes ++ """[..]")
  | _ => printer_fail "Cannot handle Rocq primitive floats and arrays yet"
  end.

(* A constant whose result type is erased, applied to more arguments than its type
   has arrows, as the projection of an erased field is: the result is the box, and
   the remaining arguments are terms of a total language, so they are dropped. *)
Definition erased_result_arity (kn : kername) : option nat :=
  match Ex.lookup_constant Σ kn with
  | Some cst =>
    let '(doms, cod) := decompose_arr (snd (Ex.cst_type cst)) in
    match cod with
    | TBox => Some #|doms|
    | _ => None
    end
  | None => None
  end.

Fixpoint mentions_tvar (i : nat) (t : box_type) : bool :=
  match t with
  | TVar n => (n =? i)%nat
  | TArr a b | TApp a b => orb (mentions_tvar i a) (mentions_tvar i b)
  | _ => false
  end.

Fixpoint ty_args (t : box_type) : list box_type :=
  match t with
  | TApp h a => (ty_args h ++ [a])%list
  | _ => []
  end.

Definition ctor_field_types (ind : inductive) (c : nat) : list box_type :=
  match Ex.lookup_env Σ (inductive_mind ind) with
  | Some (Ex.InductiveDecl mib) =>
    match nth_error (Ex.ind_bodies mib) (inductive_ind ind) with
    | Some oib =>
      match nth_error (Ex.ind_ctors oib) c with
      | Some (_, fields, _) => map snd fields
      | None => []
      end
    | None => []
    end
  | _ => []
  end.

(* Whether an argument of type [dom] lets rustc infer the type variable [i].  A
   constructor application only does so through the type parameters that its own
   fields mention: [Left 0] says nothing about [B] in [Either A B]. *)
Definition determines_tvar (i : nat) (dom : box_type) (arg : term) : bool :=
  andb (mentions_tvar i dom)
  match EAstUtils.decompose_app arg with
  | (tConstruct ind c _, _) =>
    match ty_args dom with
    | [] => true
    | targs =>
      let fields := ctor_field_types ind c in
      existsb id (mapi (fun p targ => andb (mentions_tvar i targ) (existsb (mentions_tvar p) fields)) targs)
    end
  | _ => true
  end.

(* The type arguments of a call, printed only when rustc cannot infer one of them.
   Erasure removed the explicit type argument, and a type variable that occurs
   neither in the result type nor in what an argument determines has no effect on
   the program, so any type does; [()] satisfies the [Copy] bound of the parameter. *)
Definition call_turbofish (kn : kername) (args : list term) : string :=
  match Ex.lookup_constant Σ kn, remap_constant remaps kn, remap_inline_constant remaps kn with
  | Some cst, None, None =>
    let '(tvars, ty) := Ex.cst_type cst in
    let '(doms, cod) := decompose_arr ty in
    let undetermined i :=
        andb (negb (mentions_tvar i cod))
             (negb (existsb (fun '(d, a) => determines_tvar i d a) (combine doms args))) in
    let flags := mapi (fun i _ => undetermined i) tvars in
    if orb (Nat.ltb #|args| #|doms|) (negb (existsb id flags)) then ""
    else "::<" ++ String.concat ", " (map (fun u : bool => if u then "()" else "_") flags) ++ ">"
  | _, _, _ => ""
  end.

Definition print_const_turbofish (turbofish : string) (kn : kername) (args : list (PrettyPrinter unit))
  : PrettyPrinter unit :=
  num_inline_args <- get_num_inline_args kn;;
  let (expr, num_inline_args) :=
      if (#|args| <? num_inline_args)%nat then
        (* Not enough args, use curried version *)
        ("self." ^ const_global_ident_of_kername kn ^ "__curried", 0)
      else
        (match remap_inline_constant remaps kn with
         | Some s => s
         | None => "self." ^ const_global_ident_of_kername kn ^ turbofish
         end, num_inline_args) in
  head_col <- get_indent;;
  let head := append expr in
  let args_in_head := firstn num_inline_args args in
  let args_in_tail := skipn num_inline_args args in
  print_app head args_in_head;;
  push_indent (head_col + indent_size);;
  let it_app a :=
      append "(";;
      append_nl;;
      a;;
      append ")" in
  monad_append_concat (map it_app args_in_tail);;
  pop_indent.

(* An inductive with a type parameter that no constructor field mentions may be a
   family indexed by a type, as [GExp] with [nat : Nat -> GExp Nat] and
   [bool : Bool -> GExp Bool]: erasure loses the index, and the branches of a match
   have different Rust types although each has the type the match asks for in the
   source.  Such a branch is printed under [__cast], the counterpart of OCaml's
   [Obj.magic]; the program's typing in Rocq guarantees that the two types agree. *)
Definition is_type_family (oib : Ex.one_inductive_body) : bool :=
  let fields := flat_map (fun '(_, fs, _) => map snd fs) (Ex.ind_ctors oib) in
  existsb id (mapi (fun i _ => negb (existsb (mentions_tvar i) fields)) (Ex.ind_type_vars oib)).

Section print_term.
  Context (print_term : list ident -> term -> PrettyPrinter unit).

  Definition print_case Γ ind npars discr brs : PrettyPrinter unit :=
    col <- get_indent;;
    push_indent col;;

    append "match ";;
    print_term Γ discr;;
    append " {";;

    oib <- wrap_result (lookup_ind_decl ind) id;;
    let rem := remap_inductive remaps ind in
    let family := is_type_family oib in

    push_indent (col + indent_size);;
    (fix print_cases
         (brs : list (list name * term))
         (ctors : list (ident * list (name * box_type) * nat))
         (c : nat) :=
       match brs, ctors with
       | [], [] => ret tt
       | (bctx, t) :: branches, (ctor_name, data, _) :: ctors =>
         append_nl;;

         match rem with
         | Some rem =>
           s <- wrap_option (nth_error (re_ind_ctors rem) c)
                            ((string_of_inductive ind)
                             ^ "' does not remap enough constructors");;
           append s

         | None =>
           append "&";;
           print_ind ind;;
           append "::";;
           append (clean_global_ident ctor_name)
         end;;

         push_indent (col + 2*indent_size);;
         (fix print_branch (bctx : list name) (args : list ident) (Γ : list ident) {struct bctx} :=
            match bctx with
            | [] =>
              (* In Rocq, parameters are not part of branches. But
            erasure adds the parameters to each constructor, so we
            need to get those out of the way first. These won't have
            any uses so we just print _. In addition, we add a phantom
            data when not remapped to make it valid to always have
            lifetimes. That gives another underscores. *)
              let nextra := if rem then npars else S npars in
              let extra := List.repeat "_" nextra in
              let args := (extra ++ (rev args))%list in
              print_parenthesized (0 <? #|args|)%nat (append_join ", " args);;
              append " => {";;
              append_nl ;;
              (if family then
                 append "__cast({ ";; print_term Γ t;; append " })"
               else
                 print_term Γ t)
            | name :: bctx0 =>
              name <- fresh_ident name Γ;;
              print_branch bctx0 (name :: args) (name :: Γ)
            end) (List.rev bctx) [] Γ;;

         pop_indent;;
         append_nl;;
         append "},";;

         print_cases branches ctors (S c)
       | _, _ => printer_fail "wrong number of case branches compared to inductive"
       end) brs (Ex.ind_ctors oib) 0;;

    pop_indent;;
    append_nl;;
    append "}";;

    pop_indent.

  Definition print_remapped_case Γ ind discr brs eliminator : PrettyPrinter unit :=
    col <- get_indent;;
    push_indent col;;

    append (eliminator ^ "(");;

    oib <- wrap_result (lookup_ind_decl ind) id;;

    push_indent (col + indent_size);;

    let fix map_cases (brs : list (list name * term)) :=
      match brs with
      | [] => []
      | (bctx, t) :: brs0 =>
          ((fix print_branch (bctx : list name) (args : list ident) (Γ : list ident) {struct bctx} :=
           match bctx with
           | [] =>
               let args := rev args in

               append_nl;;
               append_concat (map (fun a => a ^ ", ") args);;
               append "{";;

               push_indent (col + 2*indent_size);;
               append_nl;;
               print_term Γ t;;
               pop_indent;;

               append_nl;;
               append "},"

           | name :: bctx0 =>
               name <- fresh_ident name Γ;;
               print_branch bctx0 (name :: args) (name :: Γ)
           end) bctx [] Γ) :: map_cases brs0
      end in
    monad_append_concat (map_cases brs);;

    append_nl;;
    print_term Γ discr;;

    append ")";;
    pop_indent;;
    pop_indent.
End print_term.

Definition print_const := print_const_turbofish "".

Definition needs_block (t : term) : bool :=
  match t with
  | tLetIn _ _ _
  | tFix _ _ => true
  | _ => false
  end.

Fixpoint print_term (Γ : list ident) (t : term) {struct t} : PrettyPrinter unit :=
  match t with
  | tBox => append term_box_symbol
  | tRel n =>
    match nth_error Γ n with
    | Some name => append name
    | None => printer_fail ("unbound tRel " ++ string_of_nat n)
    end
  | tVar ident => printer_fail ("tVar " ++ ident)
  | tEvar _ _ => printer_fail "unexpected evar"
  | tLambda name t =>
    name <- fresh_ident name Γ;;
    col <- get_indent;;
    push_indent col;;
    append ("self.closure(move |" ++ name ++ "| {");;

    push_indent (col + indent_size);;
    append_nl;;
    let Γ := name :: Γ in
    print_term Γ t;;
    pop_indent;;
    append_nl;;
    append "})";;
    pop_indent

  | tLetIn na val body =>
    name <- fresh_ident na Γ;;
    col <- get_indent;;

    push_indent col;;
    append ("let " ++ name ++ " =");;
    (if needs_block val then append " {" else ret tt);;

    push_indent (col + indent_size);;
    append_nl;;
    print_term Γ val;;
    pop_indent;;

    (if needs_block val then
       append_nl;;
       append "};"
     else
       append ";");;

    append_nl;;

    print_term (name :: Γ) body;;
    pop_indent

  | tApp head arg =>

    (fix f head args_printed {struct head} :=
       match head with
       | tApp head arg =>
         let printed_arg :=
             (if needs_block arg then append "{ " else ret tt);;
             print_term Γ arg;;
             if needs_block arg then append " }" else ret tt in
         f head (printed_arg :: args_printed)

       | tConstruct ind i [] => print_constructor ind i args_printed
       | tConstruct ind i (_ :: _) =>
           printer_fail ("Costructors-as-blocks is not supported: "
                         ^ (string_of_kername ind.(inductive_mind)))

       | tConst kn =>
         match erased_result_arity kn with
         | Some n =>
           if (n <? #|args_printed|)%nat then print_const kn (firstn n args_printed)
           else print_const kn args_printed
         | None =>
           print_const_turbofish (call_turbofish kn (snd (EAstUtils.decompose_app t))) kn args_printed
         end

       | tBox => append term_box_symbol

       | _ =>
         (* For other heads we might need to guide type inference by repeatedly
            applying a hint function *)
         append (String.concat "" (repeat "hint_app(" #|args_printed|));;
         (if needs_block head then append "{ " else ret tt);;
         print_term Γ head;;
         (if needs_block head then append " }" else ret tt);;
         append ")";;
         monad_fold_left
           (fun pref a => append pref;; a;; append ")";; ret ")(") args_printed "(";;
         ret tt

       end) head [if needs_block arg then
                    append "{ ";; print_term Γ arg;; append " }"
                  else
                    print_term Γ arg]

  | tConst kn => print_const kn []
  | tConstruct ind i [] => print_constructor ind i []
  | tConstruct ind i (_ :: _) =>
                 printer_fail ("Costructors-as-blocks is not supported: "
                         ^ (string_of_kername ind.(inductive_mind)))

  | tCase (ind, npars) discr brs =>
    match brs with
    | [] =>
      (* If it's a match on an empty type, we just panic, since we should never reach this code *)
      append "panic!(""Absurd case!"")"
    | _ =>
      match remap_inductive remaps ind with
      | Some rem =>
        match re_ind_match rem with
        | Some s => print_remapped_case print_term Γ ind discr brs s
        | None => print_case print_term Γ ind npars discr brs
        end
      | None => print_case print_term Γ ind npars discr brs
      end
    end
  | tFix defs i =>
    (* Rust does not have recursive closures. Instead, we have to do a trick
       where we recurse through the heap: we first create a cell on the heap
       that will point to the closure. Then, we create the closure that unwraps
       the heap location to get itself. Finally, we put the closure into that heap
       location and it is ready to use. It is complicated by the fact that fix points
       are also mutual and we must create many heap cells before assigning the closures,
       and each closure also needs its own clone of each cell. *)
    col <- get_indent;;
    push_indent col;;

    (* Generate names and allocate cells *)
    '(Γ, cells)
    <- monad_fold_left
         (fun '(Γ, cells) d =>
            (* This is hacky, but instead of putting proper names in the context,
               we put a string that unwraps the cell in the context.
               This is simpler for now, but as a side effect we need to push a use
               since the name won't be in the context. In the future we should unwrap it after the
               first closure or find a better way to handle this. *)
            na <- fresh_ident (EAst.dname d) Γ;;
            push_use na;;
            append ("let " ++ na ++ " = self.alloc(std::cell::Cell::new(None));");;
            append_nl;;
            ret ((bytestring.String.append na ".get().unwrap()") :: Γ, na :: cells))
         defs (Γ, []);;

    let cells := rev cells in

    (* Print closures. *)
    monad_fold_left
      (fun _ '(print_def, cell) =>
         append (cell ++ ".set(Some(");;
         push_indent (col + indent_size);;
         append_nl;;
         print_def;;
         append "));";;
         pop_indent;;
         append_nl)
      (combine
         (map (fun d => print_term Γ (EAst.dbody d)) defs)
         cells)
      tt;;

    append ((nth i cells "") ++ ".get().unwrap()");;
    pop_indent

  | tProj (mkProjection ind pars c) t =>
    printer_fail ("unhandled tProj on " ^ (string_of_kername (inductive_mind ind)))

  | tCoFix _ _ => printer_fail "Cannot handle tCoFix yet"
  | tPrim p => print_prim p
  | tLazy _ => printer_fail "Cannot handle lazy yet"
  | tForce _ => printer_fail "Cannot handle force yet"
  end.

Definition print_constant
           (kn : kername)
           (type : (list name * box_type))
           (body : E.term) : PrettyPrinter unit :=

  let rname := const_global_ident_of_kername kn in

  name_col <- get_indent;;
  push_indent name_col;;

  let (type_vars, ty) := type in
  Γty <- monad_fold_left (fun Γty name => name <- fresh_ty_arg_name name Γty;;
                                          ret (Γty ++ [name])%list)
                         type_vars [];;

  (* Print version with inlined args *)
  match remap_constant remaps kn with
  | Some s => append (StringExtra.replace "##name##" rname s)
  | None =>
    if remap_inline_constant remaps kn then
      ret tt
    else
      append ("fn " ++ rname);;
      print_parenthesized_with
        "<" ">" (0 <? #|Γty|)%nat
        (append_join ", " (map (fun na => na ++ ": Copy") Γty));;
      append "(&'a self";;

      (* Native recursion: rewrite a single fixpoint's self-reference to a
         direct call to this constant, so recursion compiles to a native
         recursive [fn] rather than a heap [Cell<Option<&dyn Fn>>]. *)
      let body := native_rec_body (fst (decompose_arr ty)) kn body in
      (fix print_top Γ body ty :=
         match body, ty with
         | tLambda na body, TArr dom cod =>
           na <- fresh_ident na Γ;;
           append (", " ++ na ++ ": ");;
           print_type Γty dom;;
           print_top (na :: Γ) body cod
         | _, _ =>
           append ") -> ";;
           print_type Γty ty;;
           append " {";;

           push_indent (name_col + indent_size);;
           append_nl;;

           push_use rname;;
           print_term Γ body;;

           pop_indent;;
           append_nl;;
           append "}"
         end) [] body ty
  end;;

  (* Print curried version if there were inlined args *)
  num_inline_args <- get_num_inline_args kn;;
  (if (0 <? num_inline_args)%nat then
     append_nl;;
     append ("fn " ++ rname ++ "__curried");;
     print_parenthesized_with
       "<" ">" (0 <? #|Γty|)%nat
       (append_join ", " (map (fun na => na ++ ": Copy") Γty));;
     append "(&'a self) -> ";;
     print_type Γty ty;;
     append " {";;

     push_indent (name_col + indent_size);;
     append_nl;;

     push_use (rname ++ "__curried");;
     (* Eta-expand to the FULL arity reported by [get_num_inline_args], rather
        than to the number of leading lambdas of the erased body.  Those two
        disagree for a fixpoint-bodied constant (whose body is [λ.. (fix ..)])
        and for a remapped constant (whose body is irrelevant, the arity coming
        from the type).  Expanding to too few arguments makes [print_const] see
        an under-application and route the call back to this very wrapper, so
        [foo__curried] would call itself and diverge. *)
     let eta_term :=
       (fix wrap (k : nat) (t : term) : term :=
          match k with
          | 0 => t
          | S k' => wrap k' (tLambda nAnon t)
          end) num_inline_args
         (mkApps (tConst kn) (rev_map tRel (seq 0 num_inline_args))) in
     print_term [] eta_term;;

     pop_indent;;
     append_nl;;
     append "}"
   else
     ret tt);;

  pop_indent;;
  ret tt.

Open Scope program_scope.

Definition print_ind_ctor_definition
           (Γ : list ident)
           (ctor_name : ident)
           (data : list (name * box_type)) : PrettyPrinter unit :=
  append (clean_global_ident ctor_name);;

  (* Make sure we always take a lifetime parameter in data types *)
  append "(";;

  (* All constructors take a PhantomData as their first argument which ensures that
     Rust does not complained about unused lifetimes/type parameters.
     This phantom type is a 'a lifetimed reference to a tuple of all the type args. *)
  let print_phantom :=
      append "PhantomData<&'a ";;
      (if (#|Γ| =? 0)%nat then
         append "()"
       else
         print_parenthesized (1 <? #|Γ|)%nat (append_join ", " Γ));;
      append ">" in
  let print_datas := print_phantom :: map (print_type Γ ∘ snd) data in
  monad_append_join (append ", ") print_datas;;

  append ")".

Definition print_mutual_inductive_body
           (kn : kername)
           (mib : Ex.mutual_inductive_body) : PrettyPrinter unit :=
  col <- get_indent;;
  push_indent col;;

  names <-
  (fix print_ind_bodies
       (l : list Ex.one_inductive_body)
       (prefix : PrettyPrinter unit)
       (i : nat) :=
     match l with
     | [] => ret tt
     | oib :: l =>

       prefix;;

       append (ind_attrs (mkInd kn i));;
       append_nl;;
       append "pub enum ";;
       print_ind (mkInd kn i);;

       (* Add type parameters. Note that since we are in prenex form,
          our context will have last type parameter last, not first. *)
       Γ <- monad_fold_left
              (fun Γ name =>
                 name <- fresh_ty_arg_name (tvar_name name) Γ;;
                 ret (Γ ++ [name])%list) (ind_type_vars oib) [];;

       append "<";;
       append_join ", " ("'a" :: Γ);;
       append "> {";;

       (* Print constructors *)
       push_indent (col + indent_size);;
       append_nl;;

       monad_append_join (append ",";; append_nl)
                         (map (fun '(name, data, _) =>
                                 print_ind_ctor_definition Γ name data)
                              (Ex.ind_ctors oib));;

       pop_indent;;
       append_nl;;
       append "}";;

       print_ind_bodies l append_nl (S i)
     end) (Ex.ind_bodies mib) (ret tt) 0;;
  pop_indent;;
  ret names.

Definition print_type_alias
           (nm : kername)
           (tvars : list type_var_info)
           (bt : box_type) : PrettyPrinter unit :=
  let rname := ty_const_global_ident_of_kername nm in
  match remap_constant remaps nm with
  | Some s => append (StringExtra.replace "##name##" rname s)
  | None =>
    append ("type " ++ rname ++ "<");;
    Γrev <- monad_fold_left (fun Γ tvar => name <- fresh_ty_arg_name (tvar_name tvar) Γ;;
                                           ret (name :: Γ))
                          tvars [];;
    let Γ := rev Γrev in
    append_join ", " ("'a" :: Γ);;
    append "> = ";;
    print_type Γ bt;;
    append ";"
  end.

Fixpoint print_decls_aux
         (decls : list (kername * bool * Ex.global_decl))
         (prefix : PrettyPrinter unit) : PrettyPrinter unit :=
  match decls with
  | [] => ret tt
  | (kn, has_deps, decl) :: decls =>
    match decl with
    | Ex.ConstantDecl {| Ex.cst_type := type; Ex.cst_body := Some body |} =>
      prefix;; print_constant kn type body
    | Ex.InductiveDecl mib =>
      if remap_inductive remaps (mkInd kn 0) then
        ret tt
      else
        prefix;; print_mutual_inductive_body kn mib
    | Ex.TypeAliasDecl (Some (tvars, bt)) => prefix;; print_type_alias kn tvars bt
    | _ => ret tt
    end;;
    print_decls_aux decls (append_nl;; append_nl)
  end.

Definition print_decls decls :=
  print_decls_aux decls (ret tt).

Class Preamble :=
  { top_preamble : list string;
    program_preamble : list string }.

Context `{Preamble}.

Definition print_program : PrettyPrinter unit :=
  sig_col <- get_indent;;
  push_indent sig_col;;

  monad_append_join append_nl (map append top_preamble);;

  let is_const '(kn, decl) :=
      match decl with
      | Ex.ConstantDecl _ => true
      | _ => false
      end in

  (* Filtering out empty type declarations *)
  (* TODO: possibly, move to extraction (requires modifications of the correctness proof) *)
  let Σ := filter (fun '(kn,d) => negb (is_empty_type_decl d)) Σ in

  ind_names <- print_decls_aux (filter (negb ∘ is_const) (List.rev Σ))
                               (append_nl;; append_nl);;

  (* First print a structure that has the arena and all
     (non-polymorphic) constants in the program *)
  let constants :=
      flat_map (fun '(kn, has_deps, decl) =>
                  match decl with
                  | Ex.ConstantDecl cst => [(kn, has_deps, cst)]
                  | _ => []
                  end) (List.rev Σ) in

  append_nl;;
  append_nl;;
  push_indent (sig_col + indent_size);;

  append "struct Program {";;
  append_nl;;
  append "__alloc: bumpalo::Bump,";;

  pop_indent;;
  append_nl;;
  append "}";;

  (* Next we print all the code as associated members. First
     we print a way to create such a program. *)
  append_nl;;
  append_nl;;
  append "impl<'a> Program {";;

  append_nl;;
  append "fn new() -> Self {";;

  push_indent (sig_col + indent_size);;
  append_nl;;
  append "Program {";;

  push_indent (sig_col + 2*indent_size);;
  append_nl;;
  append "__alloc: bumpalo::Bump::new(),";;

  pop_indent;;
  append_nl;;
  append "}";;

  pop_indent;;
  append_nl;;
  append "}";;

  append_nl;;
  append_nl;;
  monad_append_join append_nl (map append program_preamble);;

  (* Finally print all constants *)
  const_names <- print_decls_aux
                   (map (MRProd.on_snd Ex.ConstantDecl) constants)
                   (append_nl;; append_nl);;

  append_nl;;
  append "}";;

  pop_indent.
End FixEnv.

Definition extract_rust_within_rocq
           (overridden_masks : Kernames.kername -> option bitmask)
           (should_inline : Kernames.kername -> bool) : extract_template_env_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [template_inline should_inline];
     pcuic_args :=
       {| optimize_prop_discr := true;
          extract_transforms := [dearg_transform overridden_masks true false false false false;
                                 TopLevelFixes.transform] |} |}.
