(** * Field-level dead-code elimination (prototype, not verified)

    Typed erasure removes constructor arguments only when they are
    logical (types and proofs).  Records of operations, such as the
    structure instances of mathcomp, then keep every operation once one of
    them is used.  This pass

    1. collects the constructor fields that are used: projected with
       [tProj], or bound in a [match] branch whose body refers to them;
    2. removes every other field of every inductive that is not remapped,
       from the inductive's declaration, from constructor applications, from
       [match] branches and from projections, reusing the dearging of
       [MetaRocq.Erasure.Typed.Optimize];
    3. removes the constants that are no longer reachable from the entry
       point.

    Dropping an unused field also drops the evaluation of its value.  In a
    total, pure program this changes nothing observable; it is not proved
    here, which is why the pass is a separate, optional step. *)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Erasure Require Import EAst.
From MetaRocq.Erasure.Typed Require Import ExAst Optimize.
From Stdlib Require Import List.

Import ListNotations.

(** Does de Bruijn index [k] occur free in [t]? Primitive values are
    treated conservatively. *)
Fixpoint occurs (k : nat) (t : term) : bool :=
  match t with
  | tRel i => Nat.eqb i k
  | tEvar _ l => existsb (occurs k) l
  | tLambda _ b => occurs (S k) b
  | tLetIn _ b u => occurs k b || occurs (S k) u
  | tApp f a => occurs k f || occurs k a
  | tConstruct _ _ l => existsb (occurs k) l
  | tCase _ d brs =>
    occurs k d || existsb (fun br => occurs (#|fst br| + k) (snd br)) brs
  | tProj _ u => occurs k u
  | tFix defs _ | tCoFix defs _ =>
    existsb (fun d => occurs (#|defs| + k) (dbody d)) defs
  | tLazy u | tForce u => occurs k u
  | tPrim _ => true
  | _ => false
  end.

(** A used field: inductive, constructor index, field index (counted from
    the first non-parameter argument). *)
Definition field := (inductive * nat * nat)%type.

Definition field_eqb (f g : field) : bool :=
  let '(i, c, j) := f in
  let '(i', c', j') := g in
  eqb i i' && Nat.eqb c c' && Nat.eqb j j'.

Fixpoint used_fields (t : term) : list field :=
  match t with
  | tEvar _ l => concat (map used_fields l)
  | tLambda _ b => used_fields b
  | tLetIn _ b u => used_fields b ++ used_fields u
  | tApp f a => used_fields f ++ used_fields a
  | tConstruct _ _ l => concat (map used_fields l)
  | tCase (ind, _) d brs =>
    let in_branch c br :=
        let n := #|fst br| in
        filter (fun f => let '(_, _, j) := f in occurs (n - S j) (snd br))
               (map (fun j => (ind, c, j)) (seq 0 n)) in
    used_fields d
      ++ concat (mapi in_branch brs)
      ++ concat (map (fun br => used_fields (snd br)) brs)
  | tProj (Kernames.mkProjection ind _ arg) u => (ind, 0, arg) :: used_fields u
  | tFix defs _ | tCoFix defs _ => concat (map (fun d => used_fields (dbody d)) defs)
  | tLazy u | tForce u => used_fields u
  | _ => []
  end.

Definition env_used_fields (Σ : global_env) : list field :=
  concat (map (fun '(_, _, decl) =>
                 match decl with
                 | ConstantDecl {| cst_body := Some body |} => used_fields body
                 | _ => []
                 end) Σ).

(** Masks that remove every unused field of every non-remapped inductive. *)
Definition field_masks (keep_ind : kername -> bool) (used : list field)
           (Σ : global_env) : list (kername * mib_masks) :=
  flat_map
    (fun '(kn, _, decl) =>
       match decl with
       | InductiveDecl mib =>
         if keep_ind kn then [] else
         let ctor_masks :=
             concat
               (mapi (fun i oib =>
                        mapi (fun c '(_, args, _) =>
                                let nfields := #|args| - ind_npars mib in
                                (i, c, map (fun j => negb (existsb (field_eqb (mkInd kn i, c, j)) used))
                                           (seq 0 nfields)))
                             (ind_ctors oib))
                     (ind_bodies mib)) in
         [(kn, {| param_mask := []; ctor_masks := ctor_masks |})]
       | _ => []
       end) Σ.

(** Constants referenced by a term. *)
Fixpoint consts_of (t : term) : list kername :=
  match t with
  | tConst kn => [kn]
  | tEvar _ l | tConstruct _ _ l => concat (map consts_of l)
  | tLambda _ b => consts_of b
  | tLetIn _ b u | tApp b u => consts_of b ++ consts_of u
  | tCase _ d brs => consts_of d ++ concat (map (fun br => consts_of (snd br)) brs)
  | tProj _ u | tLazy u | tForce u => consts_of u
  | tFix defs _ | tCoFix defs _ => concat (map (fun d => consts_of (dbody d)) defs)
  | _ => []
  end.

(** Keep the constants reachable from [roots]; keep every other kind of
    declaration.  [fuel] bounds the number of rounds (each round adds at
    least one constant or stops). *)
Fixpoint reachable (fuel : nat) (Σ : global_env) (seen : KernameSet.t)
         (todo : list kername) : KernameSet.t :=
  match fuel with
  | 0 => seen
  | S fuel =>
    match todo with
    | [] => seen
    | kn :: todo =>
      if KernameSet.mem kn seen then reachable fuel Σ seen todo else
      let seen := KernameSet.add kn seen in
      let next := match lookup_env Σ kn with
                  | Some (ConstantDecl {| cst_body := Some b |}) => consts_of b
                  | _ => []
                  end in
      reachable fuel Σ seen (next ++ todo)
    end
  end.

Definition prune (roots : list kername) (Σ : global_env) : global_env :=
  let live := reachable (S (#|Σ| * #|Σ|)) Σ KernameSet.empty roots in
  filter (fun '(kn, _, decl) =>
            match decl with
            | ConstantDecl _ => KernameSet.mem kn live
            | _ => true
            end) Σ.

(** The pass.  [keep_ind kn] holds for remapped inductives, whose
    representation is fixed by the remapping. *)
Definition field_dce (keep_ind : kername -> bool) (roots : list kername)
           (Σ : global_env) : global_env :=
  let masks := field_masks keep_ind (env_used_fields Σ) Σ in
  prune roots (dearg_env masks [] Σ).
