(** * Native recursion for single fixpoints, without [TopLevelFixes]

    The plugin runs [TopLevelFixes.transform] before printing, which already
    turns the bare fixpoint under lambdas into a direct recursive call. Here we
    extract without it (and without dearging), as Peregrine does, so the
    printer's [native_rec_body] sees each shape itself. The cargo project
    [extracted-code/rust/NativeRec-extracted] checks the values. *)
From MetaRocq.Erasure.Typed Require Import Extraction.
From TypedExtraction.Rust Require Import RustExtract Printing.
From TypedExtraction.Common Require Import PrettyPrinterMonad.
From MetaRocq.Template Require Import Ast Loader TemplateMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From Stdlib Require Import List.
Import ListNotations PrettyPrinterMonad MonadNotation.
Local Open Scope bs_scope.

(** A bare fixpoint under a lambda it uses. *)
Definition addk (k : nat) := fix f (n : nat) : nat := match n with 0 => k | S n' => S (f n') end.
(** The recursive function passed as a value. *)
Inductive rose := Node : nat -> list rose -> rose.
Fixpoint rsum (r : rose) : nat :=
  match r with Node n ts => fold_right Nat.add n (map rsum ts) end.
(** The recursive function partially applied. *)
Definition apply1 (g : nat -> nat) (x : nat) := g x.
Fixpoint pa (n m : nat) : nat := match n with 0 => m | S n' => S (apply1 (pa n') m) end.
(** Eta wrappers whose box fills an erased slot: a type, then a proof. *)
Definition len2 (A : Type) (l : list A) : nat :=
  (fix f (B : Type) (l : list B) := match l with nil => 0 | _ :: t => S (f B t) end) A l.
Definition gp (x : nat) (p : x = x) : nat :=
  (fix f (y : nat) (q : y = y) := match y with 0 => 0 | S y' => S (f y' eq_refl) end) x p.
(** A box filling a value slot: the closure cell stays. *)
Definition h2 (x y : nat) : nat :=
  (fix f (p : True) (z : nat) := match z with 0 => 0 | S z' => S (f I z') end) I y.
(** An eta wrapper whose fixpoint captures an outer variable: the closure cell stays. *)
Definition cap (x y : nat) : nat :=
  (fix f (a b : nat) := match a with 0 => x | S a' => S (f a' b) end) x y.
(** The fixpoint applied to the innermost lambdas only, then the same capturing [k]. *)
Definition sfx (A : Type) (k : nat) (l : list A) : nat :=
  (fix f (l : list A) := match l with nil => 0 | _ :: t => S (f t) end) l.
Definition sfxc (A : Type) (k : nat) (l : list A) : nat :=
  (fix f (l : list A) := match l with nil => k | _ :: t => S (f t) end) l.
(** Fewer leading lambdas than arrows in the type. *)
Fixpoint fewer (n : nat) : nat -> nat :=
  match n with 0 => fun m => m | S n' => fun m => S (fewer n' m) end.
(** A partial application at a use site, through the curried wrapper. *)
Definition use_curried := map (pa 2) [1; 2].

(** The expected values are in [NativeRec.main]. *)
Definition all : list nat :=
  [ addk 3 4; rsum (Node 1 [Node 2 []; Node 3 [Node 4 []]]); pa 3 4;
    len2 nat [1; 2; 3]; gp 5 eq_refl; h2 9 6; cap 2 1;
    sfx unit 7 [tt]; sfxc unit 7 [tt]; fewer 3 4;
    fold_right Nat.add 0 use_curried ].

Local Instance RustConfig : RustPrintConfig :=
  {| term_box_symbol := "()"; type_box_symbol := "()"; any_type_symbol := "()";
     print_full_names := false |}.

Local Instance preamble : Preamble :=
{| top_preamble := [
"#![allow(dead_code)]"; "#![allow(non_camel_case_types)]"; "#![allow(unused_imports)]";
"#![allow(non_snake_case)]"; "#![allow(unused_variables)]"; "";
"use std::marker::PhantomData;"; "";
"fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {"; "  f"; "}" ];
program_preamble := [
"fn alloc<T>(&'a self, t: T) -> &'a T {"; "  self.__alloc.alloc(t)"; "}"; "";
"fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
"  self.__alloc.alloc(F)"; "}" ] |}.

Definition params : extract_template_env_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [];
     pcuic_args := {| optimize_prop_discr := true; extract_transforms := [] |} |}.

Definition extract (p : program) : result string string :=
  entry <- match p.2 with T.tConst kn _ => ret kn | _ => Err "expected a constant" end;;
  Σ <- extract_template_env params p.1 (KernameSet.singleton entry) (fun _ => false);;
  '(_, s) <- finish_print_lines (print_program Σ no_remaps (fun _ => "#[derive(Debug, Clone)]"));;
  ret (String.concat MRString.nl s).

MetaRocq Quote Recursively Definition prog := all.
Definition out := Eval vm_compute in extract prog.

Redirect "rust/NativeRec.rs"
  MetaRocq Run (match out with Ok s => tmMsg s | Err e => tmFail e end)%monad.
