(** * Printer fixes of the Rust backend, run with cargo

    Primitive literals, type arguments that a constructor application does not
    determine (a nested constructor, a constructor without fields), and the cast
    of a match on a type-indexed family.  Extracted without [TopLevelFixes] and
    without dearging, as Peregrine does.  The cargo project
    [extracted-code/rust/PrintFixes-extracted] checks the values. *)
From MetaRocq.Erasure.Typed Require Import Extraction.
From TypedExtraction.Rust Require Import RustExtract Printing.
From TypedExtraction.Common Require Import PrettyPrinterMonad.
From MetaRocq.Template Require Import Ast Loader TemplateMonad.
From MetaRocq.Common Require Import Kernames.
From MetaRocq.Utils Require Import utils ResultMonad bytestring.
From Corelib Require Import PrimInt63 PrimString.
Import ListNotations PrettyPrinterMonad MonadNotation.

Inductive lit := I (i : PrimInt63.int) | Str (s : PrimString.string).
Definition pick (n : nat) : lit :=
  match n with 0 => I 9223372036854775807%uint63 | _ => Str "a""b\c {}~é"%pstring end.
Definition is_int (l : lit) : nat := match l with I _ => 1 | Str _ => 0 end.
Definition fromLeft {A B} (d : A) (e : A + B) : A := match e with inl a => a | inr _ => d end.
Definition fromLeft2 {A B C} (d : A) (e : (A + B) + C) : A := match e with inl (inl a) => a | _ => d end.
Definition isNone2 {A} (o : option (option A)) : nat := match o with Some None => 1 | _ => 0 end.
Inductive GE : Type -> Type := gn : nat -> GE nat | gb : unit -> GE unit.
Definition geval {A} (g : GE A) : A := match g with gn n => n | gb b => b end.
(** The expected values are in [PrintFixes.main].  The two literals only have to
    be accepted by rustc: [is_int] tells them apart. *)
Definition test : list nat :=
  [ is_int (pick 0); is_int (pick 1);
    fromLeft (B := unit) 0 (inl 5); fromLeft2 (B := unit) (C := unit) 0 (inl (inl 7));
    isNone2 (A := nat) (Some None);
    geval (gn 4) ].

Local Open Scope bs_scope.
Local Instance RustConfig : RustPrintConfig :=
  {| term_box_symbol := "()"; type_box_symbol := "()"; any_type_symbol := "()";
     print_full_names := false |}.

Local Instance preamble : Preamble :=
{| top_preamble := [
"#![allow(dead_code)]"; "#![allow(non_camel_case_types)]"; "#![allow(unused_imports)]";
"#![allow(non_snake_case)]"; "#![allow(unused_variables)]"; "";
"use std::marker::PhantomData;"; "";
"fn hint_app<TArg, TRet>(f: &dyn Fn(TArg) -> TRet) -> &dyn Fn(TArg) -> TRet {"; "  f"; "}";
"fn __cast<S, T>(x: S) -> T {"; "  let y = unsafe { std::mem::transmute_copy::<S, T>(&x) };"; "  std::mem::forget(x);"; "  y"; "}" ];
program_preamble := [
"fn alloc<T>(&'a self, t: T) -> &'a T {"; "  self.__alloc.alloc(t)"; "}"; "";
"fn closure<TArg, TRet>(&'a self, F: impl Fn(TArg) -> TRet + 'a) -> &'a dyn Fn(TArg) -> TRet {";
"  self.__alloc.alloc(F)"; "}" ] |}.

Definition params : extract_template_env_params :=
  {| check_wf_env_func := check_wf_env_func extract_within_coq;
     template_transforms := [];
     pcuic_args := {| optimize_prop_discr := true; extract_transforms := [] |} |}.

Definition extract (p : program) : result bytestring.string bytestring.string :=
  entry <- match p.2 with T.tConst kn _ => ret kn | _ => Err "expected a constant" end;;
  Σ <- extract_template_env params p.1 (KernameSet.singleton entry) (fun _ => false);;
  '(_, s) <- finish_print_lines (print_program Σ no_remaps (fun _ => "#[derive(Debug, Clone)]"));;
  ret (String.concat MRString.nl s).

MetaRocq Quote Recursively Definition prog := test.
Definition out := Eval vm_compute in extract prog.
Redirect "rust/PrintFixes.rs"
  MetaRocq Run (match out with Ok s => tmMsg s | Err e => tmFail e end)%monad.
