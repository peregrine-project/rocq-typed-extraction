(** Type parameters that no constructor field determines *)
From TypedExtraction.Plugin Require Import Loader.

(** A phantom type parameter *)
Inductive Proxy (A : Type) : Type := proxy : Proxy A.

Definition fromProxy {A} (p : Proxy A) : nat := match p with proxy _ => 1 end.

(** A type parameter that occurs only as a type parameter of the inductive itself *)
Inductive Tree (A : Type) : Type :=
| leaf : Tree A
| node : Tree A -> Tree A -> Tree A.

Fixpoint size {A} (t : Tree A) : nat :=
  match t with
  | leaf _ => 1
  | node _ l r => size l + size r
  end.

(** A type parameter that occurs in a field, applied to a phantom type *)
Inductive Wrap (A : Type) : Type := wrap : A -> Wrap A.

Definition unwrap {A} (w : Wrap A) : A := match w with wrap _ a => a end.

(** A type alias whose parameter occurs only as a phantom parameter *)
Definition ProxyAlias (A : Type) : Type := Proxy A.

Definition fromAlias (p : ProxyAlias bool) : nat := fromProxy p.

Definition test : nat :=
  fromProxy (proxy nat)
  + size (node bool (leaf bool) (leaf bool))
  + fromProxy (unwrap (wrap (Proxy nat) (proxy nat)))
  + fromAlias (proxy bool).

From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustUncheckedArith.

Redirect "rust/PhantomParams.rs" Rust Extract test.
