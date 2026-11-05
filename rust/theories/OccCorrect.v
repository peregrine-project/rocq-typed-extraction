(** Soundness of [RustExtract.occ], which decides in Rc mode whether a variable
    is moved instead of cloned, against a path-wise count of uses.

    [uses k t n] says that some evaluation path of [t] uses the variable [k] [n]
    times: a [match] takes its scrutinee and one branch, and building a closure
    or a local fixpoint counts once, whatever its body does with the variable.
    The count of a primitive value is left open, as [occ] gives it the top
    value 2.  The theorem [movable_at_most_once] is the property that the printer
    relies on: a variable found movable is used at most once on every path. *)

From Stdlib Require Import Lia List PeanoNat.
From MetaRocq.Utils Require Import MRList.
From MetaRocq.Common Require BasicAst.
From MetaRocq.Erasure Require Import EAst.
From TypedExtraction.Rust Require Import RustExtract.
Import ListNotations.

Inductive uses : nat -> term -> nat -> Prop :=
| uses_box k : uses k tBox 0
| uses_rel_eq k : uses k (tRel k) 1
| uses_rel_neq k n : n <> k -> uses k (tRel n) 0
| uses_var k i : uses k (tVar i) 0
| uses_const k c : uses k (tConst c) 0
| uses_evar k e l n : uses_all k l n -> uses k (tEvar e l) n
| uses_lambda k na b n : uses (S k) b n -> uses k (tLambda na b) (Nat.min 1 n)
| uses_letin k na v b m n :
    uses k v m -> uses (S k) b n -> uses k (tLetIn na v b) (m + n)
| uses_app k u v m n : uses k u m -> uses k v n -> uses k (tApp u v) (m + n)
| uses_construct k ind i args n :
    uses_all k args n -> uses k (tConstruct ind i args) n
| uses_case k ci d brs br m n :
    uses k d m -> In br brs -> uses (#|fst br| + k) (snd br) n ->
    uses k (tCase ci d brs) (m + n)
| uses_case_nil k ci d m : uses k d m -> uses k (tCase ci d []) m
| uses_proj k p c n : uses k c n -> uses k (tProj p c) n
| uses_fix k mfix idx n : uses_defs (#|mfix| + k) mfix n -> uses k (tFix mfix idx) n
| uses_cofix k mfix idx n : uses_defs (#|mfix| + k) mfix n -> uses k (tCoFix mfix idx) n
| uses_prim k p n : uses k (tPrim p) n
| uses_lazy k c n : uses k c n -> uses k (tLazy c) n
| uses_force k c n : uses k c n -> uses k (tForce c) n
with uses_all : nat -> list term -> nat -> Prop :=
| uses_all_nil k : uses_all k [] 0
| uses_all_cons k a l m n :
    uses k a m -> uses_all k l n -> uses_all k (a :: l) (m + n)
with uses_defs : nat -> mfixpoint term -> nat -> Prop :=
| uses_defs_nil k : uses_defs k [] 0
| uses_defs_cons k d ds m n :
    uses k (dbody d) m -> uses_defs k ds n ->
    uses_defs k (d :: ds) (Nat.min 1 m + n).

Scheme uses_ind' := Induction for uses Sort Prop
  with uses_all_ind' := Induction for uses_all Sort Prop
  with uses_defs_ind' := Induction for uses_defs Sort Prop.
Combined Scheme uses_mutind from uses_ind', uses_all_ind', uses_defs_ind'.

Lemma occ_branch_le k (br : list BasicAst.name * term) (brs : list (list BasicAst.name * term)) :
  In br brs ->
  occ (#|fst br| + k) (snd br)
    <= fold_right (fun br acc => Nat.max (occ (#|fst br| + k) (snd br)) acc) 0 brs.
Proof.
  induction brs as [|b brs IH]; cbn [In fold_right]; [contradiction|].
  intros [<-|H]; [lia|]. specialize (IH H). lia.
Qed.

Lemma occ_sound_mut :
  (forall k t n, uses k t n -> sat n <= occ k t) /\
  (forall k l n, uses_all k l n ->
     sat n <= sat (fold_right (fun a acc => occ k a + acc) 0 l)) /\
  (forall k ds n, uses_defs k ds n ->
     sat n <= sat (fold_right (fun d acc => Nat.min 1 (occ k (dbody d)) + acc) 0 ds)).
Proof.
  apply uses_mutind; intros; cbn [occ fold_right]; unfold sat in *; try lia.
  - rewrite Nat.eqb_refl. lia.
  - match goal with
    | H : In ?br ?brs |- _ => pose proof (occ_branch_le k br brs H)
    end.
    lia.
Qed.

Theorem occ_sound k t n : uses k t n -> sat n <= occ k t.
Proof. apply occ_sound_mut. Qed.

Theorem movable_at_most_once k t n : movable k t = true -> uses k t n -> n <= 1.
Proof.
  unfold movable. intros Hm Hu.
  apply Nat.leb_le in Hm.
  pose proof (occ_sound k t n Hu) as H.
  unfold sat in H. lia.
Qed.
