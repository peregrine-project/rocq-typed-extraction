(** Syntactic facts about [native_rec_body]: the shapes it rewrites to a direct
    recursive call, and the side conditions under which it leaves a term alone.
    The printer does not prove the rewrite correct; these only fix its output. *)
From Stdlib Require Import List Arith Lia.
From MetaRocq.Utils Require Import bytestring MRList.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EAst EAstUtils ELiftSubst.
From MetaRocq.Erasure.Typed Require ExAst.
From TypedExtraction.Rust Require Import RustExtract.

Import ListNotations.
Local Open Scope bs_scope.

Section Shapes.
Context (doms : list ExAst.box_type).

Lemma native_rec_body_bare (kn : kername) (d : def term) :
  native_rec_body doms kn (tFix [d] 0) = subst [tConst kn] 0 (dbody d).
Proof.
  unfold native_rec_body. cbn -[subst closedn].
  destruct (closedn 1 (dbody d)); reflexivity.
Qed.

(** ** The eta-expanded case ([k > 0] outer lambdas)

    The shape erasure actually produces for a structurally recursive
    definition is eta-expanded: [λx1..λxk. (fix f := ..) x1 .. xk]. We build
    that shape with [mk_eta_lambdas] (nested [tLambda]s, outermost first) and
    show [rev_map tRel (seq 0 k)] (the canonical "applied to all outer
    variables, in order" argument list) is recognized as an eta match by
    [nrb_is_eta_args], then that [native_rec_body] on the whole eta-wrapped
    term produces the same [subst [tConst kn] 0 (dbody d)] as the bare case
    -- i.e. [native_rec_body_bare] is the [k = 0] instance of this lemma. *)

Fixpoint mk_eta_lambdas (names : list name) (core : term) : term :=
  match names with
  | [] => core
  | na :: names' => tLambda na (mk_eta_lambdas names' core)
  end.

Lemma rev_map_tRel_seq_S (k : nat) :
  rev_map tRel (seq 0 (S k)) = tRel k :: rev_map tRel (seq 0 k).
Proof.
  rewrite seq_S, rev_map_app.
  change [k] with ([] ++ [k])%list.
  rewrite rev_map_cons. cbn.
  reflexivity.
Qed.

(** [rev_map tRel (seq 0 k)] -- the fully eta-expanded self-application's
    argument list -- is always recognized by [nrb_is_eta_args]. *)
Lemma nrb_is_eta_args_seq (doms' : list ExAst.box_type) (k : nat) :
  nrb_is_eta_args doms' k (rev_map tRel (seq 0 k)) = true.
Proof.
  induction k as [| k IH] in doms' |- *.
  - reflexivity.
  - rewrite rev_map_tRel_seq_S. cbn [nrb_is_eta_args].
    rewrite Nat.eqb_refl. cbn. apply IH.
Qed.

(** [strip]'s accumulator invariant, proved separately since [strip] is a
    local [let fix] inside [native_rec_body] (not itself top-level nameable):
    peeling the [k] lambdas built by [mk_eta_lambdas names core] pushes
    [names] onto the accumulator in reverse, and leaves [core] untouched --
    *for any* starting accumulator [acc], hence in particular for [acc = []]
    as used by [native_rec_body]. [core] itself is never [tLambda]-headed in
    our use (it is always an application spine headed by [tFix] or [tConst]),
    so the induction does not need to assume anything about it. *)
(** [mkApps (tFix [d] 0) args] is never [tLambda]-headed (an application
    spine over a fixpoint always ends in [tApp] once it has any arguments,
    and in [tFix] itself when it has none), so [strip] stops immediately on
    it regardless of the starting accumulator. *)
Lemma strip_mkApps_tFix (d : def term) (args : list term) (acc : list name) :
  (fix strip (acc0 : list name) (b : term) {struct b} : list name * term :=
     match b with
     | tLambda na b' => strip (na :: acc0) b'
     | _ => (acc0, b)
     end) acc (mkApps (tFix [d] 0) args) = (acc, mkApps (tFix [d] 0) args).
Proof.
  destruct args as [| a args' _] using rev_ind.
  - reflexivity.
  - rewrite mkApps_app. reflexivity.
Qed.

(* [strip]'s accumulator invariant is stated with [fold_left], matching
   [strip]'s own left-to-right accumulation exactly, so the induction step is
   literally the defining equation of [fold_left] on both sides -- no lemma
   about [rev]/[app] needed. *)
Lemma native_rec_body_strip_eta (kn : kername) (names : list name) (d : def term) (args : list term) (acc : list name) :
  (fix strip (acc0 : list name) (b : term) {struct b} : list name * term :=
     match b with
     | tLambda na b' => strip (na :: acc0) b'
     | _ => (acc0, b)
     end) acc (mk_eta_lambdas names (mkApps (tFix [d] 0) args))
  = (fold_left (fun acc0 na => na :: acc0) names acc, mkApps (tFix [d] 0) args).
Proof.
  revert acc.
  induction names as [| na names' IH]; intros acc; cbn.
  - apply strip_mkApps_tFix.
  - apply IH.
Qed.

Lemma fold_left_cons_length (names : list name) (acc : list name) :
  length (fold_left (fun acc0 (na : name) => na :: acc0) names acc)
  = length names + length acc.
Proof.
  revert acc.
  induction names as [| na names' IH]; intros acc; cbn.
  - reflexivity.
  - rewrite IH. cbn. lia.
Qed.

(** The general eta case: [native_rec_body] on the [k]-lambda eta wrapper of
    the fixpoint's canonical self-application computes the *same*
    [subst [tConst kn] 0 (dbody d)] as the bare case ([k = 0]). *)
Lemma native_rec_body_eta (kn : kername) (d : def term) (names : list name) :
  closedn 1 (dbody d) = true ->
  native_rec_body doms kn
    (mk_eta_lambdas names (mkApps (tFix [d] 0) (rev_map tRel (seq 0 (length names)))))
  = subst [tConst kn] 0 (dbody d).
Proof.
  intros Hclosed.
  unfold native_rec_body.
  rewrite (native_rec_body_strip_eta kn names d (rev_map tRel (seq 0 (length names))) []).
  rewrite (fold_left_cons_length names []), Nat.add_0_r.
  rewrite (decompose_app_mkApps (tFix [d] 0) (rev_map tRel (seq 0 (length names))) eq_refl).
  rewrite nrb_is_eta_args_seq, Hclosed.
  reflexivity.
Qed.

End Shapes.

(** ** The side conditions of the eta case

    An eta-wrapped fixpoint whose body captures an outer variable, or that
    fills a slot of a non-erased type with a box, is left unchanged, and the
    printer falls back to its closure-cell case. *)

Definition nrb_eta_kn : kername := (MPfile ["Test"], "g").
Definition nrb_eta_fix (b : term) : term :=
  tFix [{| dname := nAnon; dbody := b; rarg := 0 |}] 0.

(** [g x y := (fix f a b := x) x y] captures [x]. *)
Definition nrb_capture : term :=
  tLambda nAnon (tLambda nAnon
    (mkApps (nrb_eta_fix (tLambda nAnon (tLambda nAnon (tRel 4)))) [tRel 1; tRel 0])).

Example native_rec_body_capture_unchanged :
  native_rec_body [] nrb_eta_kn nrb_capture = nrb_capture.
Proof. reflexivity. Qed.

(** [g x y := (fix f p b := f p b) box y]: the box fills the slot of [x]. *)
Definition nrb_wildcard : term :=
  tLambda nAnon (tLambda nAnon
    (mkApps (nrb_eta_fix (tLambda nAnon (tLambda nAnon (mkApps (tRel 2) [tBox; tRel 0]))))
            [tBox; tRel 0])).

Example native_rec_body_wildcard_value_slot_unchanged :
  native_rec_body [ExAst.TAny; ExAst.TAny] nrb_eta_kn nrb_wildcard = nrb_wildcard.
Proof. reflexivity. Qed.

Example native_rec_body_wildcard_erased_slot :
  native_rec_body [ExAst.TBox; ExAst.TAny] nrb_eta_kn nrb_wildcard
  = tLambda nAnon (tLambda nAnon (mkApps (tConst nrb_eta_kn) [tBox; tRel 0])).
Proof. reflexivity. Qed.
