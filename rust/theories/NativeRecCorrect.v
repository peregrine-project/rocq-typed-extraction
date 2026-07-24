(* Correctness of [native_rec_body] (RustExtract.v), the rewrite that turns a
   single (non-mutual) fixpoint constant's self-reference into a direct call
   to the enclosing constant, so the Rust backend compiles recursion to a
   native recursive [fn] instead of a heap [Cell<Option<&dyn Fn>>].

   This file is a STANDALONE MetaRocq development: it does not hook into the
   Rust printer or the Transforms.v pipeline, it only states and proves
   properties of [native_rec_body] as a plain [EAst.term -> EAst.term] rewrite
   w.r.t. [EWcbvEval].

   Structure:
   - Section "Algebra" (fully Qed'd) pins down exactly what [native_rec_body]
     computes in the bare/eta cases and relates it, purely syntactically, to
     MetaRocq's own [cunfold_fix] unfolding of the corresponding [tFix].
   - Section "Semantics" connects that output to [eval]. It proves the single
     delta step and the per-redex agreement ([native_rec_body_bare_correct]),
     and then establishes that the naive whole-program observational
     equivalence -- syntactic equality of the resulting value in the two
     environments -- is FALSE ([native_rec_body_obs_equiv_disproof]): at the
     empty spine the original constant evaluates to [tFix [d] 0] while the
     rewritten one evaluates to the (lambda-headed) unfolded body, which are
     distinct values. The true, TCB-removing property therefore has to observe
     only first-order (closure-free) results, and is discussed there. A concrete
     two-constant environment ([native_rec_body_obs_equiv_disproof_premises],
     [native_rec_body_obs_equiv_fails_concretely]) witnesses that the refutation
     is non-vacuous: every premise but the refuted equivalence is satisfiable.
   - Section "Obstacles" shows the eta / [tBox]-wildcard statement fails for the
     same reason ([native_rec_body_eta_correct_disproof]), and records the
     residual first-order simulation obligation.
   - Section "First-order correctness" states the corrected property -- the
     [fo_value]-restricted observational equivalence the Rust backend relies on
     -- and reduces it ([native_rec_body_fo_obs_equiv_reduction],
     [native_rec_body_fo_obs_equiv]) to a single cross-environment applicative
     bisimulation ([Hcore]), the sole remaining ingredient.
*)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import bytestring MRList.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EAst EAstUtils ELiftSubst ECSubst EGlobalEnv EWcbvEval.
From TypedExtraction.Rust Require Import RustExtract.
From Equations Require Import Equations.

Import ListNotations.
Open Scope bs_scope.

Set Default Proof Using "Type".

(** * Section "Algebra": what [native_rec_body] computes, purely syntactically.

    This section is fully [Qed]'d. It does not touch [eval] at all: it just
    pins down the exact output of [native_rec_body] in the two shapes that
    matter (bare fixpoint, and fully eta-expanded fixpoint), and relates that
    output to MetaRocq's own [cunfold_fix] unfolding of the corresponding
    [tFix] -- i.e. it shows [native_rec_body]'s rewrite is *exactly* "the
    same one-step unfolding [cunfold_fix] already performs, with [tConst kn]
    written in place of the reconstructed [tFix [d] 0]". *)

(** [fix_subst] of a singleton, non-mutual fixpoint list is just the
    singleton list containing the fixpoint itself: MetaRocq's fixpoint
    unfolding re-injects [tFix [d] 0] for every recursive occurrence. *)
Lemma fix_subst_singleton (d : def term) : fix_subst [d] = [tFix [d] 0].
Proof. reflexivity. Qed.

(** MetaRocq's own unfolding of a closed, singleton, non-mutual fixpoint:
    [cunfold_fix [d] 0] substitutes [tFix [d] 0] for the self-reference in
    [dbody d]. This is the standard fact ([closed_fix_substl_subst_eq]) that
    [substl] (used internally by [cunfold_fix]) agrees with plain [subst] on
    closed substituends -- specialized to the singleton case. *)
Lemma cunfold_fix_singleton (d : def term) :
  is_true (closed (tFix [d] 0)) ->
  cunfold_fix [d] 0 = Some (rarg d, subst [tFix [d] 0] 0 (dbody d)).
Proof.
  intros Hcl.
  unfold cunfold_fix. cbn [nth_error].
  rewrite <- fix_subst_singleton.
  rewrite <- (closed_fix_substl_subst_eq Hcl eq_refl).
  rewrite fix_subst_singleton.
  reflexivity.
Qed.

(** The core fact the task asked to prioritize: on a *bare* singleton
    fixpoint (no eta wrapper, [k = 0] outer lambdas), [native_rec_body]
    computes *exactly* [cunfold_fix]'s unfolded body ([cunfold_fix_singleton]
    above), with [tConst kn] written in place of the reconstructed
    [tFix [d] 0]. This is a direct computation ([native_rec_body] is a plain
    [Definition], so it reduces on concrete syntactic input). *)
Lemma native_rec_body_bare (kn : kername) (d : def term) :
  native_rec_body kn (tFix [d] 0) = subst [tConst kn] 0 (dbody d).
Proof. reflexivity. Qed.

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
Lemma nrb_is_eta_args_seq (k : nat) :
  nrb_is_eta_args k (rev_map tRel (seq 0 k)) = true.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - rewrite rev_map_tRel_seq_S.
    change (nrb_is_eta_args (S k) (tRel k :: rev_map tRel (seq 0 k)) = true).
    unfold nrb_is_eta_args in *.
    cbn [Nat.eqb].
    rewrite Nat.eqb_refl. cbn.
    exact IH.
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
  native_rec_body kn
    (mk_eta_lambdas names (mkApps (tFix [d] 0) (rev_map tRel (seq 0 (length names)))))
  = subst [tConst kn] 0 (dbody d).
Proof.
  unfold native_rec_body.
  rewrite (native_rec_body_strip_eta kn names d (rev_map tRel (seq 0 (length names))) []).
  rewrite (fold_left_cons_length names []), Nat.add_0_r.
  rewrite (decompose_app_mkApps (tFix [d] 0) (rev_map tRel (seq 0 (length names))) eq_refl).
  rewrite nrb_is_eta_args_seq.
  reflexivity.
Qed.

(** * Section "Semantics": [native_rec_body] under [EWcbvEval].

    The Algebra section fixed [native_rec_body]'s *output* syntactically. Here
    we connect that output to evaluation. The only evaluation ingredient the
    rewrite actually relies on is a single delta (constant-unfolding) step:
    the recursive constant [kn] is bound, in the global environment, to the
    fixpoint itself, so [tConst kn] evaluates to [tFix [d] 0]. Everything is
    stated for an arbitrary [WcbvFlags] [wfl]; nothing below depends on
    [with_guarded_fix] / [with_prop_case] / [with_constructor_as_block], so the
    lemmas hold for both [EWcbvEval.default_wcbv_flags] and the pipeline's
    [final_wcbv_flags]. *)

(** The single delta step. A [tFix] is an [atom] (a value) for every flag set,
    so [eval_atom] evaluates it to itself, and [eval_delta] unfolds the
    constant to it. *)
Lemma const_unfolds_to_fix {wfl : EWcbvEval.WcbvFlags}
      (Sigma : global_declarations) (kn : kername)
      (decl : constant_body) (d : def term) :
  declared_constant Sigma kn decl ->
  cst_body decl = Some (tFix [d] 0) ->
  eval Sigma (tConst kn) (tFix [d] 0).
Proof.
  intros Hdecl Hbody.
  eapply eval_delta.
  - exact Hdecl.
  - exact Hbody.
  - apply eval_atom. reflexivity.
Qed.

(** The tractable core of the observational-equivalence theorem, restricted to
    the BARE case ([k = 0], [body = tFix [d] 0]).

    It exhibits, side by side, exactly the three facts the full theorem needs
    and nothing more:
    - [cunfold_fix]'s unfolded body is [subst [tFix [d] 0] 0 (dbody d)]
      (from [cunfold_fix_singleton]);
    - [native_rec_body]'s output is [subst [tConst kn] 0 (dbody d)]
      (from [native_rec_body_bare]);
    - [tConst kn] delta-steps to [tFix [d] 0] (from [const_unfolds_to_fix]).

    So the two substituted bodies are *the same term up to [tConst kn] in place
    of [tFix [d] 0] in slot 0*, and [tConst kn] evaluates to precisely that
    [tFix [d] 0]. This is "the two substitutions agree modulo a single delta
    step" made precise.

    THE REMAINING OBSTACLE (why the naive general statement below is refuted,
    and the corrected first-order one reduced rather than closed).
    Turning this per-redex agreement into a whole-program observational
    equivalence requires a *congruence-under-substitution / simulation* fact:
    if [eval Σ (tConst kn) (tFix [d] 0)] then, for every context [b],
    [subst [tConst kn] 0 b] and [subst [tFix [d] 0] 0 b] evaluate to the same
    value. In the rewritten program [tConst kn] is itself bound to
    [native_rec_body]'s output (which again contains [tConst kn]), so the
    obligation is genuinely recursive: it is a step-indexed / coinductive
    simulation over [eval] derivations, not a structural induction on terms.
    MetaRocq's Erasure library provides the per-step lemmas ([eval_delta],
    [cunfold_fix], determinism [EWcbvEval.eval_deterministic]) but no such
    substitution-congruence for [eval], so it must be built from scratch;
    that is the missing ingredient. *)
Lemma native_rec_body_bare_correct {wfl : EWcbvEval.WcbvFlags}
      (Sigma : global_declarations) (kn : kername)
      (decl : constant_body) (d : def term) :
  declared_constant Sigma kn decl ->
  cst_body decl = Some (tFix [d] 0) ->
  is_true (closed (tFix [d] 0)) ->
  (cunfold_fix [d] 0 = Some (rarg d, subst [tFix [d] 0] 0 (dbody d))) *
  (native_rec_body kn (tFix [d] 0) = subst [tConst kn] 0 (dbody d)) *
  (eval Sigma (tConst kn) (tFix [d] 0)).
Proof.
  intros Hdecl Hbody Hcl.
  split; [ split |].
  - apply cunfold_fix_singleton. exact Hcl.
  - apply native_rec_body_bare.
  - eapply const_unfolds_to_fix; eassumption.
Qed.

(** Inversion for evaluation of a constant: the only two [eval] rules with a
    [tConst] head are [eval_delta] and [eval_atom], and [tConst] is not an
    [atom], so any evaluation of [tConst c] proceeds by [eval_delta]. *)
Lemma eval_tConst_inv {wfl : EWcbvEval.WcbvFlags}
      (Sigma : global_declarations) (c : kername) (v : term) :
  eval Sigma (tConst c) v ->
  { decl : constant_body & { body : term &
    ((declared_constant Sigma c decl) * (cst_body decl = Some body) * eval Sigma body v)%type } }.
Proof.
  intros H. depelim H.
  - do 2 eexists; repeat split; eassumption.
  - cbn in i; discriminate.
Qed.

(** The naive whole-program observational equivalence -- syntactic equality of
    the evaluated value across the two environments -- is FALSE, and the failure
    is already visible at the empty argument spine ([args = []]).

    Under [Sigma] the constant delta-unfolds to [tFix [d] 0], which is an [atom],
    so [tConst kn] evaluates to [tFix [d] 0]. Under [Sigma'] it delta-unfolds to
    [native_rec_body]'s output [subst [tConst kn] 0 (dbody d)]; since every
    genuine (erased) fixpoint has a [tLambda] body, that output is
    [tLambda]-headed, so [tConst kn] evaluates to a lambda -- a value distinct
    from [tFix [d] 0]. The two constants therefore do not share their value.

    This is not a proof gap a simulation lemma could fill: the two values
    genuinely differ. A [tFix] and a constant bound to that fixpoint's unfolding
    are only *behaviourally* equivalent, never *syntactically equal as values*
    at partial applications. Any correct, TCB-removing statement must restrict
    the observed value [v] to a first-order (closure-free) normal form -- a
    constructor tree over [tBox], in which no [tFix]/[tLambda]/[tConst] occurs --
    or phrase the conclusion as an applicative bisimulation rather than value
    equality.

    Within a single environment the [tConst kn] / [tFix [d] 0] head interchange
    is free: [WcbvEvalAux.eval_mkApps_heads] swaps two heads that evaluate to a
    common value. So the residual content of the first-order statement is purely
    the CROSS-environment simulation between the guarded [tFix] recursion of
    [Sigma] and the recursion-through-[tConst kn] of [Sigma']. *)
Lemma native_rec_body_bare_obs_fails {wfl : EWcbvEval.WcbvFlags}
      (Sigma Sigma' : global_declarations) (kn : kername)
      (decl decl' : constant_body) (d : def term) (na : name) (b : term) :
  declared_constant Sigma kn decl ->
  cst_body decl = Some (tFix [d] 0) ->
  declared_constant Sigma' kn decl' ->
  cst_body decl' = Some (native_rec_body kn (tFix [d] 0)) ->
  dbody d = tLambda na b ->
  (eval Sigma (tConst kn) (tFix [d] 0) *
   (eval Sigma' (tConst kn) (tFix [d] 0) -> False))%type.
Proof.
  intros Hdecl Hbody Hdecl' Hbody' Hlam.
  split.
  - eapply const_unfolds_to_fix; eassumption.
  - intros H. apply eval_tConst_inv in H as [decl0 [body0 [[Hd0 Hb0] Hev]]].
    unfold declared_constant in Hdecl', Hd0.
    rewrite Hdecl' in Hd0. inversion Hd0; subst.
    rewrite Hbody' in Hb0. inversion Hb0; subst.
    rewrite native_rec_body_bare in Hev.
    rewrite Hlam in Hev. cbn in Hev.
    apply WcbvEvalAux.eval_tLambda_inv in Hev.
    discriminate.
Qed.

(** Consequently the general observational-equivalence statement is not a
    theorem: assuming its exact conclusion (for all argument spines and values,
    both directions) yields a contradiction, under the mild and always-satisfied
    side condition that [d]'s body is a [tLambda]. Every premise is jointly
    satisfiable (a two-constant environment binding [kn] as required, agreeing
    everywhere else, witnesses them), so this is a genuine refutation, not a
    vacuous one. It instantiates at [args = []], [v = tFix [d] 0]. *)
Theorem native_rec_body_obs_equiv_disproof {wfl : EWcbvEval.WcbvFlags}
      (Sigma Sigma' : global_declarations) (kn : kername)
      (decl decl' : constant_body) (d : def term) (na : name) (b : term) :
  declared_constant Sigma kn decl ->
  cst_body decl = Some (tFix [d] 0) ->
  declared_constant Sigma' kn decl' ->
  cst_body decl' = Some (native_rec_body kn (tFix [d] 0)) ->
  (forall kn', kn' <> kn -> lookup_env Sigma kn' = lookup_env Sigma' kn') ->
  is_true (closed (tFix [d] 0)) ->
  dbody d = tLambda na b ->
  (forall (args : list term) (v : term),
    (eval Sigma  (mkApps (tConst kn) args) v -> eval Sigma' (mkApps (tConst kn) args) v) *
    (eval Sigma' (mkApps (tConst kn) args) v -> eval Sigma  (mkApps (tConst kn) args) v)) ->
  False.
Proof.
  intros Hdecl Hbody Hdecl' Hbody' Hagree Hcl Hlam Hobs.
  destruct (native_rec_body_bare_obs_fails Sigma Sigma' kn decl decl' d na b
              Hdecl Hbody Hdecl' Hbody' Hlam) as [Hev Hne].
  specialize (Hobs [] (tFix [d] 0)) as [Hfwd _].
  cbn in Hfwd. apply Hne, Hfwd, Hev.
Qed.

(** ** Non-vacuity witness for the refutation.

    A concrete two-constant environment satisfying every hypothesis of
    [native_rec_body_obs_equiv_disproof] except the (refuted) observational
    equivalence itself. This exhibits that the refutation is not vacuous: there
    is a real global environment on which the naive statement provably fails.

    The witness is minimal: a single fixpoint [nrb_d] whose body is a lambda
    (the always-present shape for arity >= 1), bound under one kername [nrb_kn]
    to [tFix [nrb_d] 0] in [nrb_Sigma] and to [native_rec_body]'s rewritten
    output in [nrb_Sigma']. Each environment is the single binding of [nrb_kn],
    so they agree off [nrb_kn] trivially (both return [None] there). *)

Definition nrb_kn : kername := (MPfile ["Test"], "f").
Definition nrb_d : def term :=
  @E.Build_def term nAnon (tLambda nAnon tBox) 0.
Definition nrb_decl : constant_body := {| cst_body := Some (tFix [nrb_d] 0) |}.
Definition nrb_decl' : constant_body :=
  {| cst_body := Some (native_rec_body nrb_kn (tFix [nrb_d] 0)) |}.
Definition nrb_Sigma : global_declarations := [(nrb_kn, ConstantDecl nrb_decl)].
Definition nrb_Sigma' : global_declarations := [(nrb_kn, ConstantDecl nrb_decl')].

(** The two witness environments agree away from [nrb_kn]: each has [nrb_kn] as
    its only binding, so both look up to [None] on any other kername. *)
Lemma nrb_agree (kn' : kername) :
  kn' <> nrb_kn -> lookup_env nrb_Sigma kn' = lookup_env nrb_Sigma' kn'.
Proof.
  intros Hne. unfold nrb_Sigma, nrb_Sigma', lookup_env. cbn.
  destruct (ReflectEq.eqb kn' nrb_kn) eqn:Heq.
  - apply ReflectEq.eqb_eq in Heq. subst. contradiction.
  - reflexivity.
Qed.

(** Every setup hypothesis of [native_rec_body_obs_equiv_disproof] holds of the
    concrete witness (with [na = nAnon], [b = tBox]), so the refutation's
    premises are jointly satisfiable. *)
Example native_rec_body_obs_equiv_disproof_premises :
  (declared_constant nrb_Sigma nrb_kn nrb_decl) *
  (cst_body nrb_decl = Some (tFix [nrb_d] 0)) *
  (declared_constant nrb_Sigma' nrb_kn nrb_decl') *
  (cst_body nrb_decl' = Some (native_rec_body nrb_kn (tFix [nrb_d] 0))) *
  (forall kn', kn' <> nrb_kn -> lookup_env nrb_Sigma kn' = lookup_env nrb_Sigma' kn') *
  (is_true (closed (tFix [nrb_d] 0))) *
  (dbody nrb_d = tLambda nAnon tBox).
Proof.
  refine (_, _, _, _, nrb_agree, _, _); reflexivity.
Qed.

(** Feeding the witness to [native_rec_body_obs_equiv_disproof] discharges every
    setup premise and leaves exactly the naive observational-equivalence
    hypothesis, which is thereby shown false on a concrete environment: this is
    the refutation, non-vacuously instantiated. *)
Example native_rec_body_obs_equiv_fails_concretely {wfl : EWcbvEval.WcbvFlags} :
  (forall (args : list term) (v : term),
    (eval nrb_Sigma  (mkApps (tConst nrb_kn) args) v -> eval nrb_Sigma' (mkApps (tConst nrb_kn) args) v) *
    (eval nrb_Sigma' (mkApps (tConst nrb_kn) args) v -> eval nrb_Sigma  (mkApps (tConst nrb_kn) args) v)) ->
  False.
Proof.
  apply (native_rec_body_obs_equiv_disproof (wfl:=wfl)
           nrb_Sigma nrb_Sigma' nrb_kn nrb_decl nrb_decl' nrb_d nAnon tBox);
    try reflexivity.
  exact nrb_agree.
Qed.

(** * Section "Obstacles": the eta / [tBox]-wildcard case.

    The general eta case with a *canonical* argument list ([rev_map tRel ...])
    is fully handled by [native_rec_body_eta] (Algebra). What is left is the
    case [nrb_is_eta_args] also accepts a [tBox] in an argument slot (the erased
    type/proof argument of a polymorphic recursor). We split it into its
    algebraic part (provable) and its semantic part (the genuine obstacle). *)

(** Algebraic part (proved). [native_rec_body]'s *output* on an eta wrapper is
    [subst [tConst kn] 0 (dbody d)] for ANY argument list [args] that
    [nrb_is_eta_args] accepts -- including lists with [tBox] slots -- not just
    the canonical [rev_map tRel (seq 0 k)] of [native_rec_body_eta]. The proof
    is the same [strip]/[decompose_app] computation; it never inspects the
    contents of [args] beyond the [nrb_is_eta_args] test. This generalizes
    [native_rec_body_eta] (which is the [args = rev_map tRel (seq 0 (length
    names))] instance, via [nrb_is_eta_args_seq]). *)
Lemma native_rec_body_eta_gen (kn : kername) (d : def term)
      (names : list name) (args : list term) :
  nrb_is_eta_args (length names) args = true ->
  native_rec_body kn (mk_eta_lambdas names (mkApps (tFix [d] 0) args))
  = subst [tConst kn] 0 (dbody d).
Proof.
  intros Hargs.
  unfold native_rec_body.
  rewrite (native_rec_body_strip_eta kn names d args []).
  rewrite (fold_left_cons_length names []), Nat.add_0_r.
  rewrite (decompose_app_mkApps (tFix [d] 0) args eq_refl).
  rewrite Hargs.
  reflexivity.
Qed.

(** Semantic part -- the eta statement fails for the same reason as the bare
    one, and this is already witnessed by its own [names = []], [args = []]
    instance, where the eta wrapper degenerates to the bare fixpoint
    ([mk_eta_lambdas [] (mkApps (tFix [d] 0) []) = tFix [d] 0]) and the two
    constants evaluate, at the empty spine, to [tFix [d] 0] and to
    [native_rec_body]'s lambda-headed output respectively.

    A note on the [tBox] wildcard, orthogonal to this refutation.
    [native_rec_body_eta_gen] shows the rewrite produces the SAME body
    [subst [tConst kn] 0 (dbody d)] whether an eta slot holds the proper outer
    variable [tRel j] or a [tBox]; accepting a [tBox] there drops that slot,
    which is observationally sound only if the slot is semantically irrelevant
    (an erased type/proof binder). That erasability side condition IS statable
    at this plain [EAst.term] layer: MetaRocq's eta-expansion invariant is the
    boolean [EEtaExpanded.isEtaExp : global_context -> term -> bool] (with
    [isEtaExp_constant_decl] for constant bodies), which takes an [EAst.term]
    directly -- no typed-erasure layer is needed to phrase it. It is moot for
    the statement below, though: the conclusion already fails on the bare
    instance, so no [isEtaExp]-style precondition on the boxed slots can rescue
    it as written. A corrected first-order statement inherits exactly the
    cross-environment simulation obligation recorded for the bare case, and, for
    the [tBox] slots, an [isEtaExp]-style hypothesis on [kn]'s body. *)
Theorem native_rec_body_eta_correct_disproof {wfl : EWcbvEval.WcbvFlags}
      (Sigma Sigma' : global_declarations) (kn : kername)
      (decl decl' : constant_body) (d : def term) (na : name) (b : term) :
  declared_constant Sigma kn decl ->
  cst_body decl = Some (mk_eta_lambdas [] (mkApps (tFix [d] 0) [])) ->
  declared_constant Sigma' kn decl' ->
  cst_body decl' = Some (native_rec_body kn (mk_eta_lambdas [] (mkApps (tFix [d] 0) []))) ->
  (forall kn', kn' <> kn -> lookup_env Sigma kn' = lookup_env Sigma' kn') ->
  nrb_is_eta_args (length (@nil name)) [] = true ->
  dbody d = tLambda na b ->
  (forall (cargs : list term) (v : term),
    (eval Sigma  (mkApps (tConst kn) cargs) v -> eval Sigma' (mkApps (tConst kn) cargs) v) *
    (eval Sigma' (mkApps (tConst kn) cargs) v -> eval Sigma  (mkApps (tConst kn) cargs) v)) ->
  False.
Proof.
  intros Hdecl Hbody Hdecl' Hbody' Hagree Heta Hlam Hobs.
  change (mk_eta_lambdas [] (mkApps (tFix [d] 0) [])) with (tFix [d] 0) in Hbody, Hbody'.
  destruct (native_rec_body_bare_obs_fails Sigma Sigma' kn decl decl' d na b
              Hdecl Hbody Hdecl' Hbody' Hlam) as [Hev Hne].
  specialize (Hobs [] (tFix [d] 0)) as [Hfwd _].
  cbn in Hfwd. apply Hne, Hfwd, Hev.
Qed.

(** * Section "First-order correctness": the TRUE property, reduced to its core.

    The naive value-equality statement is false (Section "Semantics"); the
    corrected statement the Rust backend relies on observes only a first-order,
    closure-free result -- a constructor tree over [tBox], in which no
    [tFix]/[tLambda]/[tConst] occurs (a [nat], say). This section isolates,
    with fully [Qed]'d lemmas, exactly what is left to prove: a single
    CROSS-environment applicative bisimulation. Both intra-environment head
    swaps (the [tConst]/[tFix] interchange in [Sigma], and the
    [tConst]/[native_rec_body]-output interchange in [Sigma']) are discharged
    here; only the guarded-[tFix]-vs-[tConst]-recursion bisimulation remains,
    and it is stated as the explicit hypothesis [Hcore] of the reduction. *)

(** In [Sigma'], where [kn] is bound to [native_rec_body]'s output, that output
    is [tLambda]-headed (arity >= 1 always erases to a lambda body), hence an
    [atom] and thus a value, so [tConst kn] delta-steps directly to it. *)
Lemma const_unfolds_to_nrb {wfl : EWcbvEval.WcbvFlags}
      (Sigma' : global_declarations) (kn : kername)
      (decl' : constant_body) (d : def term) (na : name) (b : term) :
  declared_constant Sigma' kn decl' ->
  cst_body decl' = Some (native_rec_body kn (tFix [d] 0)) ->
  dbody d = tLambda na b ->
  eval Sigma' (tConst kn) (native_rec_body kn (tFix [d] 0)).
Proof.
  intros Hdecl' Hbody' Hlam.
  eapply eval_delta.
  - exact Hdecl'.
  - exact Hbody'.
  - apply eval_atom. rewrite native_rec_body_bare, Hlam. reflexivity.
Qed.

(** The two intra-environment head swaps are library facts, recorded below as
    the hypotheses [HswapSigma] and [HswapSigma'] of the reduction rather than
    inlined. Each is the instance of [WcbvEvalAux.eval_mkApps_heads] for two
    heads that evaluate, in the respective environment, to a common value:

    - in [Sigma], [tConst kn] and [tFix [d] 0] both evaluate to [tFix [d] 0]
      ([const_unfolds_to_fix] and [eval_atom] on the [tFix]);
    - in [Sigma'], [tConst kn] and [native_rec_body]'s output both evaluate to
      that (lambda-headed, hence [atom]) output ([const_unfolds_to_nrb] and
      [eval_atom] on the output).

    Both hold for every value [v] and every spine [args]. They are kept as
    hypotheses because [WcbvEvalAux.eval_mkApps_heads] is proved through the
    general [eval] value machinery and therefore carries MetaRocq's
    primitive-integer/float axioms in its assumption set; taking the swaps as
    hypotheses keeps every result in this file within the three primitive-type
    axioms. *)

(** First-order, closure-free values: a constructor tree over [tBox]. No
    [tFix]/[tLambda]/[tConst] occurs, so such a value cannot syntactically
    distinguish [Sigma]'s [tFix] from [Sigma']'s constant. This is the class of
    results the Rust backend actually observes (a [nat], a [bool], a list of
    them, ...). *)
Inductive fo_value : term -> Prop :=
| fo_box : fo_value tBox
| fo_construct (ind : inductive) (n : nat) (args : list term) :
    Forall fo_value args -> fo_value (mkApps (tConstruct ind n []) args).

(** The reduction. Composing the two intra-environment head swaps
    [HswapSigma], [HswapSigma'] (the library facts described above) turns the
    corrected, observation-restricted equivalence for [tConst kn] into a single
    CROSS-environment obligation [Hcore]: that the guarded-[tFix] recursion of
    [Sigma] and the recursion-through-[native_rec_body]'s-output of [Sigma']
    agree on the observed results. Everything except [Hcore] is either proved
    ([const_unfolds_to_fix], [const_unfolds_to_nrb]) or a bare instance of
    [WcbvEvalAux.eval_mkApps_heads] ([HswapSigma], [HswapSigma']); [Hcore] is
    the precise remaining gap.

    The reduction is pure logic (pointwise composition of the three relations)
    and parametric in the observation predicate [P]; instantiate [P := fo_value]
    for the first-order statement ([native_rec_body_fo_obs_equiv]). The
    first-order restriction is not needed for the reduction itself -- it is what
    is expected to make [Hcore] provable, since a constructor tree over [tBox]
    cannot observe the [tFix]/[tLambda] head distinction that sinks the
    unrestricted statement.

    THE REMAINING OBLIGATION ([Hcore]). For every spine [args] and observed
    [v],
      [eval Sigma (mkApps (tFix [d] 0) args) v
         <-> eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v].
    In [Sigma] the recursive self-reference in [dbody d] is the reconstructed
    [tFix [d] 0] (guarded fixpoint unfolding via [cunfold_fix]); in [Sigma'] it
    is [tConst kn], bound to [native_rec_body]'s output, which again contains
    [tConst kn]. Relating them is a step-indexed / coinductive applicative
    bisimulation over [eval] derivations, not a structural term induction:
    MetaRocq supplies the per-step lemmas ([eval_delta], [cunfold_fix],
    [eval_fix], determinism) but no substitution-congruence for [eval], so the
    bisimulation must be built from scratch. That construction is the sole
    ingredient still missing for a TCB-removing correctness proof. *)
Lemma native_rec_body_fo_obs_equiv_reduction {wfl : EWcbvEval.WcbvFlags}
      (Sigma Sigma' : global_declarations) (kn : kername) (d : def term)
      (P : term -> Prop) :
  (forall (args : list term) (v : term), P v ->
     ((eval Sigma  (mkApps (tConst kn) args) v ->
       eval Sigma  (mkApps (tFix [d] 0) args) v) *
      (eval Sigma  (mkApps (tFix [d] 0) args) v ->
       eval Sigma  (mkApps (tConst kn) args) v))%type) ->
  (forall (args : list term) (v : term), P v ->
     ((eval Sigma' (mkApps (tConst kn) args) v ->
       eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v) *
      (eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v ->
       eval Sigma' (mkApps (tConst kn) args) v))%type) ->
  (forall (args : list term) (v : term), P v ->
     ((eval Sigma  (mkApps (tFix [d] 0) args) v ->
       eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v) *
      (eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v ->
       eval Sigma  (mkApps (tFix [d] 0) args) v))%type) ->
  (forall (args : list term) (v : term), P v ->
     ((eval Sigma  (mkApps (tConst kn) args) v ->
       eval Sigma' (mkApps (tConst kn) args) v) *
      (eval Sigma' (mkApps (tConst kn) args) v ->
       eval Sigma  (mkApps (tConst kn) args) v))%type).
Proof.
  intros HswapSigma HswapSigma' Hcore args v HP.
  destruct (HswapSigma  args v HP) as [Sf Sb].
  destruct (HswapSigma' args v HP) as [Nf Nb].
  destruct (Hcore      args v HP) as [Cf Cb].
  split; intro H.
  - apply Nb, Cf, Sf, H.
  - apply Sb, Cb, Nf, H.
Qed.

(** The corrected first-order statement, as the [P := fo_value] instance of the
    reduction: given the two intra-environment head swaps ([HswapSigma],
    [HswapSigma']) and the cross-environment bisimulation on first-order results
    ([Hcore]), [tConst kn] is observationally equivalent across the two
    environments on every first-order value. This is the property the Rust
    backend relies on; the head swaps are instances of
    [WcbvEvalAux.eval_mkApps_heads] and only [Hcore] remains genuinely open. *)
Corollary native_rec_body_fo_obs_equiv {wfl : EWcbvEval.WcbvFlags}
      (Sigma Sigma' : global_declarations) (kn : kername) (d : def term) :
  (forall (args : list term) (v : term), fo_value v ->
     ((eval Sigma  (mkApps (tConst kn) args) v ->
       eval Sigma  (mkApps (tFix [d] 0) args) v) *
      (eval Sigma  (mkApps (tFix [d] 0) args) v ->
       eval Sigma  (mkApps (tConst kn) args) v))%type) ->
  (forall (args : list term) (v : term), fo_value v ->
     ((eval Sigma' (mkApps (tConst kn) args) v ->
       eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v) *
      (eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v ->
       eval Sigma' (mkApps (tConst kn) args) v))%type) ->
  (forall (args : list term) (v : term), fo_value v ->
     ((eval Sigma  (mkApps (tFix [d] 0) args) v ->
       eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v) *
      (eval Sigma' (mkApps (native_rec_body kn (tFix [d] 0)) args) v ->
       eval Sigma  (mkApps (tFix [d] 0) args) v))%type) ->
  (forall (args : list term) (v : term), fo_value v ->
     ((eval Sigma  (mkApps (tConst kn) args) v ->
       eval Sigma' (mkApps (tConst kn) args) v) *
      (eval Sigma' (mkApps (tConst kn) args) v ->
       eval Sigma  (mkApps (tConst kn) args) v))%type).
Proof.
  intros HswapSigma HswapSigma' Hcore.
  eapply native_rec_body_fo_obs_equiv_reduction; eassumption.
Qed.
