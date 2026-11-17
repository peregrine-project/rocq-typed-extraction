(** * The fixpoint and its native self-reference evaluate alike

    [NativeRecCorrect.v] reduces the first-order correctness of
    [native_rec_body] to a hypothesis [Hcore]: the constant [kn] bound to the
    guarded fixpoint [tFix [d] 0] in [Σ], and bound in [Σ'] to the fixpoint's
    body with the recursive variable replaced by [tConst kn], give the same
    first-order results.  This file proves it, for unguarded fixpoints
    ([with_guarded_fix = false]) and applied constructors
    ([with_constructor_as_block = false]), the flags at which the Rust backend
    consumes its λ□ program ([target_wcbv_flags]).

    The proof is a simulation in each direction.  [R baseF] relates a term of
    [Σ] to a term of [Σ'] that is the same up to occurrences of [tFix [d] 0] on
    the left against [tConst kn] or the body [nbody] on the right; [R baseB] is
    the converse.  Evaluation preserves both ([forward], [backward]), and on
    first-order values both are equality ([R_fo]).  The results are
    [fix_native_fo_equiv] and the head swaps [swap_fix] and [swap_body]. *)

From Stdlib Require Import List Bool Arith Lia.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import Kernames BasicAst.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils ELiftSubst ECSubst EInduction
  EGlobalEnv EWcbvEval.
From Equations Require Import Equations.
Import ListNotations.
From Stdlib Require Import ssreflect ssrbool.

Section Rel.
  Variable kn : kername.
  Variable d : def term.

  Definition nfix := tFix [d] 0.
  Definition nbody := csubst (tConst kn) 0 (dbody d).

  Definition brs_rel (R : term -> term -> Prop) :=
    Forall2 (fun (br br' : list name × term) => br.1 = br'.1 /\ R br.2 br'.2).
  Definition mfix_rel (R : term -> term -> Prop) :=
    Forall2 (fun (x y : def term) => dname x = dname y /\ rarg x = rarg y /\ R (dbody x) (dbody y)).

  (** [base] says which pairs of different terms are related; [N] closes it
      under the term formers. *)
  Variable base : term -> term -> Prop.

  Inductive R : term -> term -> Prop :=
  | R_box : R tBox tBox
  | R_rel n : R (tRel n) (tRel n)
  | R_var i : R (tVar i) (tVar i)
  | R_evar n l l' : Forall2 R l l' -> R (tEvar n l) (tEvar n l')
  | R_lambda na b b' : R b b' -> R (tLambda na b) (tLambda na b')
  | R_letin na b b' t t' : R b b' -> R t t' -> R (tLetIn na b t) (tLetIn na b' t')
  | R_app f f' a a' : R f f' -> R a a' -> R (tApp f a) (tApp f' a')
  | R_const c : R (tConst c) (tConst c)
  | R_construct ind c l l' : Forall2 R l l' -> R (tConstruct ind c l) (tConstruct ind c l')
  | R_case ci t t' brs brs' : R t t' -> brs_rel R brs brs' -> R (tCase ci t brs) (tCase ci t' brs')
  | R_proj p t t' : R t t' -> R (tProj p t) (tProj p t')
  | R_fix mf mf' idx : mfix_rel R mf mf' -> R (tFix mf idx) (tFix mf' idx)
  | R_cofix mf mf' idx : mfix_rel R mf mf' -> R (tCoFix mf idx) (tCoFix mf' idx)
  | R_prim_int i : R (tPrim (prim_int i)) (tPrim (prim_int i))
  | R_prim_float f : R (tPrim (prim_float f)) (tPrim (prim_float f))
  | R_prim_string s : R (tPrim (prim_string s)) (tPrim (prim_string s))
  | R_prim_array df df' v v' : R df df' -> Forall2 R v v' ->
      R (tPrim (prim_array {| array_default := df; array_value := v |}))
        (tPrim (prim_array {| array_default := df'; array_value := v' |}))
  | R_lazy t t' : R t t' -> R (tLazy t) (tLazy t')
  | R_force t t' : R t t' -> R (tForce t) (tForce t')
  | R_base t t' : base t t' -> R t t'.

  Lemma R_refl t : R t t.
  Proof.
    induction t using term_forall_list_ind; try now constructor.
    - constructor. induction X; constructor; auto.
    - constructor. induction X; constructor; auto.
    - constructor; auto. induction X; constructor; auto.
    - constructor. induction X; constructor; auto.
    - constructor. induction X; constructor; auto.
    - depelim X.
      + exact (R_prim_int i).
      + exact (R_prim_float f).
      + exact (R_prim_string s).
      + destruct p as [Hd Hv]. destruct a as [df v]; cbn in *.
        apply (R_prim_array df df v v); auto. induction Hv; constructor; auto.
  Qed.

  Lemma Forall2_R_refl l : Forall2 R l l.
  Proof. induction l; constructor; auto using R_refl. Qed.

  (** Substitution, for a [base] whose pairs are closed. *)
  Hypothesis base_closed : forall t t', base t t' -> closed t /\ closed t'.

  Lemma R_csubst a a' : R a a' -> forall k t t', R t t' -> R (csubst a k t) (csubst a' k t').
  Proof.
    intros Ha. fix IH 4. intros k t t' H. destruct H; cbn.
    - exact R_box.
    - destruct (Nat.compare k n); [exact Ha|exact (R_rel _)|exact (R_rel _)].
    - exact (R_var _).
    - apply R_evar. revert l l' H. fix aux 3. intros ? ? [|x y l l' Hxy Hl]; cbn.
      + constructor.
      + apply Forall2_cons; [apply IH; exact Hxy|apply aux; exact Hl].
    - apply R_lambda. apply IH. exact H.
    - apply R_letin; apply IH; assumption.
    - apply R_app; apply IH; assumption.
    - exact (R_const _).
    - apply R_construct. revert l l' H. fix aux 3. intros ? ? [|x y l l' Hxy Hl]; cbn.
      + constructor.
      + apply Forall2_cons; [apply IH; exact Hxy|apply aux; exact Hl].
    - apply R_case; [apply IH; exact H|]. unfold brs_rel in *.
      revert brs brs' H0. fix aux 3. intros ? ? [|x y l l' [Heq Hr] Hl]; cbn.
      + constructor.
      + apply Forall2_cons; [|apply aux; exact Hl]. cbn. rewrite Heq. split; [reflexivity|].
        apply IH. exact Hr.
    - apply R_proj. apply IH. exact H.
    - apply R_fix. unfold mfix_rel in *. rewrite -(Forall2_length H). generalize (#|mf| + k). intros k'.
      revert mf mf' H. fix aux 3. intros ? ? [|x y l l' (Hn & Hr & Hb) Hl]; cbn.
      + constructor.
      + apply Forall2_cons; [|apply aux; exact Hl]. cbn. split; [exact Hn|split; [exact Hr|]].
        apply IH. exact Hb.
    - apply R_cofix. unfold mfix_rel in *. rewrite -(Forall2_length H). generalize (#|mf| + k). intros k'.
      revert mf mf' H. fix aux 3. intros ? ? [|x y l l' (Hn & Hr & Hb) Hl]; cbn.
      + constructor.
      + apply Forall2_cons; [|apply aux; exact Hl]. cbn. split; [exact Hn|split; [exact Hr|]].
        apply IH. exact Hb.
    - exact (R_prim_int i).
    - exact (R_prim_float f).
    - exact (R_prim_string s).
    - apply (R_prim_array (csubst a k df) (csubst a' k df')); [apply IH; exact H|].
      revert v v' H0. fix aux 3. intros ? ? [|x y l l' Hxy Hl]; cbn.
      + constructor.
      + apply Forall2_cons; [apply IH; exact Hxy|apply aux; exact Hl].
    - apply R_lazy. apply IH. exact H.
    - apply R_force. apply IH. exact H.
    - destruct (base_closed _ _ H) as [Hc Hc'].
      rewrite !csubst_closed; [eapply closed_upwards; tea; lia|eapply closed_upwards; tea; lia|].
      now apply R_base.
  Qed.
End Rel.

(** ** Generic facts about [R] *)

Lemma F2_nth {A B} (P : A -> B -> Prop) l l' n x :
  Forall2 P l l' -> nth_error l n = Some x -> exists y, nth_error l' n = Some y /\ P x y.
Proof.
  intros H. induction H in n |- *; destruct n; cbn; try discriminate.
  - intros E. injection E as ->. eauto.
  - eauto.
Qed.

Lemma F2_nth_s {A B} (P : A -> B -> Prop) l l' n x :
  Forall2 P l l' -> nth_error l n = Some x -> {y | nth_error l' n = Some y /\ P x y}.
Proof.
  intros H E. destruct (nth_error l' n) as [y|] eqn:E'.
  - exists y. destruct (F2_nth _ _ _ _ _ H E) as (y' & Ey' & Hp). rewrite E' in Ey'.
    injection Ey' as ->. auto.
  - exfalso. destruct (F2_nth _ _ _ _ _ H E) as (y' & Ey' & Hp). congruence.
Qed.

Lemma F2_rev {A B} (P : A -> B -> Prop) l l' : Forall2 P l l' -> Forall2 P (List.rev l) (List.rev l').
Proof. induction 1; cbn; [constructor|]. apply Forall2_app; auto. Qed.

Lemma F2_skipn {A B} (P : A -> B -> Prop) n l l' : Forall2 P l l' -> Forall2 P (skipn n l) (skipn n l').
Proof.
  intros H. induction H in n |- *; destruct n; cbn.
  - constructor.
  - constructor.
  - constructor; auto.
  - apply IHForall2.
Qed.

Section Generic.
  Variable base : term -> term -> Prop.
  Hypothesis base_closed : forall t t', base t t' -> closed t /\ closed t'.
  Local Notation R := (R base).

  Lemma R_mkApps f f' l l' : R f f' -> Forall2 R l l' -> R (mkApps f l) (mkApps f' l').
  Proof. intros Hf H. induction H in f, f', Hf |- *; cbn; auto. apply IHForall2. now apply R_app. Qed.

  Lemma R_substl s s' t t' : Forall2 R s s' -> R t t' -> R (substl s t) (substl s' t').
  Proof.
    intros H. induction H in t, t' |- *; intros Ht; rewrite /substl /=; auto.
    apply IHForall2. now apply R_csubst.
  Qed.

  Lemma R_fix_subst mf mf' : mfix_rel R mf mf' -> Forall2 R (fix_subst mf) (fix_subst mf').
  Proof.
    intros H. unfold fix_subst. rewrite -(Forall2_length H).
    generalize #|mf| as n. induction n; constructor; auto. now apply R_fix.
  Qed.

  Lemma R_cofix_subst mf mf' : mfix_rel R mf mf' -> Forall2 R (cofix_subst mf) (cofix_subst mf').
  Proof.
    intros H. unfold cofix_subst. rewrite -(Forall2_length H).
    generalize #|mf| as n. induction n; constructor; auto. now apply R_cofix.
  Qed.

  Lemma R_cunfold_fix mf mf' idx n fn : mfix_rel R mf mf' -> cunfold_fix mf idx = Some (n, fn) ->
    {fn' | cunfold_fix mf' idx = Some (n, fn') /\ R fn fn'}.
  Proof.
    intros H. unfold cunfold_fix.
    destruct (nth_error mf idx) eqn:E; [|discriminate]. intros [= <- <-].
    destruct (F2_nth_s _ _ _ _ _ H E) as (y & Ey & (Hn & Hr & Hb)).
    rewrite Ey. eexists; split; [now rewrite Hr|]. apply R_substl; [now apply R_fix_subst|exact Hb].
  Qed.

  Lemma R_cunfold_cofix mf mf' idx n fn : mfix_rel R mf mf' -> cunfold_cofix mf idx = Some (n, fn) ->
    {fn' | cunfold_cofix mf' idx = Some (n, fn') /\ R fn fn'}.
  Proof.
    intros H. unfold cunfold_cofix.
    destruct (nth_error mf idx) eqn:E; [|discriminate]. intros [= <- <-].
    destruct (F2_nth_s _ _ _ _ _ H E) as (y & Ey & (Hn & Hr & Hb)).
    rewrite Ey. eexists; split; [now rewrite Hr|]. apply R_substl; [now apply R_cofix_subst|exact Hb].
  Qed.

  Lemma R_iota_red pars args args' br br' : Forall2 R args args' -> R br.2 br'.2 ->
    R (iota_red pars args br) (iota_red pars args' br').
  Proof. intros H Hb. unfold iota_red. apply R_substl; auto. now apply F2_rev, F2_skipn. Qed.

  Lemma R_repeat_box n : Forall2 R (repeat tBox n) (repeat tBox n).
  Proof. induction n; constructor; auto. apply R_box. Qed.
End Generic.

(** ** Evaluation facts *)

Lemma eval_not_const {wfl : WcbvFlags} Σ t v : eval Σ t v -> forall c, v <> tConst c.
Proof.
  intros ev. induction ev; intros c' Hc; try discriminate.
  all: try (match goal with IH : forall c, ?r <> tConst c |- _ => exact (IH c' Hc) end).
  subst. cbn in i. discriminate.
Qed.

Lemma eval_tFix_inv {wfl : WcbvFlags} Σ mf idx v : eval Σ (tFix mf idx) v -> v = tFix mf idx.
Proof. intros ev. depelim ev. reflexivity. Qed.

Lemma eval_tLambda_inv' {wfl : WcbvFlags} Σ na b v : eval Σ (tLambda na b) v -> v = tLambda na b.
Proof. intros ev. depelim ev. reflexivity. Qed.

Lemma eval_tApp_arg {wfl : WcbvFlags} Σ f a b r :
  eval Σ (tApp f b) r -> eval Σ a b -> value Σ b -> eval Σ (tApp f a) r.
Proof.
  intros ev ea vb. pose proof (value_final _ vb) as eb.
  depelim ev;
  try (match goal with H : eval Σ b ?av |- _ =>
         pose proof (eval_deterministic H eb) as E; subst av end).
  - eapply eval_box; eauto.
  - eapply eval_beta; eauto.
  - eapply eval_fix; eauto.
  - eapply eval_fix_value; eauto.
  - eapply eval_fix'; eauto.
  - eapply eval_construct; eauto.
  - eapply eval_app_cong; eauto.
  - cbn in i. discriminate.
Qed.

Lemma eval_tApp_head {wfl : WcbvFlags} Σ f h a r :
  eval Σ (tApp h a) r -> eval Σ f h -> value Σ h -> eval Σ (tApp f a) r.
Proof.
  intros ev ef vh. pose proof (value_final _ vh) as eh.
  depelim ev;
  try (match goal with H : eval Σ h ?hv |- _ => assert_fails (constr_eq hv h);
         pose proof (eval_deterministic H eh) as E; subst end).
  - eapply eval_box; eauto.
  - eapply eval_beta; eauto.
  - eapply eval_fix; eauto.
  - eapply eval_fix_value; eauto.
  - eapply eval_fix'; eauto.
  - eapply eval_construct; eauto.
  - eapply eval_app_cong; eauto.
  - cbn in i. discriminate.
Qed.

Lemma eval_tApp_head' {wfl : WcbvFlags} Σ g g' a r :
  (forall X, eval Σ g X -> eval Σ g' X) -> eval Σ (tApp g a) r -> eval Σ (tApp g' a) r.
Proof.
  intros Hg ev. depelim ev.
  - eapply eval_box; eauto.
  - eapply eval_beta; eauto.
  - eapply eval_fix; eauto.
  - eapply eval_fix_value; eauto.
  - eapply eval_fix'; eauto.
  - eapply eval_construct; eauto.
  - eapply eval_app_cong; eauto.
  - cbn in i. discriminate.
Qed.

Lemma eval_mkApps_head' {wfl : WcbvFlags} Σ g g' args r :
  (forall X, eval Σ g X -> eval Σ g' X) -> eval Σ (mkApps g args) r -> eval Σ (mkApps g' args) r.
Proof.
  induction args in g, g', r |- *; cbn; intros Hg ev; auto.
  eapply IHargs; [|exact ev]. intros X. now apply eval_tApp_head'.
Qed.

(** ** First-order values

    A first-order value is a constructor tree over [tBox]; [fo] over-approximates
    it by allowing any application of such trees.  On it, a relation [R base]
    whose base pairs never start from such a tree is equality. *)

Inductive fo : term -> Prop :=
| fo_box : fo tBox
| fo_construct ind n : fo (tConstruct ind n [])
| fo_app f a : fo f -> fo a -> fo (tApp f a).

Lemma fo_mkApps f args : fo f -> Forall fo args -> fo (mkApps f args).
Proof. intros Hf H. induction H in f, Hf |- *; cbn; auto. apply IHForall. now constructor. Qed.

Lemma R_fo base (nb : forall t t', base t t' -> ~ fo t) x y : R base x y -> fo x -> y = x.
Proof.
  induction 1; intros Hx; try (inversion Hx; fail).
  - reflexivity.
  - inversion Hx; subst. f_equal; auto.
  - inversion Hx; subst. inversion H; subst. reflexivity.
  - exfalso. exact (nb _ _ H Hx).
Qed.

(** ** The forward simulation: from the fixpoint to the self-reference *)

Section Forward.
  Context {wfl : WcbvFlags}.
  Hypothesis Hg : with_guarded_fix = false.
  Hypothesis Hb : with_constructor_as_block = false.
  Variables (kn : kername) (d : def term) (Σ Σ' : global_declarations).
  Hypothesis HΣ : declared_constant Σ kn {| cst_body := Some (nfix d) |}.
  Hypothesis HΣ' : declared_constant Σ' kn {| cst_body := Some (nbody kn d) |}.
  Hypothesis Hother : forall c, c <> kn -> lookup_env Σ c = lookup_env Σ' c.
  Hypothesis Hcl : closedn 1 (dbody d).
  Hypothesis Hlam : isLambda (dbody d).

  Definition baseF t t' := t = nfix d /\ (t' = tConst kn \/ t' = nbody kn d).
  Local Notation RF := (R baseF).

  Lemma closed_nfix : closed (nfix d).
  Proof. unfold nfix; simpl. unfold test_def; simpl. now rewrite Hcl. Qed.

  Lemma closed_nbody : closed (nbody kn d).
  Proof. unfold nbody. eapply closed_csubst; auto. Qed.

  Lemma baseF_closed t t' : baseF t t' -> closed t /\ closed t'.
  Proof.
    intros [-> [-> | ->]]; split; auto using closed_nfix, closed_nbody.
  Qed.

  Lemma nbody_lambda : isLambda (nbody kn d).
  Proof. unfold nbody. now apply isLambda_csubst. Qed.

  Lemma eval_nbody : eval Σ' (nbody kn d) (nbody kn d).
  Proof. apply eval_atom. pose proof nbody_lambda. destruct (nbody kn d); cbn in *; auto. Qed.

  Lemma eval_kn' : eval Σ' (tConst kn) (nbody kn d).
  Proof. eapply eval_delta; [exact HΣ'|reflexivity|exact eval_nbody]. Qed.

  Lemma lookup_minductive_eq m : lookup_minductive Σ m = lookup_minductive Σ' m.
  Proof.
    unfold lookup_minductive. destruct (eqb_spec m kn) as [->|ne].
    - unfold declared_constant in HΣ, HΣ'. now rewrite HΣ HΣ'.
    - now rewrite Hother.
  Qed.

  Lemma lookup_inductive_eq i : lookup_inductive Σ i = lookup_inductive Σ' i.
  Proof. unfold lookup_inductive. now rewrite lookup_minductive_eq. Qed.

  Lemma lookup_constructor_eq i c : lookup_constructor Σ i c = lookup_constructor Σ' i c.
  Proof. unfold lookup_constructor. now rewrite lookup_inductive_eq. Qed.

  Lemma cipd_eq i c : constructor_isprop_pars_decl Σ i c = constructor_isprop_pars_decl Σ' i c.
  Proof. unfold constructor_isprop_pars_decl. now rewrite lookup_constructor_eq. Qed.

  Lemma iiap_eq i : inductive_isprop_and_pars Σ i = inductive_isprop_and_pars Σ' i.
  Proof. unfold inductive_isprop_and_pars. now rewrite lookup_inductive_eq. Qed.

  Ltac nobase := match goal with Hb0 : baseF _ _ |- _ => destruct Hb0 as [Hfx _]; inversion Hfx end.

  Lemma RF_box y : RF tBox y -> y = tBox.
  Proof. intros H; inversion H; subst; [reflexivity|nobase]. Qed.

  Ltac imp H := exfalso; inversion H; subst; nobase; fail.

  Lemma RF_lambda na b y : RF (tLambda na b) y -> {b' | y = tLambda na b' /\ RF b b'}.
  Proof. intros H. destruct y; try imp H. exists y. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_lazy t y : RF (tLazy t) y -> {t' | y = tLazy t' /\ RF t t'}.
  Proof. intros H. destruct y; try imp H. exists y. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_app f a y : RF (tApp f a) y -> {f' & {a' | y = tApp f' a' /\ RF f f' /\ RF a a'}}.
  Proof. intros H. destruct y; try imp H. exists y1, y2. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_letin na b t y : RF (tLetIn na b t) y -> {b' & {t' | y = tLetIn na b' t' /\ RF b b' /\ RF t t'}}.
  Proof. intros H. destruct y; try imp H. exists y1, y2. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_case ci t brs y : RF (tCase ci t brs) y ->
    {t' & {brs' | y = tCase ci t' brs' /\ RF t t' /\ brs_rel RF brs brs'}}.
  Proof. intros H. destruct y; try imp H. exists y, brs0. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_proj p t y : RF (tProj p t) y -> {t' | y = tProj p t' /\ RF t t'}.
  Proof. intros H. destruct y; try imp H. exists y. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_force t y : RF (tForce t) y -> {t' | y = tForce t' /\ RF t t'}.
  Proof. intros H. destruct y; try imp H. exists y. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_const c y : RF (tConst c) y -> y = tConst c.
  Proof. intros H; inversion H; subst; [reflexivity|nobase]. Qed.

  Lemma RF_construct ind c l y : RF (tConstruct ind c l) y -> {l' | y = tConstruct ind c l' /\ Forall2 RF l l'}.
  Proof. intros H. destruct y; try imp H. exists args. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_cofix mf idx y : RF (tCoFix mf idx) y -> {mf' | y = tCoFix mf' idx /\ mfix_rel RF mf mf'}.
  Proof. intros H. destruct y; try imp H. exists mfix. inversion H; subst; [auto|nobase]. Qed.

  Lemma RF_fix mf idx y : RF (tFix mf idx) y ->
    {mf' | y = tFix mf' idx /\ mfix_rel RF mf mf'} +
    ((mf = [d] /\ idx = 0 /\ y = tConst kn) + (mf = [d] /\ idx = 0 /\ y = nbody kn d)).
  Proof.
    intros H. pose proof nbody_lambda as Hnl.
    destruct y; try (exfalso; inversion H; subst;
      match goal with Hb : baseF _ _ |- _ =>
        destruct Hb as [_ [Hy|Hy]]; [discriminate|rewrite -Hy in Hnl; cbn in Hnl; discriminate] end; fail).
    - right; right. inversion H; subst.
      match goal with Hb : baseF _ _ |- _ => destruct Hb as [Hfx [Hy|Hy]]; [discriminate|] end.
      unfold nfix in Hfx. injection Hfx as -> ->. auto.
    - right; left. inversion H; subst.
      match goal with Hb : baseF _ _ |- _ => destruct Hb as [Hfx [Hy|Hy]] end.
      + unfold nfix in Hfx. injection Hfx as -> ->. auto.
      + rewrite -Hy in Hnl. cbn in Hnl. discriminate.
    - left. exists mfix. inversion H; subst; [auto|].
      match goal with Hb : baseF _ _ |- _ =>
        destruct Hb as [_ [Hy|Hy]]; [discriminate|rewrite -Hy in Hnl; cbn in Hnl; discriminate] end.
  Qed.

  Lemma RF_mkApps_construct ind c args y : RF (mkApps (tConstruct ind c []) args) y ->
    {args' | y = mkApps (tConstruct ind c []) args' /\ Forall2 RF args args'}.
  Proof.
    revert y; induction args using rev_ind; intros y.
    - cbn. intros H. apply RF_construct in H as (l' & -> & Hl). destruct l'; [|exfalso; inversion Hl]. exists []; split; auto.
    - rewrite mkApps_app. cbn. intros H. apply RF_app in H as (f' & a' & -> & Hf & Ha).
      apply IHargs in Hf as (args' & -> & Hargs). exists (args' ++ [a']). split.
      + now rewrite mkApps_app.
      + apply Forall2_app; auto.
  Qed.

  Lemma RF_mkApps_cofix mf idx args y : RF (mkApps (tCoFix mf idx) args) y ->
    {mf' & {args' | y = mkApps (tCoFix mf' idx) args' /\ mfix_rel RF mf mf' /\ Forall2 RF args args'}}.
  Proof.
    revert y; induction args using rev_ind; intros y.
    - cbn. intros H. apply RF_cofix in H as (mf' & -> & Hm). exists mf', []; split; auto.
    - rewrite mkApps_app. cbn. intros H. apply RF_app in H as (f' & a' & -> & Hf & Ha).
      apply IHargs in Hf as (mf' & args' & -> & Hm & Hargs). exists mf', (args' ++ [a']). split; [|split; auto].
      + now rewrite mkApps_app.
      + apply Forall2_app; auto.
  Qed.

  Lemma RF_head_shape x y : RF x y ->
    isConstructApp x = isConstructApp y /\ isPrimApp x = isPrimApp y /\ isLazyApp x = isLazyApp y.
  Proof.
    induction 1; try now (cbn; auto).
    - rewrite /isConstructApp /isPrimApp /isLazyApp !head_tApp. exact IHR1.
    - destruct H as [-> [-> | ->]]; [cbn; auto|].
      pose proof nbody_lambda. destruct (nbody kn d); cbn in *; try discriminate; auto.
  Qed.

  Lemma RF_cond x y : RF x y ->
    ~~ (isLambda x || isFix x || isBox x || isConstructApp x || isPrimApp x || isLazyApp x) ->
    ~~ (isLambda y || isFix y || isBox y || isConstructApp y || isPrimApp y || isLazyApp y).
  Proof.
    intros H. pose proof (RF_head_shape _ _ H) as (E1 & E2 & E3). rewrite -E1 -E2 -E3.
    destruct H; cbn; auto.
    destruct H as [-> _]. cbn. discriminate.
  Qed.

  Local Notation sim t v := (forall t', RF t t' -> ∑ v', eval Σ' t' v' × RF v v').

  Lemma RF_base_nbody : RF (nfix d) (nbody kn d).
  Proof. apply R_base. split; auto. Qed.

  Lemma RF_fn : RF (csubst (nfix d) 0 (dbody d)) (nbody kn d).
  Proof.
    unfold nbody. apply R_csubst; [exact baseF_closed| |apply R_refl].
    apply R_base. split; auto.
  Qed.


  Lemma forward t v (ev : eval Σ t v) : sim t v.
  Proof.
    induction ev; intros t2 Ht.
    - (* box *)
      apply RF_app in Ht as (a2 & t2' & -> & Ha & Ht).
      destruct (IHev1 _ Ha) as (w & ew & Hw). apply RF_box in Hw as ->.
      destruct (IHev2 _ Ht) as (w' & ew' & Hw').
      exists tBox. split; [eapply eval_box; eauto|apply R_box].
    - (* beta *)
      apply RF_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw). apply RF_lambda in Hw as (b2 & -> & Hb2).
      destruct (IHev2 _ Ha) as (a2' & ea2 & Ha2).
      destruct (IHev3 (csubst a2' 0 b2)) as (r2 & er2 & Hr2).
      { apply R_csubst; auto. exact baseF_closed. }
      exists r2. split; [eapply eval_beta; eauto|auto].
    - (* zeta *)
      apply RF_letin in Ht as (b2 & t3 & -> & Hb2 & Ht3).
      destruct (IHev1 _ Hb2) as (w & ew & Hw).
      destruct (IHev2 (csubst w 0 t3)) as (r2 & er2 & Hr2).
      { apply R_csubst; auto. exact baseF_closed. }
      exists r2. split; [eapply eval_zeta; eauto|auto].
    - (* iota *)
      apply RF_case in Ht as (discr2 & brs2 & -> & Hd & Hbrs).
      destruct (IHev1 _ Hd) as (w & ew & Hw). apply RF_mkApps_construct in Hw as (args2 & -> & Hargs).
      destruct (F2_nth_s _ _ _ _ _ Hbrs e2) as (br2 & Hbr2 & Heq & Hbr).
      destruct (IHev2 (iota_red pars args2 br2)) as (r2 & er2 & Hr2).
      { apply R_iota_red; auto. exact baseF_closed. }
      exists r2. split; auto.
      eapply eval_iota; eauto.
      + now rewrite -cipd_eq.
      + now rewrite -(Forall2_length Hargs).
      + rewrite -Heq. rewrite -(Forall2_length (F2_skipn _ pars _ _ Hargs)). assumption.
    - (* iota_block *)
      congruence.
    - (* iota_sing *)
      apply RF_case in Ht as (discr2 & brs2 & -> & Hd & Hbrs).
      destruct (IHev1 _ Hd) as (w & ew & Hw). apply RF_box in Hw as ->.
      subst brs. destruct brs2 as [|[n2 f2] [|]];
        [exfalso; inversion Hbrs| |exfalso; inversion Hbrs;
         match goal with H : Forall2 _ [] (_ :: _) |- _ => inversion H end].
      assert (n = n2 /\ RF f4 f2) as [-> Hf]
        by (inversion Hbrs as [|? ? ? ? [Heq Hf] Hnil]; subst; cbn in *; auto).
      destruct (IHev2 (substl (repeat tBox #|n2|) f2)) as (r2 & er2 & Hr2).
      { apply R_substl; [exact baseF_closed|apply R_repeat_box|exact Hf]. }
      exists r2. split; auto. eapply eval_iota_sing; eauto. now rewrite -iiap_eq.
    - (* fix, guarded *)
      rewrite Hg in guarded. discriminate.
    - (* fix_value, guarded *)
      rewrite Hg in guarded. discriminate.
    - (* fix', unguarded *)
      apply RF_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw).
      destruct (IHev2 _ Ha) as (av2 & eav2 & Hav).
      apply RF_fix in Hw as [(mf2 & -> & Hm) | [(-> & -> & ->) | (-> & -> & ->)]].
      + destruct (R_cunfold_fix _ baseF_closed _ _ _ _ _ Hm e0) as (fn2 & e2 & Hfn).
        destruct (IHev3 (tApp fn2 av2)) as (r2 & er2 & Hr2); [now apply R_app|].
        exists r2. split; auto. eapply eval_fix'; eauto.
      + exfalso. exact (eval_not_const _ _ _ ew kn eq_refl).
      + (* the fixpoint against its native body: unfold on the left, beta on the right *)
        cbn in e0. injection e0 as <- <-.
        destruct (IHev3 (tApp (nbody kn d) av2)) as (r2 & er2 & Hr2).
        { apply R_app; auto. rewrite /substl /=. exact RF_fn. }
        exists r2. split; auto.
        eapply eval_tApp_arg; [|exact eav2|now eapply eval_to_value].
        eapply eval_tApp_head; [exact er2|exact ew|]. now eapply eval_to_value.
    - (* cofix_case *)
      apply RF_case in Ht as (discr2 & brs2 & -> & Hd & Hbrs).
      destruct (IHev1 _ Hd) as (w & ew & Hw).
      apply RF_mkApps_cofix in Hw as (mf2 & args2 & -> & Hm & Hargs).
      destruct (R_cunfold_cofix _ baseF_closed _ _ _ _ _ Hm e0) as (fn2 & e2 & Hfn).
      destruct (IHev2 (tCase ip (mkApps fn2 args2) brs2)) as (r2 & er2 & Hr2).
      { apply R_case; auto. now apply R_mkApps. }
      exists r2. split; auto. eapply eval_cofix_case; eauto.
    - (* cofix_proj *)
      apply RF_proj in Ht as (discr2 & -> & Hd).
      destruct (IHev1 _ Hd) as (w & ew & Hw).
      apply RF_mkApps_cofix in Hw as (mf2 & args2 & -> & Hm & Hargs).
      destruct (R_cunfold_cofix _ baseF_closed _ _ _ _ _ Hm e0) as (fn2 & e2 & Hfn).
      destruct (IHev2 (tProj p (mkApps fn2 args2))) as (r2 & er2 & Hr2).
      { apply R_proj. now apply R_mkApps. }
      exists r2. split; auto. eapply eval_cofix_proj; eauto.
    - (* delta *)
      apply RF_const in Ht as ->.
      destruct (eq_dec c kn) as [->|ne].
      + assert (decl = {| cst_body := Some (nfix d) |}) as ->.
        { unfold declared_constant in isdecl, HΣ. rewrite HΣ in isdecl. now injection isdecl. }
        cbn in e. injection e as <-. apply eval_tFix_inv in ev as ->.
        exists (nbody kn d). split; [exact eval_kn'|exact RF_base_nbody].
      + destruct (IHev body) as (r2 & er2 & Hr2); [apply R_refl|].
        exists r2. split; auto. eapply eval_delta; eauto.
        unfold declared_constant in *. now rewrite -Hother.
    - (* proj *)
      apply RF_proj in Ht as (discr2 & -> & Hd).
      destruct (IHev1 _ Hd) as (w & ew & Hw). apply RF_mkApps_construct in Hw as (args2 & -> & Hargs).
      destruct (F2_nth_s _ _ _ _ _ Hargs e3) as (a2 & Ha2 & Ha).
      destruct (IHev2 _ Ha) as (r2 & er2 & Hr2).
      exists r2. split; auto. eapply eval_proj; eauto.
      + now rewrite -cipd_eq.
      + now rewrite -(Forall2_length Hargs).
    - (* proj_block *)
      congruence.
    - (* proj_prop *)
      apply RF_proj in Ht as (discr2 & -> & Hd).
      destruct (IHev _ Hd) as (w & ew & Hw). apply RF_box in Hw as ->.
      exists tBox. split; [eapply eval_proj_prop; eauto; now rewrite -iiap_eq|apply R_box].
    - (* construct *)
      apply RF_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw). apply RF_mkApps_construct in Hw as (args2 & -> & Hargs).
      destruct (IHev2 _ Ha) as (a2' & ea2 & Ha2).
      exists (tApp (mkApps (tConstruct ind c []) args2) a2'). split.
      + eapply eval_construct; eauto.
        * now rewrite -lookup_constructor_eq.
        * now rewrite -(Forall2_length Hargs).
      + apply R_app; auto. apply R_mkApps; auto. apply R_construct. constructor.
    - (* construct_block *)
      congruence.
    - (* app_cong *)
      apply RF_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw).
      destruct (IHev2 _ Ha) as (a2' & ea2 & Ha2).
      exists (tApp w a2'). split; [|now apply R_app].
      eapply eval_app_cong; eauto.
      rewrite Hg in i |- *. exact (RF_cond _ _ Hw i).
    - (* prim *)
      destruct X.
      + assert (t2 = tPrim (prim_int i)) as -> by (inversion Ht; subst; [reflexivity|nobase]).
        exists (tPrim (prim_int i)). split; [constructor; constructor|exact (R_prim_int _ i)].
      + assert (t2 = tPrim (prim_float f)) as -> by (inversion Ht; subst; [reflexivity|nobase]).
        exists (tPrim (prim_float f)). split; [constructor; constructor|exact (R_prim_float _ f)].
      + assert (t2 = tPrim (prim_string s)) as -> by (inversion Ht; subst; [reflexivity|nobase]).
        exists (tPrim (prim_string s)). split; [constructor; constructor|exact (R_prim_string _ s)].
      + destruct t2; try (exfalso; inversion Ht; subst; nobase; fail).
        destruct prim as [tag m]. destruct m; try (exfalso; inversion Ht; subst; nobase; fail).
        destruct a1 as [df2 v2].
        assert (RF def df2 /\ Forall2 RF v v2) as [Hdf Hv] by (inversion Ht; subst; [auto|nobase]).
        destruct (s _ Hdf) as (df2' & edf2 & Hdf2).
        assert (∑ v2', All2_Set (eval Σ') v2 v2' × Forall2 RF v' v2') as (v2' & ev2 & Hv2).
        { clear -a Hv. induction ev in v2, Hv, a |- *.
          - destruct v2; [exists []; split; constructor|exfalso; inversion Hv].
          - destruct v2 as [|x2 v2]; [exfalso; inversion Hv|].
            assert (RF x x2 /\ Forall2 RF l v2) as [Hx Hl] by (inversion Hv; auto).
            destruct a as [IHx a].
            destruct (IHx _ Hx) as (y2 & ey2 & Hy).
            destruct (IHev a v2 Hl) as (v2' & ev2 & Hv2).
            exists (y2 :: v2'). split; constructor; auto. }
        exists (tPrim (prim_array {| array_default := df2'; array_value := v2' |})). split.
        * apply eval_prim. exact (evalPrimArray (eval Σ') v2 df2 v2' df2' ev2 edf2).
        * apply R_prim_array; auto.
    - (* force *)
      apply RF_force in Ht as (t3 & -> & Ht3).
      destruct (IHev1 _ Ht3) as (w & ew & Hw). apply RF_lazy in Hw as (t4 & -> & Ht4).
      destruct (IHev2 _ Ht4) as (r2 & er2 & Hr2).
      exists r2. split; auto. eapply eval_force; eauto.
    - (* atom *)
      destruct t; try (cbn in i; discriminate).
      + apply RF_box in Ht as ->. exists tBox. split; [now apply eval_atom|apply R_box].
      + apply RF_lambda in Ht as (b2 & -> & Hb2). exists (tLambda na b2). split; [now apply eval_atom|now apply R_lambda].
      + destruct args; [|cbn in i; discriminate].
        apply RF_construct in Ht as (l2 & -> & Hl). destruct l2; [|exfalso; inversion Hl].
        exists (tConstruct ind n []). split; [|apply R_construct; constructor].
        apply eval_atom. unfold atom in *. now rewrite -lookup_constructor_eq.
      + apply RF_fix in Ht as [(mf2 & -> & Hm) | [(-> & -> & ->) | (-> & -> & ->)]].
        * exists (tFix mf2 idx). split; [now apply eval_atom|now apply R_fix].
        * exists (nbody kn d). split; [exact eval_kn'|exact RF_base_nbody].
        * exists (nbody kn d). split; [exact eval_nbody|exact RF_base_nbody].
      + apply RF_cofix in Ht as (mf2 & -> & Hm). exists (tCoFix mf2 idx). split; [now apply eval_atom|now apply R_cofix].
      + apply RF_lazy in Ht as (t2' & -> & Ht2). exists (tLazy t2'). split; [now apply eval_atom|now apply R_lazy].
  Qed.

  (** ** The backward simulation: from the self-reference to the fixpoint *)

  Definition baseB t t' := t' = nfix d /\ (t = tConst kn \/ t = nbody kn d).
  Local Notation RB := (R baseB).

  Lemma baseB_closed t t' : baseB t t' -> closed t /\ closed t'.
  Proof. intros [-> [-> | ->]]; split; auto using closed_nfix, closed_nbody. Qed.

  Ltac nobaseB := match goal with Hb0 : baseB _ _ |- _ =>
    let Hl := fresh in pose proof nbody_lambda as Hl;
    destruct Hb0 as [Hy [Hx|Hx]];
    first [unfold nfix in Hy; discriminate | discriminate | rewrite -Hx in Hl; cbn in Hl; discriminate] end.
  Ltac impB H := exfalso; inversion H; subst; nobaseB; fail.

  Lemma RB_box y : RB tBox y -> y = tBox.
  Proof. intros H; inversion H; subst; [reflexivity|nobaseB]. Qed.

  Lemma RB_lazy t y : RB (tLazy t) y -> {t' | y = tLazy t' /\ RB t t'}.
  Proof. intros H. destruct y; try impB H. exists y. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_app f a y : RB (tApp f a) y -> {f' & {a' | y = tApp f' a' /\ RB f f' /\ RB a a'}}.
  Proof. intros H. destruct y; try impB H. exists y1, y2. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_letin na b t y : RB (tLetIn na b t) y -> {b' & {t' | y = tLetIn na b' t' /\ RB b b' /\ RB t t'}}.
  Proof. intros H. destruct y; try impB H. exists y1, y2. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_case ci t brs y : RB (tCase ci t brs) y ->
    {t' & {brs' | y = tCase ci t' brs' /\ RB t t' /\ brs_rel RB brs brs'}}.
  Proof. intros H. destruct y; try impB H. exists y, brs0. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_proj p t y : RB (tProj p t) y -> {t' | y = tProj p t' /\ RB t t'}.
  Proof. intros H. destruct y; try impB H. exists y. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_force t y : RB (tForce t) y -> {t' | y = tForce t' /\ RB t t'}.
  Proof. intros H. destruct y; try impB H. exists y. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_construct ind c l y : RB (tConstruct ind c l) y -> {l' | y = tConstruct ind c l' /\ Forall2 RB l l'}.
  Proof. intros H. destruct y; try impB H. exists args. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_cofix mf idx y : RB (tCoFix mf idx) y -> {mf' | y = tCoFix mf' idx /\ mfix_rel RB mf mf'}.
  Proof. intros H. destruct y; try impB H. exists mfix. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_fix mf idx y : RB (tFix mf idx) y -> {mf' | y = tFix mf' idx /\ mfix_rel RB mf mf'}.
  Proof. intros H. destruct y; try impB H. exists mfix. inversion H; subst; [auto|nobaseB]. Qed.

  Lemma RB_const c y : RB (tConst c) y -> (y = tConst c) + (c = kn /\ y = nfix d).
  Proof.
    intros H. destruct (eq_dec y (tConst c)) as [->|ne]; [now left|right].
    inversion H; subst; [congruence|].
    match goal with Hb0 : baseB _ _ |- _ => destruct Hb0 as [-> [Hx|Hx]] end.
    - injection Hx as ->. auto.
    - exfalso. pose proof nbody_lambda as Hl. rewrite -Hx in Hl. discriminate.
  Qed.

  Lemma RB_lambda na b y : RB (tLambda na b) y ->
    {b' | y = tLambda na b' /\ RB b b'} + (tLambda na b = nbody kn d /\ y = nfix d).
  Proof.
    intros H. destruct y; try impB H.
    - left. exists y. inversion H; subst; [auto|nobaseB].
    - right. inversion H; subst.
      match goal with Hb0 : baseB _ _ |- _ => destruct Hb0 as [Hfx [Hx|Hx]]; [discriminate|auto] end.
  Qed.

  Lemma RB_mkApps_construct ind c args y : RB (mkApps (tConstruct ind c []) args) y ->
    {args' | y = mkApps (tConstruct ind c []) args' /\ Forall2 RB args args'}.
  Proof.
    revert y; induction args using rev_ind; intros y.
    - cbn. intros H. apply RB_construct in H as (l' & -> & Hl). destruct l'; [|exfalso; inversion Hl]. exists []; split; auto.
    - rewrite mkApps_app. cbn. intros H. apply RB_app in H as (f' & a' & -> & Hf & Ha).
      apply IHargs in Hf as (args' & -> & Hargs). exists (args' ++ [a']). split.
      + now rewrite mkApps_app.
      + apply Forall2_app; auto.
  Qed.

  Lemma RB_mkApps_cofix mf idx args y : RB (mkApps (tCoFix mf idx) args) y ->
    {mf' & {args' | y = mkApps (tCoFix mf' idx) args' /\ mfix_rel RB mf mf' /\ Forall2 RB args args'}}.
  Proof.
    revert y; induction args using rev_ind; intros y.
    - cbn. intros H. apply RB_cofix in H as (mf' & -> & Hm). exists mf', []; split; auto.
    - rewrite mkApps_app. cbn. intros H. apply RB_app in H as (f' & a' & -> & Hf & Ha).
      apply IHargs in Hf as (mf' & args' & -> & Hm & Hargs). exists mf', (args' ++ [a']). split; [|split; auto].
      + now rewrite mkApps_app.
      + apply Forall2_app; auto.
  Qed.

  Lemma RB_head_shape x y : RB x y ->
    isConstructApp x = isConstructApp y /\ isPrimApp x = isPrimApp y /\ isLazyApp x = isLazyApp y.
  Proof.
    induction 1; try now (cbn; auto).
    - rewrite /isConstructApp /isPrimApp /isLazyApp !head_tApp. exact IHR1.
    - destruct H as [-> [-> | ->]]; [cbn; auto|].
      pose proof nbody_lambda. destruct (nbody kn d); cbn in *; try discriminate; auto.
  Qed.

  Lemma RB_cond x y : RB x y -> (forall c, x <> tConst c) ->
    ~~ (isLambda x || isFix x || isBox x || isConstructApp x || isPrimApp x || isLazyApp x) ->
    ~~ (isLambda y || isFix y || isBox y || isConstructApp y || isPrimApp y || isLazyApp y).
  Proof.
    intros H Hnc. pose proof (RB_head_shape _ _ H) as (E1 & E2 & E3). rewrite -E1 -E2 -E3.
    destruct H; cbn; auto.
    destruct H as [_ [-> | ->]]; [now destruct (Hnc kn)|].
    pose proof nbody_lambda. destruct (nbody kn d); cbn in *; try discriminate; auto.
  Qed.

  Local Notation simB t v := (forall t', RB t t' -> ∑ v', eval Σ t' v' × RB v v').

  Lemma eval_nfix : eval Σ (nfix d) (nfix d).
  Proof. now apply eval_atom. Qed.

  Lemma eval_kn : eval Σ (tConst kn) (nfix d).
  Proof. eapply eval_delta; [exact HΣ|reflexivity|exact eval_nfix]. Qed.

  Lemma RB_base_nbody : RB (nbody kn d) (nfix d).
  Proof. apply R_base. split; auto. Qed.

  Lemma dbody_lam : {na0 & {b0 | dbody d = tLambda na0 b0}}.
  Proof. destruct (dbody d); try discriminate. eauto. Qed.

  Lemma eval_nbody_inv v : eval Σ' (nbody kn d) v -> v = nbody kn d.
  Proof.
    destruct dbody_lam as (na0 & b0 & E). unfold nbody. rewrite E. cbn.
    intros ev. now apply eval_tLambda_inv' in ev.
  Qed.

  Lemma backward t v (ev : eval Σ' t v) : simB t v.
  Proof.
    induction ev; intros t2 Ht.
    - (* box *)
      apply RB_app in Ht as (a2 & t2' & -> & Ha & Ht).
      destruct (IHev1 _ Ha) as (w & ew & Hw). apply RB_box in Hw as ->.
      destruct (IHev2 _ Ht) as (w' & ew' & Hw').
      exists tBox. split; [eapply eval_box; eauto|apply R_box].
    - (* beta *)
      apply RB_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw).
      destruct (IHev2 _ Ha) as (a2' & ea2 & Ha2).
      apply RB_lambda in Hw as [(b2 & -> & Hb2) | (Hlb & ->)].
      + destruct (IHev3 (csubst a2' 0 b2)) as (r2 & er2 & Hr2).
        { apply R_csubst; auto. exact baseB_closed. }
        exists r2. split; [eapply eval_beta; eauto|auto].
      + (* the native body against the fixpoint: beta on the left, unfold on the right *)
        destruct dbody_lam as (na0 & b0 & E).
        unfold nbody in Hlb. rewrite E in Hlb. cbn in Hlb. injection Hlb as -> ->.
        destruct (IHev3 (csubst a2' 0 (csubst (nfix d) 1 b0))) as (r2 & er2 & Hr2).
        { apply R_csubst; [exact baseB_closed|exact Ha2|].
          apply R_csubst; [exact baseB_closed| |apply R_refl].
          apply R_base. split; auto. }
        exists r2. split; auto.
        eapply eval_fix'; [exact Hg|exact ew| |exact ea2|].
        * cbn. reflexivity.
        * rewrite /substl /= E /=.
          eapply eval_beta; [now apply eval_atom| |exact er2].
          eapply value_final. now eapply eval_to_value.
    - (* zeta *)
      apply RB_letin in Ht as (b2 & t3 & -> & Hb2 & Ht3).
      destruct (IHev1 _ Hb2) as (w & ew & Hw).
      destruct (IHev2 (csubst w 0 t3)) as (r2 & er2 & Hr2).
      { apply R_csubst; auto. exact baseB_closed. }
      exists r2. split; [eapply eval_zeta; eauto|auto].
    - (* iota *)
      apply RB_case in Ht as (discr2 & brs2 & -> & Hd & Hbrs).
      destruct (IHev1 _ Hd) as (w & ew & Hw). apply RB_mkApps_construct in Hw as (args2 & -> & Hargs).
      destruct (F2_nth_s _ _ _ _ _ Hbrs e2) as (br2 & Hbr2 & Heq & Hbr).
      destruct (IHev2 (iota_red pars args2 br2)) as (r2 & er2 & Hr2).
      { apply R_iota_red; auto. exact baseB_closed. }
      exists r2. split; auto.
      eapply eval_iota; eauto.
      + now rewrite cipd_eq.
      + now rewrite -(Forall2_length Hargs).
      + rewrite -Heq. rewrite -(Forall2_length (F2_skipn _ pars _ _ Hargs)). assumption.
    - (* iota_block *)
      congruence.
    - (* iota_sing *)
      apply RB_case in Ht as (discr2 & brs2 & -> & Hd & Hbrs).
      destruct (IHev1 _ Hd) as (w & ew & Hw). apply RB_box in Hw as ->.
      subst brs. destruct brs2 as [|[n2 f2] [|]];
        [exfalso; inversion Hbrs| |exfalso; inversion Hbrs;
         match goal with H : Forall2 _ [] (_ :: _) |- _ => inversion H end].
      assert (n = n2 /\ RB f4 f2) as [-> Hf]
        by (inversion Hbrs as [|? ? ? ? [Heq Hf] Hnil]; subst; cbn in *; auto).
      destruct (IHev2 (substl (repeat tBox #|n2|) f2)) as (r2 & er2 & Hr2).
      { apply R_substl; [exact baseB_closed|apply R_repeat_box|exact Hf]. }
      exists r2. split; auto. eapply eval_iota_sing; eauto. now rewrite iiap_eq.
    - (* fix, guarded *)
      rewrite Hg in guarded. discriminate.
    - (* fix_value, guarded *)
      rewrite Hg in guarded. discriminate.
    - (* fix', unguarded *)
      apply RB_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw).
      destruct (IHev2 _ Ha) as (av2 & eav2 & Hav).
      apply RB_fix in Hw as (mf2 & -> & Hm).
      destruct (R_cunfold_fix _ baseB_closed _ _ _ _ _ Hm e0) as (fn2 & e2 & Hfn).
      destruct (IHev3 (tApp fn2 av2)) as (r2 & er2 & Hr2); [now apply R_app|].
      exists r2. split; auto. eapply eval_fix'; eauto.
    - (* cofix_case *)
      apply RB_case in Ht as (discr2 & brs2 & -> & Hd & Hbrs).
      destruct (IHev1 _ Hd) as (w & ew & Hw).
      apply RB_mkApps_cofix in Hw as (mf2 & args2 & -> & Hm & Hargs).
      destruct (R_cunfold_cofix _ baseB_closed _ _ _ _ _ Hm e0) as (fn2 & e2 & Hfn).
      destruct (IHev2 (tCase ip (mkApps fn2 args2) brs2)) as (r2 & er2 & Hr2).
      { apply R_case; auto. now apply R_mkApps. }
      exists r2. split; auto. eapply eval_cofix_case; eauto.
    - (* cofix_proj *)
      apply RB_proj in Ht as (discr2 & -> & Hd).
      destruct (IHev1 _ Hd) as (w & ew & Hw).
      apply RB_mkApps_cofix in Hw as (mf2 & args2 & -> & Hm & Hargs).
      destruct (R_cunfold_cofix _ baseB_closed _ _ _ _ _ Hm e0) as (fn2 & e2 & Hfn).
      destruct (IHev2 (tProj p (mkApps fn2 args2))) as (r2 & er2 & Hr2).
      { apply R_proj. now apply R_mkApps. }
      exists r2. split; auto. eapply eval_cofix_proj; eauto.
    - (* delta *)
      destruct (eq_dec c kn) as [->|ne].
      + assert (decl = {| cst_body := Some (nbody kn d) |}) as ->.
        { unfold declared_constant in isdecl, HΣ'. rewrite HΣ' in isdecl. now injection isdecl. }
        cbn in e. injection e as <-. apply eval_nbody_inv in ev as ->.
        apply RB_const in Ht as [-> | (_ & ->)].
        * exists (nfix d). split; [exact eval_kn|exact RB_base_nbody].
        * exists (nfix d). split; [exact eval_nfix|exact RB_base_nbody].
      + apply RB_const in Ht as [-> | (E & _)]; [|congruence].
        destruct (IHev body) as (r2 & er2 & Hr2); [apply R_refl|].
        exists r2. split; auto. eapply eval_delta; eauto.
        unfold declared_constant in *. now rewrite Hother.
    - (* proj *)
      apply RB_proj in Ht as (discr2 & -> & Hd).
      destruct (IHev1 _ Hd) as (w & ew & Hw). apply RB_mkApps_construct in Hw as (args2 & -> & Hargs).
      destruct (F2_nth_s _ _ _ _ _ Hargs e3) as (a2 & Ha2 & Ha).
      destruct (IHev2 _ Ha) as (r2 & er2 & Hr2).
      exists r2. split; auto. eapply eval_proj; eauto.
      + now rewrite cipd_eq.
      + now rewrite -(Forall2_length Hargs).
    - (* proj_block *)
      congruence.
    - (* proj_prop *)
      apply RB_proj in Ht as (discr2 & -> & Hd).
      destruct (IHev _ Hd) as (w & ew & Hw). apply RB_box in Hw as ->.
      exists tBox. split; [eapply eval_proj_prop; eauto; now rewrite iiap_eq|apply R_box].
    - (* construct *)
      apply RB_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw). apply RB_mkApps_construct in Hw as (args2 & -> & Hargs).
      destruct (IHev2 _ Ha) as (a2' & ea2 & Ha2).
      exists (tApp (mkApps (tConstruct ind c []) args2) a2'). split.
      + eapply eval_construct; eauto.
        * now rewrite lookup_constructor_eq.
        * now rewrite -(Forall2_length Hargs).
      + apply R_app; auto. apply R_mkApps; auto. apply R_construct. constructor.
    - (* construct_block *)
      congruence.
    - (* app_cong *)
      apply RB_app in Ht as (f2 & a2 & -> & Hf & Ha).
      destruct (IHev1 _ Hf) as (w & ew & Hw).
      destruct (IHev2 _ Ha) as (a2' & ea2 & Ha2).
      exists (tApp w a2'). split; [|now apply R_app].
      eapply eval_app_cong; eauto.
      rewrite Hg in i |- *. exact (RB_cond _ _ Hw (eval_not_const _ _ _ ev1) i).
    - (* prim *)
      destruct X.
      + assert (t2 = tPrim (prim_int i)) as -> by (inversion Ht; subst; [reflexivity|nobaseB]).
        exists (tPrim (prim_int i)). split; [constructor; constructor|exact (R_prim_int _ i)].
      + assert (t2 = tPrim (prim_float f)) as -> by (inversion Ht; subst; [reflexivity|nobaseB]).
        exists (tPrim (prim_float f)). split; [constructor; constructor|exact (R_prim_float _ f)].
      + assert (t2 = tPrim (prim_string s)) as -> by (inversion Ht; subst; [reflexivity|nobaseB]).
        exists (tPrim (prim_string s)). split; [constructor; constructor|exact (R_prim_string _ s)].
      + destruct t2; try (exfalso; inversion Ht; subst; nobaseB; fail).
        destruct prim as [tag m]. destruct m; try (exfalso; inversion Ht; subst; nobaseB; fail).
        destruct a1 as [df2 v2].
        assert (RB def df2 /\ Forall2 RB v v2) as [Hdf Hv] by (inversion Ht; subst; [auto|nobaseB]).
        destruct (s _ Hdf) as (df2' & edf2 & Hdf2).
        assert (∑ v2', All2_Set (eval Σ) v2 v2' × Forall2 RB v' v2') as (v2' & ev2 & Hv2).
        { clear -a Hv. induction ev in v2, Hv, a |- *.
          - destruct v2; [exists []; split; constructor|exfalso; inversion Hv].
          - destruct v2 as [|x2 v2]; [exfalso; inversion Hv|].
            assert (RB x x2 /\ Forall2 RB l v2) as [Hx Hl] by (inversion Hv; auto).
            destruct a as [IHx a].
            destruct (IHx _ Hx) as (y2 & ey2 & Hy).
            destruct (IHev a v2 Hl) as (v2' & ev2 & Hv2).
            exists (y2 :: v2'). split; constructor; auto. }
        exists (tPrim (prim_array {| array_default := df2'; array_value := v2' |})). split.
        * apply eval_prim. exact (evalPrimArray (eval Σ) v2 df2 v2' df2' ev2 edf2).
        * apply R_prim_array; auto.
    - (* force *)
      apply RB_force in Ht as (t3 & -> & Ht3).
      destruct (IHev1 _ Ht3) as (w & ew & Hw). apply RB_lazy in Hw as (t4 & -> & Ht4).
      destruct (IHev2 _ Ht4) as (r2 & er2 & Hr2).
      exists r2. split; auto. eapply eval_force; eauto.
    - (* atom *)
      destruct t; try (cbn in i; discriminate).
      + apply RB_box in Ht as ->. exists tBox. split; [now apply eval_atom|apply R_box].
      + apply RB_lambda in Ht as [(b2 & -> & Hb2) | (Hlb & ->)].
        * exists (tLambda na b2). split; [now apply eval_atom|now apply R_lambda].
        * exists (nfix d). split; [exact eval_nfix|]. rewrite Hlb. exact RB_base_nbody.
      + destruct args; [|cbn in i; discriminate].
        apply RB_construct in Ht as (l2 & -> & Hl). destruct l2; [|exfalso; inversion Hl].
        exists (tConstruct ind n []). split; [|apply R_construct; constructor].
        apply eval_atom. unfold atom in *. now rewrite lookup_constructor_eq.
      + apply RB_fix in Ht as (mf2 & -> & Hm).
        exists (tFix mf2 idx). split; [now apply eval_atom|now apply R_fix].
      + apply RB_cofix in Ht as (mf2 & -> & Hm). exists (tCoFix mf2 idx). split; [now apply eval_atom|now apply R_cofix].
      + apply RB_lazy in Ht as (t2' & -> & Ht2). exists (tLazy t2'). split; [now apply eval_atom|now apply R_lazy].
  Qed.

  (** ** The results *)

  Lemma baseF_not_fo t t' : baseF t t' -> ~ fo t.
  Proof. intros [-> _] H. inversion H. Qed.

  Lemma baseB_not_fo t t' : baseB t t' -> ~ fo t.
  Proof.
    intros [_ [-> | ->]] H; [inversion H|].
    pose proof nbody_lambda as Hl. destruct (nbody kn d); cbn in Hl; try discriminate. inversion H.
  Qed.

  (** [Hcore]: on first-order results, the fixpoint in [Σ] and its body with
      the recursive variable replaced by [tConst kn] in [Σ'] evaluate alike. *)
  Theorem fix_native_fo_equiv args v : fo v ->
    (eval Σ (mkApps (nfix d) args) v -> eval Σ' (mkApps (nbody kn d) args) v) *
    (eval Σ' (mkApps (nbody kn d) args) v -> eval Σ (mkApps (nfix d) args) v).
  Proof.
    intros Hv. split; intros ev.
    - destruct (forward _ _ ev (mkApps (nbody kn d) args)) as (v' & ev' & Hr).
      { apply R_mkApps; [exact RF_base_nbody|]. apply Forall2_R_refl. }
      rewrite (R_fo _ baseF_not_fo _ _ Hr Hv) in ev'. exact ev'.
    - destruct (backward _ _ ev (mkApps (nfix d) args)) as (v' & ev' & Hr).
      { apply R_mkApps; [exact RB_base_nbody|]. apply Forall2_R_refl. }
      rewrite (R_fo _ baseB_not_fo _ _ Hr Hv) in ev'. exact ev'.
  Qed.

  (** The head swaps: in [Σ] the constant evaluates as the fixpoint, in [Σ']
      as the body. *)
  Theorem swap_fix args v :
    (eval Σ (mkApps (tConst kn) args) v -> eval Σ (mkApps (nfix d) args) v) *
    (eval Σ (mkApps (nfix d) args) v -> eval Σ (mkApps (tConst kn) args) v).
  Proof.
    split; apply eval_mkApps_head'; intros X ev.
    - depelim ev.
      2: { cbn in i. discriminate. }
      unfold declared_constant in isdecl, HΣ. rewrite HΣ in isdecl.
      injection isdecl as <-. cbn in e. injection e as <-. apply eval_tFix_inv in ev as ->. exact eval_nfix.
    - apply eval_tFix_inv in ev. unfold nfix in ev |- *. rewrite ev. exact eval_kn.
  Qed.

  Theorem swap_body args v :
    (eval Σ' (mkApps (tConst kn) args) v -> eval Σ' (mkApps (nbody kn d) args) v) *
    (eval Σ' (mkApps (nbody kn d) args) v -> eval Σ' (mkApps (tConst kn) args) v).
  Proof.
    split; apply eval_mkApps_head'; intros X ev.
    - depelim ev.
      2: { cbn in i. discriminate. }
      unfold declared_constant in isdecl, HΣ'. rewrite HΣ' in isdecl.
      injection isdecl as <-. cbn in e. injection e as <-. apply eval_nbody_inv in ev as ->. exact eval_nbody.
    - apply eval_nbody_inv in ev as ->. exact eval_kn'.
  Qed.

  (** The constant [kn] gives the same first-order results in [Σ] and [Σ']. *)
  Theorem native_fo_obs_equiv args v : fo v ->
    (eval Σ (mkApps (tConst kn) args) v -> eval Σ' (mkApps (tConst kn) args) v) *
    (eval Σ' (mkApps (tConst kn) args) v -> eval Σ (mkApps (tConst kn) args) v).
  Proof.
    intros Hv. destruct (swap_fix args v) as [S1 S2]. destruct (swap_body args v) as [B1 B2].
    destruct (fix_native_fo_equiv args v Hv) as [C1 C2].
    split; intros H; [apply B2, C1, S1, H|apply S2, C2, B1, H].
  Qed.
End Forward.
