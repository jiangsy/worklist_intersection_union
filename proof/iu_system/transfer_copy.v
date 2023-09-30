(* Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.

Require Import algo.ott.
Require Import algo.notations.
Require Import algo.ln_inf_extra.
Require Import decl.ott.
Require Import decl.notations.
Require Import decl.properties.
Require Import decl.ln_inf_extra.
Require Import ln_utils.


Inductive ss_entry := 
  | sse_tv 
  | sse_tvar
  | sse_ev (t : ld_type).

Definition subst_set := list (var * ss_entry).

Declare Scope subst_set_scope.
Delimit Scope subst_set_scope with subst.
Bind Scope subst_set_scope with subst_set.

Notation "s1 ;; s2" := (app s2 s1)
  (at level 58, left associativity) : subst_set_scope.

Notation "s ; ex : t" := (cons (pair ex (sse_ev t)) s)
  (at level 58, ex at next level, t at next level, left associativity) : type_scope.

Notation "s ; x" := (cons (pair x sse_tv) s)
  (at level 58, x at next level, left associativity) : type_scope.

Notation "x : t ∈ s" := (binds x (sse_ev t) s)
  (at level 58, t at next level, no associativity) : type_scope.


Fixpoint fv_ss (θ : subst_set) : atoms :=
  match θ with
  | nil => {}
  | θ' ; ex : t => fv_ss θ' `union` singleton ex
  | θ' ; x => fv_ss θ' `union` singleton x
  end.

Fixpoint ss_to_ctx (θ : subst_set) : ld_context := 
  match θ with 
  | nil => ld_ctx_nil
  | θ' ; x => ld_ctx_cons (ss_to_ctx θ') x
  | θ' ; ex : t => ss_to_ctx θ'
  end.

Inductive wf_ss : subst_set -> Prop :=
  | wf_ss_nil : wf_ss nil
  | wf_ss_tv : forall x θ,
      wf_ss θ -> x `notin` dom θ ->
      wf_ss (θ; x)
  | wf_ss_ev : forall ex t Θ, 
     wf_ss Θ -> 
     ex `notin` dom Θ ->
     ld_wf_type (ss_to_ctx Θ) t -> 
     ld_mono_type t ->
     wf_ss (Θ; ex : t)
.

Lemma wf_uniq : forall Θ,
    wf_ss Θ -> uniq Θ.
Proof.
  induction 1; eauto.
Qed.


Lemma wf_mono : forall θ x t, 
  wf_ss θ -> x : t ∈ θ -> ld_mono_type t.
Proof.
  intros.
  induction H.
  - inversion H0.
  - inversion H0.
    inversion H2.
    auto.
  - inversion H0.
    + dependent destruction H4. auto.
    + auto.
Qed.

Reserved Notation "θ ⫦ t ⇝ t'"
  (at level 65, t at next level, no associativity).
Inductive inst_type : subst_set -> la_type -> ld_type -> Prop := 
  | inst_t_tvar : forall θ x, 
      wf_ss θ -> 
      θ ⫦ (la_t_tvar_f x) ⇝ (ld_t_var_f x)
  | inst_t_evar : forall θ x tᵈ, 
      wf_ss θ -> 
      x : tᵈ ∈ θ -> 
      θ ⫦ (la_t_evar x) ⇝ tᵈ
  | inst_t_int : forall θ, 
      wf_ss θ -> 
      θ ⫦ la_t_int ⇝ ld_t_int
  | inst_t_arrow : forall θ Aᵃ Bᵃ Aᵈ Bᵈ, 
      θ ⫦ Aᵃ ⇝ Aᵈ -> 
      θ ⫦ Bᵃ ⇝ Bᵈ ->
      θ ⫦ (la_t_arrow Aᵃ Bᵃ) ⇝ (ld_t_arrow Aᵈ Bᵈ)
  | inst_t_intersection : forall θ Aᵃ Bᵃ Aᵈ Bᵈ,
      θ ⫦ Aᵃ ⇝ Aᵈ -> 
      θ ⫦ Bᵃ ⇝ Bᵈ ->
      θ ⫦ (la_t_intersection Aᵃ Bᵃ) ⇝ (ld_t_intersection Aᵈ Bᵈ)
  | inst_t_union : forall θ Aᵃ Bᵃ Aᵈ Bᵈ,
      θ ⫦ Aᵃ ⇝ Aᵈ -> 
      θ ⫦ Bᵃ ⇝ Bᵈ ->
      θ ⫦ (la_t_union Aᵃ Bᵃ) ⇝ (ld_t_union Aᵈ Bᵈ)
  | inst_t_forall : forall θ L A' A,
      (forall x, x `notin` L -> 
        θ ⫦ (open_la_type_wrt_la_type A' (la_t_tvar_f x)) ⇝ (open_ld_type_wrt_ld_type A (ld_t_var_f x))) ->
      θ ⫦ (la_t_forall A') ⇝ (ld_t_forall A)
where "θ ⫦ t ⇝ t'" := (inst_type θ t t').

Lemma inst_t_wf_ss : forall θ t t',
  θ ⫦ t ⇝ t' -> wf_ss θ.
Proof.
  induction 1; pick fresh x'; eauto.
Qed.


Reserved Notation "θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ'"
  (at level 65, Γᵃ at next level, Γᵈ at next level, no associativity).
Inductive inst_worklist : subst_set -> la_worklist -> ld_worklist -> subst_set -> Prop := 
  | inst_wl_nil : forall θ, 
      wf_ss θ -> 
      θ ⫦ la_wl_nil ⇝ ld_wl_nil ⫣ θ
  | inst_wl_sub : forall θ θ' Γᵃ t1ᵃ t2ᵃ Γᵈ t1ᵈ t2ᵈ, 
      θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ' -> 
      θ' ⫦ t1ᵃ ⇝ t1ᵈ -> 
      θ' ⫦ t2ᵃ ⇝ t2ᵈ -> 
      θ ⫦ (la_wl_cons_w Γᵃ (la_w_sub t1ᵃ t2ᵃ)) ⇝ (ld_wl_cons_w Γᵈ (ld_w_sub t1ᵈ t2ᵈ)) ⫣ θ'
  | inst_wl_tv : forall θ θ' x Γᵃ Γᵈ, 
      θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ' -> 
      θ ⫦ (la_wl_cons_tv Γᵃ x) ⇝ (ld_wl_cons_tv Γᵈ x) ⫣ (θ'; x)
  | inst_wl_ev : forall θ θ' ex lbᵃ ubᵃ lbᵈ ubᵈ Γᵃ Γᵈ, 
      θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ' -> 
      θ ⫦ lbᵃ ⇝ lbᵈ ->
      θ ⫦ ubᵃ ⇝ ubᵈ ->
      θ ⫦ (la_wl_cons_ev Γᵃ lbᵃ ex ubᵃ) ⇝ (ld_wl_cons_w Γᵈ (ld_w_sub lbᵈ ubᵈ)) ⫣ (θ' ; ex : lbᵈ)
where "θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ'" := (inst_worklist θ Γᵃ Γᵈ θ').


Hint Constructors inst_type : transfer.
Hint Constructors inst_worklist : transfer.


Lemma fv_ss_ld_ctx_dom: forall θ x,
  x `notin` fv_ss θ -> x `notin` ld_ctx_dom (ss_to_ctx θ).
Proof.
  induction θ; simpl; intros; auto.
  - destruct a; destruct s.
    + simpl in *. auto.
    + auto.
Qed.


Lemma notin_wf_t_notin_ss: forall t θ x,
  ss_to_ctx θ ⊢ t -> x `notin` fv_ss θ -> x `notin` fv_ld_type t.
Proof.
  induction t; intros.
  - auto.
  - simpl. dependent destruction H.
    inst_cofinites_by (L `union` singleton x).
    eapply ld_wf_type_fv with (x:=x) in H.
    rewrite fv_ld_type_open_ld_type_wrt_ld_type_lower.
    eauto. simpl. auto.
    apply notin_add; auto.
    apply fv_ss_ld_ctx_dom. auto.
  - simpl. dependent destruction H; apply notin_union; eauto.
  - simpl. dependent destruction H; apply notin_union; eauto.
  - simpl. dependent destruction H; apply notin_union; eauto.
  - auto.
  - dependent destruction H; auto.
    clear H.
    induction θ; auto.
    + inversion H0.
    + destruct a. destruct s; simpl in *.
      inversion H0; subst; auto.
      auto.
Qed.

Lemma notin_ss_notin_inst : forall θ x ex t,
    wf_ss θ ->
    ex : t ∈ θ -> 
    x `notin` fv_ss θ ->
    x `notin` fv_ld_type t.
Proof.
  intro θ.
  induction θ; intros.
  - inversion H0.
  - inversion H0. destruct a; destruct s.
    + inversion H2.
    + inversion H2. subst. inversion H. subst. 
      simpl in H1. eapply notin_wf_t_notin_ss; eauto.
    + eapply IHθ; eauto. inversion H; auto.
      destruct a; destruct s; simpl in *. auto. auto.
Qed.

Lemma inst_t_lc : forall θ Aᵃ Aᵈ, 
  θ ⫦ Aᵃ ⇝ Aᵈ -> 
  lc_la_type Aᵃ /\ lc_ld_type Aᵈ.
Proof.
  intros.
  induction H; try (split; destruct_conjs; auto; fail).
  - split. auto. 
    induction θ.
    + inversion H0.
    + destruct a. inversion H0.
      * inversion H1. subst. inversion H.
        subst. now apply ld_mono_is_ld_lc.
      * inversion H. apply IHθ; auto. auto.
  - split; inst_cofinites_by L.
    + apply lc_la_t_forall_exists with (x1:=x). intuition.
    + apply lc_ld_t_forall_exists with (x1:=x). intuition.
Qed.


Ltac inversion_eq :=
  repeat
    match goal with 
        | H : ?a = ?b |-  _ => dependent destruction H
      end.

Lemma inst_A_det : forall θ Aᵃ A₁ᵈ,
  uniq θ -> 
  θ ⫦ Aᵃ ⇝ A₁ᵈ -> 
  forall A₂ᵈ, θ ⫦ Aᵃ ⇝ A₂ᵈ -> 
    A₁ᵈ = A₂ᵈ.
Proof.
  induction 2; (intros e₂ᵈ H2; dependent destruction H2; auto). 
  - specialize (binds_unique _ _ _ _ _ H1 H3).
    intros. specialize (H4 H). inversion_eq. auto.
  - specialize (IHinst_type1 H _ H2_).
    specialize (IHinst_type2 H _ H2_0).
    subst. auto.
  - inst_cofinites_by (L `union` L0 `union` (fv_ld_type A) `union` (fv_ld_type A0)).  
    assert (A = A0).
    + eapply open_ld_type_wrt_ld_type_inj with (x1:=x); auto.
    + subst. auto. 
Qed.


Lemma not_in_dom_not_in_fv_ss: forall x θ,
  x `notin` dom θ -> 
  x `notin` fv_ss θ.
Proof.
  induction θ; auto.
  destruct a. destruct s; simpl; 
  intros; apply notin_union; auto.
Qed.


Lemma inst_e_rename : forall θ Aᵃ Aᵈ x x'
  , θ ⫦ Aᵃ ⇝ Aᵈ 
  -> x `notin` dom θ
  -> θ ⫦ [`ᵃ x' /ᵃ x] Aᵃ ⇝ [`ᵈ x' /ᵗ x] Aᵈ.
Proof with auto with transfer.
  intros. induction H; simpl; auto...
  - unfold eq_dec. destruct (EqDec_eq_of_X x0 x); auto...
  - rewrite subst_ld_type_fresh_eq. auto...
    eapply notin_ss_notin_inst; eauto.
    now apply not_in_dom_not_in_fv_ss. 
  - eapply inst_t_forall with (L := L `union` singleton x). intros.
    rewrite_la_subst_open_var. rewrite_ld_subst_open_var. auto.
Qed.


Lemma inst_e_rev_subst' : forall tᵃ tᵈ x θ Aᵃ,
  lc_la_type Aᵃ -> 
  x `notin` (fx_la_type tᵃ `union` fv_ss θ) -> 
  θ ⫦ tᵃ ⇝ tᵈ -> 
  forall A'ᵈ, θ ⫦ [tᵃ /ᵃ x] Aᵃ ⇝ A'ᵈ
    -> exists Aᵈ, [tᵈ /ᵗ x] Aᵈ = A'ᵈ /\ θ ⫦ Aᵃ ⇝ Aᵈ.
Proof with auto with transfer.
  intros * Hlc Hfv Hinstt.
  induction Hlc; intros * HinstA; simpl in *.
  - inversion HinstA. exists ld_t_int. simpl. split; auto...
  - specialize (inst_t_lc _ _ _ Hinstt). intros.
    dependent destruction HinstA.
    inst_cofinites_by (L `union` singleton x `union` fv_ld_type tᵈ `union`  fv_ld_type A `union` dom θ `union` fx_la_type t). 
    replace (`ᵃ x0) with ([tᵃ /ᵃ x] (`ᵃ x0)) in H1 by (apply subst_la_type_fresh_eq; auto).
    rewrite <- subst_la_type_open_la_type_wrt_la_type in H1.
    specialize (H0 _ _ H1).
    destruct H0 as [A'ᵈ HinstA'ᵈ].
    exists (ld_t_forall (close_ld_type_wrt_ld_type x0 A'ᵈ)). simpl.
    rewrite subst_ld_type_close_ld_type_wrt_ld_type. 
    + split.
      * f_equal. destruct_conjs. apply ld_type_open_r_close_l; auto. 
      * eapply inst_t_forall with (L:=L); intros.
        rewrite (subst_la_type_intro x0) by auto.
        rewrite (subst_ld_type_intro x0) by (apply close_dtyp_notin).
        apply inst_e_rename; auto.
        rewrite open_ld_type_wrt_ld_type_close_ld_type_wrt_ld_type. intuition.
    + intuition. 
    + auto.
    + auto.
    + intuition.
  - dependent destruction HinstA.
    specialize (IHHlc1 _ HinstA1). destruct IHHlc1 as [t₁ᵈ HinstA1inv].
    specialize (IHHlc2 _ HinstA2). destruct IHHlc2 as [t₂ᵈ HinstA2inv].
    exists (ld_t_arrow t₁ᵈ t₂ᵈ). destruct_conjs. split; simpl; subst; auto...
  - exists (ld_t_var_f x5).
    destruct (x5 == x).  
    + subst. simpl. destruct (x == x).
      * split.
        -- assert (uniq θ) as Huniq by (apply wf_uniq; eapply inst_t_wf_ss; eauto).
           specialize (inst_A_det _ _ _ Huniq Hinstt). intros.
           specialize (H _ HinstA). auto.
        -- constructor. eapply inst_t_wf_ss. eauto.
      * contradiction.
    + simpl. unfold eq_dec. destruct (EqDec_eq_of_X x5 x).
      * contradiction.
      * inversion HinstA; split; auto... 
  - simpl in *. exists A'ᵈ. split.
    + rewrite subst_ld_type_fresh_eq. auto.
      inversion HinstA.
      eapply notin_ss_notin_inst; eauto.
    + auto.
Qed.

Lemma inst_wf : forall θ tᵃ tᵈ,
  θ ⫦ tᵃ ⇝ tᵈ -> wf_ss θ.
Proof.
  intros. induction H; auto.
  - inst_cofinites_by L. auto.
Qed.

Lemma inst_e_rev_subst : forall A'ᵈ θ tᵃ tᵈ x Aᵃ,
  lc_la_type Aᵃ ->
  x `notin` (fx_la_type tᵃ `union` fv_ss θ) -> 
  θ ⫦ tᵃ ⇝ tᵈ → θ ⫦ [tᵃ /ᵃ x] Aᵃ ⇝ A'ᵈ ->
  exists Aᵈ, [tᵈ /ᵗ x] Aᵈ = A'ᵈ ∧ θ ⫦ Aᵃ ⇝ Aᵈ.
Proof.
  intros.  
  specialize (inst_e_rev_subst' _ _ _ _  _ H H0 H1 A'ᵈ).
  intros.
  specialize (H3 H2).
  auto.
Qed.

Fixpoint ld_type_to_la_type (Aᵈ : ld_type) : la_type :=
  match Aᵈ with 
  | ld_t_int => la_t_int
  | ld_t_forall A'ᵈ => la_t_forall (ld_type_to_la_type A'ᵈ)
  | ld_t_arrow A₁ᵈ A₂ᵈ => la_t_arrow (ld_type_to_la_type A₁ᵈ) (ld_type_to_la_type A₂ᵈ)
  | ld_t_var_b n => la_t_tvar_b n
  | ld_t_var_f x => la_t_tvar_f x
  end.

Lemma ld_type_to_la_type_open_open_expr_wrt_expr_distr_rec : forall e1 e2 n,
ld_type_to_la_type (open_ld_type_wrt_ld_type_rec n e2 e1) = open_la_type_wrt_la_type_rec n (ld_type_to_la_type e2) (ld_type_to_la_type e1).
Proof.
  intros e1.
  induction e1; simpl; intros; auto.
  - rewrite IHe1. auto.
  - rewrite IHe1_1. rewrite IHe1_2. auto.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; simpl. auto.
      auto.
    + simpl. auto.
Qed.

Lemma ld_type_to_la_type_open_open_expr_wrt_expr_distr : forall e1 e2,
  ld_type_to_la_type (open_ld_type_wrt_ld_type e1 e2) = open_la_type_wrt_la_type
  (ld_type_to_la_type e1)(ld_type_to_la_type e2) .
Proof.
  intros.
  unfold open_la_type_wrt_la_type.
  unfold open_ld_type_wrt_ld_type.
  rewrite ld_type_to_la_type_open_open_expr_wrt_expr_distr_rec.
  auto.
Qed.

Lemma inst_ld_type_to_la_type: forall θ Aᵈ,
  lc_ld_type Aᵈ ->
  wf_ss θ ->
  θ ⫦ ld_type_to_la_type Aᵈ ⇝ Aᵈ.
Proof.
  intros * Hlc.
  induction Hlc; simpl; try (constructor; auto; fail).
  - intros.
    eapply inst_t_forall with (L:=empty).
    intros.
    specialize (H0 x H1).
    rewrite ld_type_to_la_type_open_open_expr_wrt_expr_distr in H0.
    simpl in *.
    eauto.
Qed.


Lemma ld_type_to_la_type_open_rec_distr: forall t1ᵈ t2ᵈ n, 
  ld_type_to_la_type (open_ld_type_wrt_ld_type_rec n t2ᵈ t1ᵈ) = open_la_type_wrt_la_type_rec n (ld_type_to_la_type t2ᵈ) (ld_type_to_la_type t1ᵈ).
Proof.
  intro t1ᵈ; induction t1ᵈ; intros; auto.
  - simpl. rewrite IHt1ᵈ.
    auto.
  - simpl. rewrite IHt1ᵈ1. rewrite IHt1ᵈ2. auto.
  - simpl. destruct (lt_eq_lt_dec n n0); simpl; auto.
    + destruct s; auto.
Qed.


Lemma ld_type_to_la_type_open_distr: forall t1ᵈ t2ᵈ , 
  ld_type_to_la_type (open_ld_type_wrt_ld_type t1ᵈ t2ᵈ ) = open_la_type_wrt_la_type (ld_type_to_la_type t1ᵈ) (ld_type_to_la_type t2ᵈ).
Proof.
  intros. unfold open_ld_type_wrt_ld_type. unfold open_la_type_wrt_la_type.
  rewrite ld_type_to_la_type_open_rec_distr. auto.
Qed.

Lemma ld_type_to_la_type_open_var_distr: forall t1ᵈ x , 
  ld_type_to_la_type (t1ᵈ ^ᵈ x) = (ld_type_to_la_type t1ᵈ) ^ᵃ x.
Proof.
  intros. 
  replace (`ᵃ x) with (ld_type_to_la_type (`ᵈ x)) by auto.
  rewrite ld_type_to_la_type_open_distr.
  auto.
Qed.


Lemma ld_type_to_la_type_keeps_lc: forall tᵈ,
  lc_ld_type tᵈ -> lc_la_type (ld_type_to_la_type tᵈ).
Proof.
  intros. induction H; simpl; auto.
  - econstructor. intros. simpl in *. simpl.
    rewrite <- ld_type_to_la_type_open_var_distr.
    auto.
Qed.

Lemma inst_subst : forall θ x tᵈ Aᵃ Aᵈ, 
  lc_la_type Aᵃ ->
  x `notin` (fx_la_type Aᵃ)->
  (θ; x : tᵈ) ⫦ Aᵃ ⇝ Aᵈ -> 
  θ ⫦ [ld_type_to_la_type tᵈ /^ᵃ x] Aᵃ ⇝ Aᵈ.
Proof.
  intros * Hlc Hfv Hinstopen.
  generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros.
  - inversion Hinstopen. econstructor.
    inversion H. auto.
  - dependent destruction Hinstopen.
    eapply inst_t_forall with (L:=singleton x `union` fx_la_type t `union` fex_la_type t `union` L). intros.
    + intros.
      rewrite la_type_ex_subst_open_comm.
      * eapply H0.
        apply fx_la_type_open_la_type_notin; auto.
        auto.
      * inst_cofinites_with x0.
        apply inst_wf in H1.
        inversion H1.
        apply ld_type_to_la_type_keeps_lc. apply ld_mono_is_ld_lc. auto.
      * auto.
  - dependent destruction Hinstopen.
    econstructor; auto.
  - destruct (x5 == x).
    + subst.
      apply notin_singleton_1 in Hfv. 
      contradiction.
    + dependent destruction Hinstopen.
      constructor. inversion H. auto. 
  - dependent destruction Hinstopen. 
    destruct (ex5 == x). 
    + subst.
      apply binds_unique with (a:=sse_ev tᵈ) in H0. inversion H0. subst. inversion H.
      * apply inst_ld_type_to_la_type; auto. 
        apply ld_mono_is_ld_lc. auto.
      * constructor; auto.
      * apply wf_uniq. auto.
    + inversion H0. 
      * dependent destruction H1.
        contradiction.
      * econstructor; auto.      
        dependent destruction H. auto.
Qed.


(* Lemma transfer_reorder: forall Γᵃ Γ'ᵈ θ' x t m Γ'ᵃ,
  reorder Γᵃ x t m la_wl_nil Γ'ᵃ ->
  inst_worklist nil Γ'ᵃ Γ'ᵈ θ' ->
  exists Γᵈ θ, inst_worklist nil Γᵃ Γᵈ θ.
Proof.
  intros. 
  generalize dependent θ'.
  generalize dependent Γ'ᵈ.
  induction H; intros.
  - admit.
  - admit.
  - dependent destruction H1.
    specialize (IHreorder Γᵈ θ' H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].  
    exists (ld_wl_cons_tv Γ'ᵈ y), θ''.
    constructor. auto.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ].
    exists Γ'ᵈ.
    econstructor; auto. admit.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ].
    exists Γ'ᵈ.
    econstructor; eauto. admit.
  - dependent destruction H0.
    admit.
Admitted.

Lemma transfer_reorder': forall Γᵃ Γᵈ θ x t m Γ'ᵃ,
  reorder Γᵃ x t m la_wl_nil Γ'ᵃ ->
  inst_worklist nil Γᵃ Γᵈ θ -> 
  exists Γ'ᵈ θ', inst_worklist nil Γ'ᵃ Γ'ᵈ θ'.
Proof.
  intros. 
  generalize dependent θ.
  generalize dependent Γᵈ.
  induction H; intros.
  - exists Γᵈ, θ. admit.
  - admit.
  - dependent destruction H1.
    specialize (IHreorder Γᵈ θ' H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].  
    exists (ld_wl_cons_tv Γ'ᵈ y), θ''.
    econstructor. auto.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].
    exists Γ'ᵈ, (θ''; y : tᵈ).
    econstructor; auto.
    + admit.
    + admit.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].
    exists Γ'ᵈ, (θ''; y : tᵈ).
    econstructor; eauto.
    + admit.
    + admit.
  - dependent destruction H0.
Admitted. *)


Definition transfer (Γ : la_worklist) (Γ' : ld_worklist) : Prop :=
  exists θ', inst_worklist nil Γ Γ' θ'. *)