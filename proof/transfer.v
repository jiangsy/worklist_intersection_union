Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.

Require Import algo.ott.
Require Import algo.notations.
Require Import decl.ott.
Require Import decl.notations.
Require Import decl.properties.
Require Import decl.ln_inf_extra.
Require Import ln_utils.


Inductive ss_entry := 
  | sse_tv 
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
  | wf_ss_ev : forall ex t Θ
    , wf_ss Θ -> ex `notin` dom Θ ->
     ld_wf_mtype (ss_to_ctx Θ) t -> 
     wf_ss (Θ; ex : t)
.

Lemma wf_uniq : forall Θ,
    wf_ss Θ -> uniq Θ.
Proof.
  induction 1; eauto.
Qed.


Reserved Notation "θ ⫦ t ⇝ t'"
  (at level 65, t at next level, no associativity).
Inductive inst_type : subst_set -> la_type -> ld_type -> Prop := 
  | inst_t_tvar : forall θ x, 
      wf_ss θ -> 
      θ ⫦ (la_t_tvar_f x) ⇝ (ld_t_var_f x)
  | inst_t_evar : forall θ x t, 
      wf_ss θ -> 
      x : t ∈ θ -> 
      θ ⫦ (la_t_evar x) ⇝ t
  | inst_t_int : forall θ, 
      wf_ss θ -> 
      θ ⫦ la_t_int ⇝ ld_t_int
  | inst_t_arrow : forall θ A' B' A B, 
      θ ⫦ A' ⇝ A -> θ ⫦ B' ⇝ B ->
      θ ⫦ (la_t_arrow A' B') ⇝ (ld_t_arrow A B)
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


Inductive inst_ev : subst_set -> var -> la_typelist -> la_typelist -> Prop :=
  | inst_ev_nil : forall θ x, inst_ev θ x la_tl_nil la_tl_nil
  | inst_ev_lbs : forall θ x lb lbs ubs lb' t', 
      inst_ev θ x lbs ubs -> 
      inst_type θ lb lb' -> 
      inst_type θ (la_t_evar x) t' -> 
      ld_sub (ss_to_ctx θ) lb' t' -> 
      inst_ev θ x (la_tl_cons lbs lb) ubs
  | inst_ev_ubs : forall θ x lbs ub ubs ub' t', 
      inst_ev θ x lbs ubs -> 
      inst_type θ ub ub' -> 
      inst_type θ (la_t_evar x) t' -> 
      ld_sub (ss_to_ctx θ) t' ub' -> 
      inst_ev θ x lbs (la_tl_cons ubs ub) 
.


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
      θ ⫦ (la_wl_cons_tv Γᵃ x) ⇝ (ld_wl_cons_tv Γᵈ x) ⫣ θ'
  | inst_wl_ev : forall θ θ' tᵈ lbs ex ubs Γᵃ Γᵈ, 
      θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ' -> 
      ld_mono_type tᵈ -> 
      ex `notin` dom θ' -> 
      inst_ev (θ' ; ex : tᵈ) ex lbs ubs -> 
      θ ⫦ (la_wl_cons_ev Γᵃ lbs ex ubs) ⇝ Γᵈ ⫣ (θ' ; ex : tᵈ)
where "θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ'" := (inst_worklist θ Γᵃ Γᵈ θ').


Hint Constructors inst_type : transfer.
Hint Constructors inst_ev : transfer.
Hint Constructors inst_worklist : transfer.

Lemma notin_ss_notin_inst : forall x ex Θ A,
    ex : A ∈ Θ → x `notin` fv_ss Θ → x `notin` fv_ld_type A.
Proof.
  induction Θ; intros.
  - inversion H.
  - destruct a. destruct H.
    + inversion H; subst; simpl in *; auto. admit.
    + simpl in H0; eauto.
Admitted.


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
        subst. apply ld_wf_mtype_is_mtype in H7.
        now apply ld_mono_is_ld_lc.
      * inversion H. apply IHθ; auto. auto.
  - split; inst_cofinites_by L.
    + apply lc_la_t_forall_exists with (x1:=x). intuition.
    + apply lc_ld_t_forall_exists with (x1:=x). intuition.
Qed.

(* consult Alvin *)
Lemma inst_A_wf_A: forall θ Aᵃ Aᵈ, 
  θ ⫦ Aᵃ ⇝ Aᵈ -> ss_to_ctx θ ⊢ Aᵈ.
Proof.
  intros.
  dependent induction H.
Admitted.

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
  -> θ ⫦ [`′ x' /ᵃ x] Aᵃ ⇝ [` x' /ᵈ x] Aᵈ.
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
  forall A'ᵈ, θ ⫦ subst_la_type tᵃ x Aᵃ ⇝ A'ᵈ
    -> exists Aᵈ, [tᵈ /ᵈ x] Aᵈ = A'ᵈ /\ θ ⫦ Aᵃ ⇝ Aᵈ.
Proof with auto with transfer.
  intros * Hlc Hfv Hinstt.
  induction Hlc; intros * HinstA; simpl in *.
  - inversion HinstA. exists ld_t_int. simpl. split; auto...
  - specialize (inst_t_lc _ _ _ Hinstt). intros.
    dependent destruction HinstA.
    inst_cofinites_by (L `union` singleton x `union` fv_ld_type tᵈ `union`  fv_ld_type A `union` dom θ `union` fx_la_type t). 
    replace (`′ x0) with ([tᵃ /ᵃ x] `′ x0) in H1 by (apply subst_la_type_fresh_eq; auto).
    rewrite <- subst_la_type_open_la_type_wrt_la_type in H1.
    specialize (H0 _ _ H1).
    destruct H0 as [A'ᵈ HinstA'ᵈ].
    exists (ld_t_forall (close_ld_type_wrt_ld_type x0 A'ᵈ)). simpl.
    rewrite subst_ld_type_close_ld_type_wrt_ld_type. 
    + split.
      * f_equal. destruct_conjs. apply ld_type_open_r_close_l; auto. 
      * eapply inst_t_forall with (L:=L); intros.
        rewrite (subst_la_type_intro x0) by auto.
        rewrite (subst_ld_type_intro x0) by (apply close_ld_type_notin).
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


Lemma inst_e_rev_subst : forall A'ᵈ θ tᵃ tᵈ x Aᵃ,
  lc_la_type Aᵃ ->
  x `notin` (fx_la_type tᵃ `union` fv_ss θ) -> 
  θ ⫦ tᵃ ⇝ tᵈ → θ ⫦ [tᵃ /ᵃ x] Aᵃ ⇝ A'ᵈ ->
  exists Aᵈ, [tᵈ /ᵈ x] Aᵈ = A'ᵈ ∧ θ ⫦ Aᵃ ⇝ Aᵈ.
Proof.
  intros.  
  specialize (inst_e_rev_subst' _ _ _ _  _ H H0 H1 A'ᵈ).
  intros.
  specialize (H3 H2).
  auto.
Qed.

Definition transfer (Γ : la_worklist) (Γ' : ld_worklist) : Prop :=
  exists θ', inst_worklist nil Γ Γ' θ'.