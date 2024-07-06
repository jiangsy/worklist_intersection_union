Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_rename.
Require Import uni.decl.prop_subtyping.
Require Import uni.ltac_utils.

Hint Constructors d_wf_typ: core.
Hint Constructors d_wf_env: core.

Inductive d_subtenv : denv -> denv -> Prop :=
  | d_subtenv__empty: d_subtenv nil nil
  | d_subtenv__tvar : forall Ψ Ψ' X,
      d_subtenv Ψ' Ψ ->
      d_subtenv (X ~ dbind_tvar_empty  ++  Ψ')
          (X ~ dbind_tvar_empty  ++  Ψ)
  | d_subtenv__var : forall Ψ Ψ' x A A',
      d_subtenv Ψ' Ψ ->
      d_sub Ψ A A' ->
      d_subtenv (x ~ dbind_typ A ++ Ψ')
          (x ~ dbind_typ A' ++ Ψ).

Inductive d_subenv : denv -> denv -> Prop :=
  | d_subenv__empty: d_subenv nil nil
  | d_subenv__tvar : forall Ψ Ψ' X,
      d_subenv Ψ' Ψ ->
      d_subenv (X ~ dbind_tvar_empty  ++  Ψ')
          (X ~ dbind_tvar_empty  ++  Ψ)
  | d_subenv__stvar : forall Ψ Ψ' X,
    d_subenv Ψ' Ψ ->
    d_subenv (X ~ dbind_stvar_empty  ++  Ψ')
        (X ~ dbind_stvar_empty  ++  Ψ)
  | d_subenv__var : forall Ψ Ψ' x A A',
      d_subenv Ψ' Ψ ->
      d_sub Ψ A A' ->
      d_subenv (x ~ dbind_typ A ++ Ψ')
          (x ~ dbind_typ A' ++ Ψ).

#[local] Hint Constructors d_subtenv d_subenv: core.

Lemma d_wf_tenv_d_wf_env : forall Ψ,
  ⊢ᵈₜ Ψ -> ⊢ᵈ Ψ.
Proof.
  intros. induction H; auto.
Qed.

Lemma d_subenv_refl: forall Ψ,
  ⊢ᵈₜ Ψ -> d_subtenv Ψ Ψ.
Proof with auto.
  intros. induction H; auto...
  econstructor; auto.
  apply d_sub_refl; auto. 
Qed.

Lemma d_subtenv_same_dom : forall Ψ Ψ',
  d_subtenv Ψ' Ψ ->
  dom Ψ = dom Ψ'.
Proof.
  intros. induction H; simpl; auto; rewrite IHd_subtenv; auto.
Qed.

Lemma d_subenv_same_dom : forall Ψ Ψ',
  d_subenv Ψ' Ψ ->
  dom Ψ = dom Ψ'.
Proof.
  intros. induction H; simpl; auto; rewrite IHd_subenv; auto.
Qed.

Lemma d_subtenv_same_tvar : forall Ψ Ψ' X,
  d_subtenv Ψ' Ψ ->
  X ~ □ ∈ᵈ Ψ ->
  X ~ □ ∈ᵈ Ψ'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.

Lemma d_subenv_same_dtvar : forall Ψ Ψ' X b,
  b = □ \/ b = ■ ->
  d_subenv Ψ' Ψ ->
  binds X b Ψ ->
  binds X b Ψ'.
Proof.
  intros. induction H0; simpl; intros; auto.
  - inversion H1; auto.
    + inversion H2; auto.
  - inversion H1; auto.
    + inversion H2; auto.   
  - inversion H1. 
    + dependent destruction H3. inversion H; inversion H3.
    + auto.
Qed.

Lemma d_subtenv_same_var : forall Ψ Ψ' A x,
  ⊢ᵈ Ψ ->
  d_subtenv Ψ' Ψ ->
  x ~ A ∈ᵈ Ψ ->
  exists A', x ~ A' ∈ᵈ Ψ' /\ Ψ ⊢ A' <: A.
Proof.
  intros. induction H0; simpl; intros; auto.
  - inversion H1; auto.
  - inversion H1; auto.
    + inversion H2.
    + apply d_wf_env_strengthen_app in H as Hwfe. 
      specialize (IHd_subtenv Hwfe H2).
      destruct IHd_subtenv as [A'].
      exists A'; intuition.
      eapply d_sub_weaken_cons; eauto.
  - inversion H1; auto.
    + dependent destruction H3.
      exists A0; intuition.
      eapply d_sub_weaken_cons; eauto.
    + apply d_wf_env_strengthen_app in H as Hwfe.  
      specialize (IHd_subtenv Hwfe H3).
      destruct IHd_subtenv as [A''].
      exists A''; intuition.
      eapply d_sub_weaken_cons; eauto.
Qed.

Lemma d_subtenv_stvar_false : forall Ψ Ψ' X,
  d_subtenv Ψ' Ψ ->
  X ~ ■ ∈ᵈ Ψ -> 
  False.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.

Lemma d_subtenv_wf_typ : forall Ψ Ψ' A,
  Ψ ᵗ⊢ᵈ A -> 
  d_subtenv Ψ' Ψ -> 
  Ψ' ᵗ⊢ᵈ A.
Proof.
  intros * H. generalize dependent Ψ'. induction H; intros; auto.
  - econstructor.
    eapply d_subtenv_same_tvar; eauto.
  - exfalso. eapply d_subtenv_stvar_false; eauto.
  - eapply d_wf_typ__all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed.

Lemma d_subenv_wf_typ : forall Ψ Ψ' A,
  Ψ ᵗ⊢ᵈ A -> 
  d_subenv Ψ' Ψ -> 
  Ψ' ᵗ⊢ᵈ A.
Proof.
  intros * H. generalize dependent Ψ'. induction H; intros; auto.
  - econstructor.
    eapply d_subenv_same_dtvar; eauto.
  - apply d_wf_typ__stvar. 
    eapply d_subenv_same_dtvar; eauto.
  - eapply d_wf_typ__all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed.

Lemma d_subtenv_wf_env : forall Ψ,
  ⊢ᵈₜ Ψ ->
  forall Ψ',
    d_subtenv Ψ' Ψ ->
    ⊢ᵈₜ Ψ'.
Proof.
  intros Ψ H. induction H; intros.
  - inversion H. auto.
  - dependent destruction H1.
    econstructor; auto.
    erewrite <- d_subtenv_same_dom; auto.
  - dependent destruction H2.
    econstructor; auto.
    + apply d_sub_d_wf in H3. destruct H3.
      eapply d_subtenv_wf_typ; eauto. auto. intuition.
    + erewrite <- d_subtenv_same_dom; auto.
Qed.

Lemma d_subtenv_wf_tenv_inv : forall Ψ' Ψ,
  ⊢ᵈₜ Ψ' ->
  d_subtenv Ψ' Ψ ->
  ⊢ᵈₜ Ψ. 
Proof with subst; try solve_notin; eauto using d_sub_d_wf_typ2.
  intros * HW HS. induction* HS.
  all: forwards HE: d_subtenv_same_dom HS;
    forwards*: d_wf_tenv_strengthen_cons HW;
    inverts HW;
    econstructor; try rewrite HE...
Qed.

Ltac solve_wf_subenv := match goal with
  | H : d_subtenv ?Ψ' ?Ψ |- ?Ψ' ᵗ⊢ᵈ ?A => eapply d_subtenv_wf_typ; eauto
  | H : d_subtenv ?Ψ' ?Ψ |- ⊢ᵈₜ ?Ψ' => eapply d_subtenv_wf_env; eauto
end.

Lemma binds_subtenv: forall Ψ X Ψ',
  X ~ □ ∈ᵈ Ψ -> 
  d_subtenv Ψ' Ψ -> 
  X ~ □ ∈ᵈ Ψ'.
Proof with try solve_by_invert.
  intros* HD HS. induction* HS.
  - forwards* [?|?]: binds_app_1 HD.
  - forwards* [(?&?)|?]: binds_cons_1 HD...
Qed.

Lemma binds_subenv: forall Ψ X Ψ' b,
  b = □ \/ b = ■ ->
  binds X b Ψ ->
  d_subenv Ψ' Ψ -> 
  binds X b Ψ'.
Proof with try solve_by_invert.
  intros* HB HD HS. induction* HS.
  - forwards* [?|?]: binds_app_1 HD.
  - forwards* [?|?]: binds_app_1 HD.
  - forwards* [(?&?)|?]: binds_cons_1 HD...
    subst. inversion HB. inversion H0. inversion H0.
Qed.

Lemma d_mono_typ_subtenv: forall Ψ A Ψ',
  d_mono_typ Ψ A -> 
  d_subtenv Ψ' Ψ -> 
  d_mono_typ Ψ' A.
Proof with eauto using binds_subtenv.
  intros* HD HS. gen HS.
  induction HD; intros...
Qed.

Lemma d_mono_typ_subenv: forall Ψ A Ψ',
  Ψ ᵗ⊢ᵈₘ A -> 
  d_subenv Ψ' Ψ -> 
  Ψ' ᵗ⊢ᵈₘ A.
Proof with eauto using binds_subenv.
  intros* HD HS. gen HS.
  induction HD; intros... 
Qed.

Lemma d_wneq_all_subtenv: forall Ψ A Ψ',
  d_wneq_all Ψ A -> 
  d_subtenv Ψ' Ψ -> 
  d_wneq_all Ψ' A.
Proof with eauto using binds_subtenv.
  intros* HD HS. gen HS.
  induction HD; intros...
Qed.

Lemma d_wneq_all_subenv: forall Ψ A Ψ',
  d_wneq_all Ψ A -> 
  d_subenv Ψ' Ψ -> 
  d_wneq_all Ψ' A.
Proof with eauto using binds_subenv.
  intros* HD HS. gen HS.
  induction HD; intros...
Qed.

#[local] Hint Immediate d_wf_tenv_d_wf_env  : core.

Lemma d_wf_tenv_subenv : forall Ψ Ψ',
  ⊢ᵈₜ Ψ -> 
  d_subenv Ψ' Ψ -> 
  ⊢ᵈₜ Ψ'.
Proof.
  intros * Hwf Hsube. generalize dependent Ψ'. 
  induction Hwf; intros; auto; try dependent destruction Hsube; auto.
  - constructor; auto. erewrite <- d_subenv_same_dom; eauto.
  - constructor; auto. apply d_sub_d_wf_typ1 in H1. eapply d_subenv_wf_typ; eauto.
    erewrite <- d_subenv_same_dom; eauto.
Qed.

Lemma d_wf_env_subenv : forall Ψ Ψ',
  ⊢ᵈ Ψ -> 
  d_subenv Ψ' Ψ -> 
  ⊢ᵈ Ψ'.
Proof.
  intros * Hwf. generalize dependent Ψ'. induction Hwf; intros.
  - apply d_wf_tenv_d_wf_env. eapply d_wf_tenv_subenv; eauto.
  - dependent destruction H0. apply d_wf_env__stvar; eauto.
    erewrite <- d_subenv_same_dom; eauto.
Qed.

Lemma d_sub_subenv: forall Ψ Ψ' A B,
  Ψ ⊢ A <: B -> 
  d_subenv Ψ' Ψ -> 
  Ψ' ⊢ A <: B.
Proof with eauto using d_mono_typ_subenv, d_wneq_all_subenv, d_wf_env_subenv, d_subenv_wf_typ.
  intros Ψ Ψ' A B Hsub. generalize dependent Ψ'.
  induction Hsub; intros; auto; try solve [constructor; eauto using d_mono_typ_subtenv, d_wf_env_subenv, d_subenv_wf_typ].
  - inst_cofinites_for d_sub__all; intros; inst_cofinites_with X...
  - inst_cofinites_for d_sub__alll T:=T...
Qed.

Lemma d_subtenv_subenv: forall Ψ Ψ',
  d_subtenv Ψ' Ψ -> 
  d_subenv Ψ' Ψ.
Proof.
  intros. dependent induction H; auto.
Qed.

Lemma d_sub_subtenv : forall Ψ Ψ' A B,
  Ψ ⊢ A <: B -> 
  d_subtenv Ψ' Ψ -> 
  Ψ' ⊢ A <: B.
Proof.
  intros. apply d_subtenv_subenv in H0. eapply d_sub_subenv; eauto.
Qed.

#[local] Hint Resolve d_wf_typ_subst_tvar d_wf_env_subst_tvar bind_typ_subst d_wf_typ_lc_typ : core.

Definition dmode_size (mode : typing_mode) : nat :=
  match mode with
  | typingmode__inf => 0
  | typingmode__chk => 1
  end.

Fixpoint exp_size (e:exp) : nat :=
  match e with
    | exp_unit => 1
    | exp_var_f _ => 1
    | exp_var_b _ => 1
    | exp_abs e1 => 1 + exp_size e1
    | exp_app e1 e2 => 1 + exp_size e1 + exp_size e2
    | exp_anno e1 _ => 1 + exp_size e1
    | exp_tapp e1 _ => 1 + exp_size e1
    | exp_tabs e => 1 + exp_size e
  end.

Fixpoint typ_size (A:typ) : nat :=
  match A with
    | typ_intersection A1 A2 => typ_size A1 + typ_size A2 + 1
    | typ_union A1 A2 => typ_size A1 + typ_size A2 + 1
    | _ => 0
  end.

Lemma d_wneq_all_tapp_false : forall Ψ A B C,
  d_wneq_all Ψ A ->
  Ψ ⊢ A ○ B ⇒⇒ C -> 
  False.
Proof. 
  intros. generalize dependent B. generalize dependent C. 
    dependent induction H; intros; auto.
  - dependent destruction H0.
  - dependent destruction H0.
  - dependent destruction H0.
  - dependent destruction H1.
  - dependent destruction H1; auto.
    eapply IHd_wneq_all; eauto.
  - dependent destruction H1; auto.
    eapply IHd_wneq_all; eauto.
  - dependent destruction H1; auto.
    + eapply IHd_wneq_all1; eauto.
    + eapply IHd_wneq_all2; eauto.
Qed.
  

Theorem d_inftapp_subsumption_same_env : forall Ψ A B C A',
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ⊢ A' <: A ->
  exists C', Ψ ⊢ C' <: C /\ Ψ ⊢ A' ○ B ⇒⇒ C'.
Proof with auto.
  intros. generalize dependent A'. dependent induction H.
  - intros. dependent induction H1.
    + exists typ_bot. split; auto... 
    + eapply d_sub_open_mono_bot_false in H4; eauto. contradiction.
    + specialize (IHd_sub H H0 (eq_refl _)). destruct IHd_sub as [C1 Hc1].
      exists C1; intuition...
    + specialize (IHd_sub H H0 (eq_refl _)). destruct IHd_sub as [C1 Hc1].
      exists C1; intuition...
    + specialize (IHd_sub1 H H0 (eq_refl _)). destruct IHd_sub1 as [C1 Hc1].
      specialize (IHd_sub2 H H0 (eq_refl _)). destruct IHd_sub2 as [C2 Hc2].
      exists (typ_union C1 C2). split.
      intuition... intuition...
  - intros. dependent induction H2.
    + exists typ_bot. intuition...
      econstructor...
      dependent destruction H0. pick fresh X.
      inst_cofinites_with X.
      erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto...
      rewrite_env ((map (subst_typ_in_dbind B X) nil) ++ Ψ).
      eapply d_wf_typ_subst_tvar; eauto...
    + exists (A0 ᵗ^^ₜ B). split; auto...
      pick fresh X. inst_cofinites_with X.
      erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
      erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (A:=A); eauto.
      rewrite_env ((map (subst_typ_in_dbind B X) nil) ++ Ψ).
      apply d_sub_subst_stvar; auto...
      econstructor; eauto.
      inst_cofinites_for d_wf_typ__all; intros.
      * inst_cofinites_with X. auto.
      * inst_cofinites_with X.
        apply d_wf_typ_stvar_tvar_cons; eauto...
        apply d_sub_d_wf in H5; intuition.
    + inversion H3.
    + specialize (IHd_sub _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [C1 Hc1].
      exists C1; intuition...
    + specialize (IHd_sub _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [C1 Hc1].
      exists C1; intuition...
    + specialize (IHd_sub1 _ H H0 H1 (eq_refl _)).
      specialize (IHd_sub2 _ H H0 H1 (eq_refl _)).
      destruct IHd_sub1 as [C1].
      destruct IHd_sub2 as [C2].
      exists (typ_union C1 C2); intuition.
  - intros. apply d_sub_intersection_inv in H1.
    intuition.
  - intros. apply d_sub_intersection_inv in H1.
    intuition.
  - intros. dependent induction H1.
    + exists typ_bot.
      apply d_inftapp_d_wf in H.
      apply d_inftapp_d_wf in H0.
      intuition...
    + dependent destruction H3.
      * exfalso. eapply d_wneq_all_tapp_false; eauto.
      * exfalso. eapply d_wneq_all_tapp_false; eauto.
    + specialize (IHd_sub _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      apply d_inftapp_d_wf in H. intuition.
      destruct IHd_sub as [C3]. exists C3. intuition.
    + specialize (IHd_sub _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      apply d_inftapp_d_wf in H. intuition.
      destruct IHd_sub as [C3]. exists C3. intuition.
    + specialize (IHd_inftapp1 _ H1).
      destruct IHd_inftapp1 as [C3].
      exists C3. intuition...
      apply d_sub__union1; eauto...
      apply d_inftapp_d_wf in H0. intuition.
    + specialize (IHd_inftapp2 _ H1).
      destruct IHd_inftapp2 as [C3].
      exists C3. intuition...
      apply d_sub__union2; eauto...
      apply d_inftapp_d_wf in H. intuition.
    + specialize (IHd_sub1 _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      destruct IHd_sub1 as [C1'].
      destruct IHd_sub2 as [C2'].
      exists (typ_union C1' C2'). intuition...
Qed.

#[export] Hint Immediate d_inftapp_d_wf_env d_inftapp_d_wf_typ1 d_inftapp_d_wf_typ2 d_inftapp_d_wf_typ3 : core.

Lemma d_inftapp_subenv : forall Ψ Ψ' A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  d_subtenv Ψ' Ψ ->
  Ψ' ⊢ A ○ B ⇒⇒ C.
Proof with auto;
eauto using d_subtenv_wf_env, d_subtenv_wf_typ.
  intros * HA HE.
  induction HA; intuition eauto...
Qed.

Corollary d_inftapp_subsumption: forall Ψ Ψ' A A' B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ⊢ A' <: A ->
  d_subtenv Ψ' Ψ ->
  exists C', Ψ ⊢ C' <: C /\ Ψ' ⊢ A' ○ B ⇒⇒ C'.
Proof with eauto.
  intros * HA HS HE.
  forwards (?&?&HA'): d_inftapp_subsumption_same_env HA HS.
  forwards : d_inftapp_subenv HA' HE.
  exists*.
Qed.

Theorem d_inftapp_soundness2 : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  (exists A', Ψ ⊢ A <: typ_all A' /\ Ψ ⊢ C <: open_typ_wrt_typ A' B /\ Ψ ⊢ open_typ_wrt_typ A' B <: C) \/ 
  (Ψ ⊢ A <: typ_bot /\ Ψ ⊢ C <: typ_bot).
Proof.
  intros. dependent induction H; eauto.
  - left. exists A. repeat split.
    + apply d_sub_refl; eauto.
    + apply d_sub_refl; eauto.
      apply d_wf_typ_all_open; eauto.
    + apply d_sub_refl; eauto.
      apply d_wf_typ_all_open; eauto.
  - inversion IHd_inftapp.
    + destruct H1 as [A' [Hsub1 Hsub2]]; auto. left.
      exists A'. split; eauto.
    + right. destruct_conj. split; eauto.
  - inversion IHd_inftapp.
    + destruct H1 as [A' [Hsub1 Hsub2]]; auto. left.
      exists A'. split; eauto.
    + right. destruct_conj. split; eauto.
  - destruct IHd_inftapp1; destruct IHd_inftapp2.
    + destruct H1 as [A1' [Hsub1 Heq1]]; eauto.
      destruct H2 as [A2' [Hsub2 Heq2]]; eauto.
      left.
      exists (typ_union A1' A2'). split; eauto.
      econstructor; eauto.
      * apply sub_transitivity with (B:=typ_all A1'); eauto.
        apply d_sub_d_wf in Hsub1 as Hwf1.
        apply d_sub_d_wf in Hsub2 as Hwf2.
        destruct_conj. dependent destruction H6. dependent destruction H11.
        inst_cofinites_for d_sub__all; eauto; intros; inst_cofinites_with X.
        -- unfold open_typ_wrt_typ. simpl.
           auto. 
        -- unfold open_typ_wrt_typ. simpl.
           apply d_sub__union1; eauto.
           apply d_sub_refl; eauto.
           apply d_wf_env__stvar; eauto.
           apply d_wf_typ_tvar_stvar_cons; eauto.
           apply d_wf_typ_tvar_stvar_cons; eauto.
      * apply sub_transitivity with (B:=typ_all A2'); eauto.
        apply d_sub_d_wf in Hsub1 as Hwf1.
        apply d_sub_d_wf in Hsub2 as Hwf2.
        destruct_conj. dependent destruction H6. dependent destruction H11.
        inst_cofinites_for d_sub__all; eauto; intros; inst_cofinites_with X.
        -- unfold open_typ_wrt_typ. simpl.
           auto. 
        -- unfold open_typ_wrt_typ. simpl.
           apply d_sub__union2; eauto.
           apply d_sub_refl; eauto.
           apply d_wf_env__stvar; eauto.
           apply d_wf_typ_tvar_stvar_cons; eauto.
           apply d_wf_typ_tvar_stvar_cons; eauto.
      * destruct_conj; split; unfold open_typ_wrt_typ in *; simpl; subst; auto.
        -- apply d_sub__union3; eauto.
           apply sub_transitivity with (B:=open_typ_wrt_typ_rec 0 B A1'); eauto.
           apply d_sub__union1; eauto. apply d_sub_refl; eauto.
           apply d_sub_d_wf_typ1 in H4; eauto.
           apply d_sub_d_wf_typ1 in H2; eauto.
           apply sub_transitivity with (B:=open_typ_wrt_typ_rec 0 B A2'); eauto.
           apply d_sub__union2; eauto. apply d_sub_refl; eauto.
           apply d_sub_d_wf_typ1 in H2; eauto.
           apply d_sub_d_wf_typ1 in H4; eauto.
        -- apply d_sub__union3; eauto.
    + left. destruct H1 as [A1']. 
      exists A1'. destruct_conj. repeat split; eauto.
      * apply d_sub__union3; eauto.
        apply sub_transitivity with (B:=typ_bot); eauto.
        apply d_sub_d_wf_typ2 in H1; eauto.
      * apply d_sub__union3; eauto.
        apply sub_transitivity with (B:=typ_bot); eauto.
        apply d_sub_d_wf_typ1 in H5; eauto.
    + left. destruct H2 as [A2']. 
      exists A2'. destruct_conj. repeat split; eauto.
      * apply d_sub__union3; eauto.
        apply sub_transitivity with (B:=typ_bot); eauto.
        apply d_sub_d_wf_typ2 in H2; eauto.
      * apply d_sub__union3; eauto.
        apply sub_transitivity with (B:=typ_bot); eauto.
        apply d_sub_d_wf_typ1 in H4; eauto.
    + right. destruct_conj. split; eauto.
Qed.

Inductive bot_free : typ -> Prop :=
  | bot_free_tvar : forall X,
      bot_free (typ_var_f X)
  | bot_free_unit : 
      bot_free typ_unit
  | bot_free_top : 
      bot_free typ_top
  | bot_free_arrow : forall A B,
      bot_free A ->
      bot_free B ->
      bot_free (typ_arrow A B)
  | bot_free_all : forall A L,
      (forall X, X `notin` L -> bot_free (open_typ_wrt_typ A (typ_var_f X))) ->
      bot_free (typ_all A)
  | bot_free_intersection : forall A B,
      bot_free A ->
      bot_free B ->
      bot_free (typ_intersection A B)
  | bot_free_union : forall A B,
      bot_free A ->
      bot_free B ->
      bot_free (typ_union A B).

Theorem d_inftapp_soundness1 : forall Ψ A B C,
  bot_free A ->
  Ψ ⊢ A ○ B ⇒⇒ C ->
  exists A', Ψ ⊢ A <: typ_all A' /\ C = open_typ_wrt_typ A' B.
Proof.
  intros. dependent induction H0; eauto.
  - inversion H.
  - exists A. split.
    + apply d_sub_refl; eauto.
    + auto.
  - dependent destruction H. destruct IHd_inftapp as [A' [Hsub1 Hsub2]]; auto.
    exists A'. split; eauto.
  - dependent destruction H. destruct IHd_inftapp as [A' [Hsub1 Hsub2]]; auto.
    exists A'. split; eauto.
  - dependent destruction H. 
    destruct IHd_inftapp1 as [A1' [Hsub1 Heq1]]; eauto.
    destruct IHd_inftapp2 as [A2' [Hsub2 Heq2]]; eauto.
    exists (typ_union A1' A2'). split; eauto.
    econstructor; eauto.
    + apply sub_transitivity with (B:=typ_all A1'); eauto.
      apply d_sub_d_wf in Hsub1 as Hwf1.
      apply d_sub_d_wf in Hsub2 as Hwf2.
      destruct_conj. dependent destruction H6. dependent destruction H7.
      inst_cofinites_for d_sub__all; eauto; intros; inst_cofinites_with X.
      * unfold open_typ_wrt_typ. simpl.
        auto. 
      *  unfold open_typ_wrt_typ. simpl.
        apply d_sub__union1; eauto.
        apply d_sub_refl; eauto.
        apply d_wf_env__stvar; eauto.
        apply d_wf_typ_tvar_stvar_cons; eauto.
        apply d_wf_typ_tvar_stvar_cons; eauto.
    + apply sub_transitivity with (B:=typ_all A2'); eauto.
      apply d_sub_d_wf in Hsub1 as Hwf1.
      apply d_sub_d_wf in Hsub2 as Hwf2.
      destruct_conj. dependent destruction H6. dependent destruction H7.
      inst_cofinites_for d_sub__all; eauto; intros; inst_cofinites_with X.
      * unfold open_typ_wrt_typ. simpl.
        auto. 
      * unfold open_typ_wrt_typ. simpl.
        apply d_sub__union2; eauto.
        apply d_sub_refl; eauto.
        apply d_wf_env__stvar; eauto.
        apply d_wf_typ_tvar_stvar_cons; eauto.
        apply d_wf_typ_tvar_stvar_cons; eauto.
    + unfold open_typ_wrt_typ in *. simpl. subst. auto.
Qed.

Theorem d_inftapp_completness : forall Ψ A A' B,
  ⊢ᵈₜ Ψ ->
  Ψ ᵗ⊢ᵈ B ->
  Ψ ⊢ A <: typ_all A' ->
  exists C, Ψ ⊢ A ○ B ⇒⇒ C /\ Ψ ⊢ C <: open_typ_wrt_typ A' B. 
Proof.
  intros. eapply d_inftapp_subsumption_same_env with (B:=B) (C:=open_typ_wrt_typ A' B) in H1; eauto.
  destruct H1 as [C].
  - exists C. intuition.
  - apply d_sub_d_wf in H1; destruct_conj; eauto.
Qed.

(* Theorem d_inftapp_soundness3 : forall Ψ A B C A',
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ⊢ typ_all A' <: A -> Ψ ⊢ open_typ_wrt_typ A' B <: C.
Proof.
  intros. dependent induction H; eauto.
  - dependent destruction H1.
    eapply d_sub_open_mono_bot_false in H4; eauto. contradiction.
  - dependent destruction H2.
    pick fresh X. inst_cofinites_with X.
    rewrite_env (nil ++ X ~ ■ ++ Ψ) in H4.
    eapply d_sub_subst_stvar in H4; eauto. simpl in H4.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; eauto.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; eauto.
    inversion H2.
  - apply d_sub_intersection_inv in H1.
    destruct_conj; eauto.
  - apply d_sub_intersection_inv in H1.
    destruct_conj; eauto.
  - dependent destruction H1. 
    + dependent destruction H1.
      * apply d_wneq_all_tapp_false in H; eauto. contradiction.
      * apply d_wneq_all_tapp_false in H0; eauto. contradiction.
    + eauto.
    + eauto.
Qed. *)

#[export] Hint Immediate d_infabs_d_wf_env d_infabs_d_wf_typ1 d_infabs_d_wf_typ2 d_infabs_d_wf_typ3 : core.

Theorem d_infabs_subsumption_same_env : forall Ψ A A' B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ⊢ A' <: A ->
  exists B' C', Ψ ⊢ typ_arrow B' C' <: typ_arrow B C /\ Ψ ⊢ A' ▹ B' → C'.
Proof with auto using d_mono_typ_d_wf_typ.
  intros. generalize dependent A'. induction H; intros.
  - dependent induction H0...
    + exists typ_top typ_bot. auto...
    + exfalso. eapply d_sub_open_mono_bot_false; eauto.
    + specialize (IHd_sub H (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub H (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub1 H (eq_refl _)).
      specialize (IHd_sub2 H (eq_refl _)).
      destruct IHd_sub1 as [B1 [C1]].
      destruct IHd_sub2 as [B2 [C2]].
      exists (typ_intersection B1 B2) (typ_union C1 C2).
      destruct H0. destruct H1.
      split; intuition...
      dependent destruction H0. dependent destruction H1.
      eauto...
  - dependent induction H2...
    + exists typ_top typ_bot. dependent destruction H2.
      eauto...
    + exists A1 A2. intuition...
      apply d_sub_d_wf in H2_.
      apply d_sub_d_wf in H2_0.
      intuition...
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
      econstructor. eauto. auto...
      * pick fresh Y and apply d_wf_typ__all.
         ** forwards: H4 Y...
         ** forwards: d_sub_d_wf_typ1 H2.
            rewrite_env (nil++Ψ) in H6.
            forwards*: d_wf_typ_open_mono_inv H6.
      * eauto.
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub1 _ _ H H0 H1 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub1 as [B2 [C2]].
      destruct IHd_sub2 as [B3 [C3]].
      exists (typ_intersection B2 B3) (typ_union C2 C3).
      split; intuition...
      dependent destruction H2. dependent destruction H4.
      eauto...
  - dependent induction H2.
    + exists typ_top typ_bot.
      econstructor; eauto...
    + assert (Ψ ⊢ A0 ᵗ^^ₜ T <: A ᵗ^^ₜ T). {
        pick fresh SZ. forwards*: H5 SZ.
        rewrite_env (nil++ (SZ, ■) :: Ψ ) in H6.
        forwards*: d_sub_subst_stvar T H6. eapply d_mono_typ_d_wf_typ...
        simpl in H7.
        rewrite subst_typ_in_typ_open_typ_wrt_typ in H7...
        simpl in H7. case_if in H7.
        rewrite subst_typ_in_typ_fresh_eq in H7...
        rewrite subst_typ_in_typ_open_typ_wrt_typ in H7...
        simpl in H7. case_if in H7...
        rewrite subst_typ_in_typ_fresh_eq in H7...
        all: eauto.
      }
      specialize (IHd_infabs _ H6).
      destruct IHd_infabs as [B2 [C2]].
      exists B2 C2. intuition...
      eapply d_infabs__all with (T:=T); auto. 
      pick fresh Y and apply d_wf_typ__all.
      ** forwards: H3 Y...
      ** forwards: d_sub_d_wf_typ1 H6.
         rewrite_env (nil++Ψ) in H7.
         forwards*: d_wf_typ_open_mono_inv Y H7 H.
    + inversion H3.
    + specialize (IHd_sub _ H H0 H1 IHd_infabs (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2. intuition.
    + specialize (IHd_sub _ H H0 H1 IHd_infabs (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2. intuition.
    + specialize (IHd_sub1 _ H H0 H1 IHd_infabs (eq_refl _)).
      specialize (IHd_sub2 _ H H0 H1 IHd_infabs (eq_refl _)).
      destruct IHd_sub1 as [B2 [C2]].
      destruct IHd_sub2 as [B3 [C3]].
      exists (typ_intersection B2 B3) (typ_union C2 C3).
      intuition...
      dependent destruction H4. dependent destruction H2.
      eauto...
  - apply d_sub_intersection_inv in H1.
    intuition.
  - apply d_sub_intersection_inv in H1.
    intuition.
  - dependent induction H1.
    + exists typ_top typ_bot. intuition.
      econstructor; econstructor; eauto.
      all: eauto using d_infabs_d_wf_typ2, d_infabs_d_wf_typ3.
    + specialize (IHd_sub _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub as [B2' [C2']].
      exists B2' C2'. intuition.
      eapply d_infabs__all with (T:=T); auto.
      * pick fresh Y and apply d_wf_typ__all.
        -- forwards: H4 Y...
        -- forwards: d_sub_d_wf_typ1 H2.
           rewrite_env (nil++Ψ) in H5.
           forwards*: d_wf_typ_open_mono_inv H5.
    + specialize (IHd_sub _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub as [B2' [C2']].
      exists B2' C2'. intuition.
    + specialize (IHd_sub _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub as [B2' [C2']].
      exists B2' C2'. intuition.
    + specialize (IHd_infabs1 _ H1).
      destruct IHd_infabs1 as [B2' [C2']].
      exists B2' C2'. intuition.
      dependent destruction H4. eauto...
    + specialize (IHd_infabs2 _ H1).
      destruct IHd_infabs2 as [B2' [C2']].
      exists B2' C2'. intuition.
      dependent destruction H4. eauto...
    + specialize (IHd_sub1 _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub1 as [B2' [C2']].
      destruct IHd_sub2 as [B3' [C3']].
      exists (typ_intersection B2' B3') (typ_union C2' C3').
      intuition...
      dependent destruction H1. dependent destruction H3.
      intuition...
Qed.

Lemma d_infabs_subenv : forall Ψ Ψ' A B C,
  Ψ ⊢ A ▹ B → C ->
  d_subtenv Ψ' Ψ ->
  Ψ' ⊢ A ▹ B → C.
Proof with eauto using d_subtenv_wf_env, d_subtenv_wf_typ.
  intros * HA HE.
  induction HA; intuition eauto...
  eapply d_infabs__all with (T:=T); eauto using d_mono_typ_subtenv...
Qed.

Corollary d_infabs_subsumption: forall Ψ Ψ' A A' B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ⊢ A' <: A ->
  d_subtenv Ψ' Ψ ->
  exists B' C', Ψ ⊢ typ_arrow B' C' <: typ_arrow B C /\ Ψ' ⊢ A' ▹ B' → C'.
Proof with eauto.
  intros * HA HS HE.
  forwards (?&?&HA'): d_infabs_subsumption_same_env HA HS.
  forwards : d_infabs_subenv HA' HE.
  exists*.
Qed.

Theorem d_infabs_soundness : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ⊢ A <: typ_arrow B C.
Proof.
  intros. induction H; eauto.
  - apply d_sub_refl; auto.
  - dependent destruction H0.
    inst_cofinites_for d_sub__alll T:=T; intros; auto.
    apply d_infabs_d_wf in H2.
    econstructor; intuition; eauto.
  - apply sub_transitivity with (B:=typ_union (typ_arrow B1 C1) (typ_arrow B2 C2)); eauto using d_sub_refl.
    apply d_sub__union3; eauto.
    apply d_sub__union3.
    apply d_sub__arrow; eauto using d_sub_refl.
    apply d_sub__arrow; eauto using d_sub_refl.
Qed.

Theorem d_infabs_completeness: forall Ψ A B C,
  ⊢ᵈₜ Ψ ->
  Ψ ⊢ A <: typ_arrow B C ->
  exists B' C',
    Ψ ⊢ A ▹ B' → C' /\ Ψ ⊢ typ_arrow B' C' <: typ_arrow B C.
Proof.
  intros. 
  eapply d_infabs_subsumption_same_env with (B:=B) (C:=C) in H0; eauto.
  destruct_conj; eauto.
  apply d_sub_d_wf in H0.
  destruct_conj. dependent destruction H2.
  econstructor; auto.
Qed.

#[local] Hint Extern 1 (_ < _) => lia : core.

Lemma exp_size_open_var_rec : forall e x n,
  exp_size e = exp_size (open_exp_wrt_exp_rec n (exp_var_f x) e).
Proof.
  intros. generalize dependent n. induction e; simpl; auto.
  - intros. destruct (lt_eq_lt_dec n n0).
    + destruct s; auto.
    + auto.
Qed.

Lemma d_exp_size_open_var: forall e x,
  exp_size e = exp_size (open_exp_wrt_exp e (exp_var_f x)).
Proof.
  intros. unfold open_exp_wrt_exp.
  apply exp_size_open_var_rec.
Qed.

Lemma exp_size_open_typ_rec : forall e A n,
  exp_size e = exp_size (open_exp_wrt_typ_rec n A e).
Proof.
  intros. generalize dependent n. induction e; simpl; auto.
Qed.

Lemma d_exp_size_open_typ: forall e A,
  exp_size e = exp_size (open_exp_wrt_typ e A).
Proof.
  intros. unfold open_exp_wrt_exp.
  apply exp_size_open_typ_rec.
Qed.

Theorem d_chk_inf_subsumption : forall n1 n2 n3 Ψ Ψ' e A mode,
  exp_size e < n1 ->
  dmode_size mode < n2 ->
  typ_size A < n3 ->
  d_chk_inf Ψ e mode A ->
  d_subtenv Ψ' Ψ ->
    match mode with
    | typingmode__chk => forall A', Ψ ⊢ A <: A' -> Ψ' ⊢ e ⇐ A'
    | typingmode__inf => exists A', Ψ ⊢ A' <: A /\ Ψ' ⊢ e ⇒ A'
    end.
Proof with auto.
  intro n1; induction n1; intro n2; induction n2; intros n3; induction n3; intros * Hn1 Hn2 Hn3 Hty Hsubenv.
  - inversion Hn1.
  - inversion Hn1.
  - inversion Hn1.
  - inversion Hn1.
  - inversion Hn2.
  - inversion Hn2.
  - inversion Hn3.
  - destruct mode.
    (* e => A *)
    + dependent destruction Hty; simpl in Hn1, Hn2, Hn3.
      * eapply d_subtenv_same_var in Hsubenv as Hsubenvvar; eauto.
        destruct Hsubenvvar as [S1 [Hbind Hsub]]. exists S1; intuition.
        constructor; eauto. eapply d_subtenv_wf_env; eauto.
      (* e : A => A *)
      * exists A. split.
        apply d_sub_refl; auto...
        apply d_wf_tenv_d_wf_env.
        eapply d_chk_inf_wf_env; eauto.
        econstructor. eapply d_subtenv_wf_typ with (Ψ:=Ψ); auto.
        refine (IHn1 _ _ _ _ _ _ _ _ _ _  Hty _ _ _); eauto... simpl in *...
        apply d_sub_refl; auto...
        apply d_wf_tenv_d_wf_env. eapply d_chk_inf_wf_env; eauto.
      (* () => 1 *)
      * exists typ_unit. split; auto.
        econstructor. eapply d_subtenv_wf_env; eauto.
      (* e1 e2 => A *)
      * eapply IHn1 in Hty1; eauto...
        destruct Hty1 as [A2]. inversion H0.
        eapply d_infabs_subsumption in H; eauto.
        destruct H as [B2 [C2]].
        exists C2; intuition.
        dependent destruction H0...
        dependent destruction H0...
        econstructor; eauto...
        refine (IHn1 _ _ _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
      * exists (typ_arrow A B).
        inst_cofinites_by (L `union` dom Ψ `union` fvar_in_exp e).
        eapply IHn1 with (Ψ':=x ~ dbind_typ A ++ Ψ') in H0 as Hty; eauto... 
        -- split. eapply d_sub_refl...
           ++ apply d_chk_inf_wf_env in H0. dependent destruction H0...
           ++ apply d_mono_typ_d_wf_typ...
           ++ eapply d_chk_inf__inf_abs_mono with (L:=L `union` dom Ψ').
              eapply d_mono_typ_subtenv; eauto.
              intros.
              replace (open_exp_wrt_exp e (exp_var_f x0)) with ({exp_var_f x0 ᵉ/ₑ x} open_exp_wrt_exp e (exp_var_f x)).
              apply d_chk_inf_rename_var_cons. apply Hty; eauto. 
              ** apply d_sub_refl. eapply d_wf_tenv_d_wf_env. eapply d_chk_inf_wf_env; eauto.
                 apply d_chk_inf_wf_typ in H0; auto.
              ** solve_notin. 
              ** simpl. rewrite subst_exp_in_exp_open_exp_wrt_exp...
                 rewrite (subst_exp_in_exp_fresh_eq e); eauto...
                 simpl. case_if; auto...
        -- rewrite <- d_exp_size_open_var. lia.
        -- econstructor...
          apply d_sub_refl.
          apply d_chk_inf_wf_env in H0. dependent destruction H0...
          apply d_mono_typ_d_wf_typ in H. dependent destruction H...
      (* /\ a. e : A => forall a. A *)
      * exists (typ_all A); split.
        -- eapply d_sub_refl; auto.
           inst_cofinites_by L. apply d_chk_inf_wf_env in H0...
           dependent destruction H0... inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X; auto.
           apply d_chk_inf_wf_typ in H0...
        -- pick fresh X and apply d_chk_inf__inf_tabs; inst_cofinites_with X...
           ++ refine (IHn1 _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
              simpl. rewrite <- d_exp_size_open_typ; lia.
              apply d_sub_refl...  eauto. 
              apply d_chk_inf_wf_env in H0; eauto.
              eapply d_chk_inf_wf_typ in H0; auto.
      (* e @T *)
      * eapply IHn1 in Hty; eauto...
        destruct Hty as [A1 [Hsuba1 Hinfa1]].
        eapply d_inftapp_subsumption in H0; eauto.
        destruct H0 as [C2 Hc2].
        exists C2. intuition...
        econstructor; eauto...
    (* e <= *)
    + dependent destruction Hty; simpl in Hn1, Hn2, Hn3.
      (* \x. e <= Top *)
      * intros.
        dependent induction H0; eauto...
        -- eapply d_chk_inf__chk_abstop with (L:=L `union` dom Ψ)... intros.
           inst_cofinites_with x.
           simpl in H.
           refine (IHn1 _ _ _ _ _ _ _ _ _ _ H _ _ _); eauto...
           rewrite <- d_exp_size_open_var. lia.
           econstructor; auto.
           econstructor. eapply d_wf_tenv_d_wf_env. eapply d_chk_inf_wf_env; eauto.
           econstructor; eauto.
        -- apply d_chk_inf__chk_union1...
           eapply d_subtenv_wf_typ; eauto.
        -- apply d_chk_inf__chk_union2...
           eapply d_subtenv_wf_typ; eauto.
      (* \x. e <= T1 -> T2 *)
      * intros.
        assert (d_wft_ord A') as Hwford.
        { eapply d_wft_ord_complete with (Ψ:=Ψ). eapply d_sub_d_wf_typ2; eauto. }
        induction Hwford.
        -- dependent destruction H1.
           ++ inst_cofinites_for d_chk_inf__chk_abstop. intros.
              inst_cofinites_with x.
              refine (IHn1 _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
              rewrite <- d_exp_size_open_var. lia.
              econstructor; eauto.
              eapply d_wf_tenv_d_wf_env. eapply d_chk_inf_wf_env; eauto.
              inverts H2. eauto using d_wf_typ_weaken_cons.
           ++ inst_cofinites_for d_chk_inf__chk_abs.
              eauto using d_subtenv_wf_typ, d_sub_d_wf_typ1.
              intros. inst_cofinites_with x.
              refine (IHn1 _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
              rewrite <- d_exp_size_open_var. lia.
              applys~ d_sub_weaken_cons.
              apply d_chk_inf_wf_env in H0...
           ++ inversion H2.
           ++ inversion H3.
           ++ inversion H3.
        -- dependent destruction H1; auto...
        -- dependent destruction H1; eauto using d_subtenv_wf_typ...
      (* e <= forall a. A *)
      (*  * admit. ignore for now *** *)
      (* e <= A *)
      * intros.
        eapply IHn2 in Hty; eauto.
        destruct Hty as [A'' [Hsub Hinf]].
        apply d_chk_inf__chk_sub with (B := A''); auto.
        apply sub_transitivity with (B := B); auto...
        eapply d_sub_subenv; eauto. apply d_subtenv_subenv... 
        apply sub_transitivity with (B := A); auto...
        eapply d_sub_subenv; eauto. apply d_subtenv_subenv... 
        eapply d_sub_subenv; eauto. apply d_subtenv_subenv... 
        simpl. lia.
      * intros. assert (d_wft_ord A') as Hwford.
        { eapply d_wft_ord_complete with (Ψ:=Ψ). eapply d_sub_d_wf_typ2; eauto. }
        induction Hwford.
        -- dependent destruction H.
           ++ dependent destruction H0. refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ inversion H1.
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
           ++ inversion H1.
           ++ inversion H1.
        -- dependent destruction H; auto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
        -- dependent destruction H; eauto using d_subtenv_wf_typ...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
      * intros.
        refine (IHn3 _ _ _ _ _ _ _ _ Hty _ _ _); eauto...
        apply d_sub_union_inv in H0. intuition.
      * intros.
        refine (IHn3 _ _ _ _ _ _ _ _ Hty _ _ _); eauto...
        apply d_sub_union_inv in H0. intros. intuition.
Qed.

Corollary d_chk_subsumption : forall Ψ e A B,
  ⊢ᵈₜ Ψ ->
  Ψ ⊢ e ⇐ A ->
  Ψ ⊢ A <: B ->
  Ψ ⊢ e ⇐ B.
Proof.
  intros.
  refine (d_chk_inf_subsumption _ _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto.
  now apply d_subenv_refl.
Qed.
