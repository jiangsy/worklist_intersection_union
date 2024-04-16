Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import Lia.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import uni.algo_worklist.transfer.
Require Import uni.algo_worklist.prop_rename.
Require Import ln_utils.

Ltac destruct_trans_wl :=
  match goal with 
  | H : trans_worklist ?θ ?Γ (dworklist_conswork ?Ω ?w) ?θ' |- _ => dependent destruction H
  end.

Ltac destruct_trans' :=
  lazymatch goal with
  | H : trans_work ?θ ?wᵃ (?wᵈ _) |- _ => dependent destruction H
  | H : trans_work ?θ ?wᵃ (?wᵈ _ _) |- _ => dependent destruction H
  | H : trans_work ?θ ?wᵃ (?wᵈ _ _ _) |- _ => dependent destruction H
  | H : trans_conts ?θ ?wᵃ (?C_CS _) |- _ => dependent destruction H
  | H : trans_conts ?θ ?wᵃ (?C_CS _ _) |- _ => dependent destruction H
  | H : trans_contd ?θ ?wᵃ (?C_CD _ _) |- _ => dependent destruction H
  | H : trans_contd ?θ ?wᵃ (?C_CD _ _) |- _ => dependent destruction H
  | H : trans_exp ?θ ?eᵃ (open_exp_wrt_exp _ _) |- _ => fail
  | H : trans_exp ?θ ?eᵃ exp_unit |- _ => dependent destruction H
  | H : trans_exp ?θ ?eᵃ (?C_E _) |- _ => dependent destruction H
  | H : trans_exp ?θ ?eᵃ (?C_E _ _) |- _ => dependent destruction H
  | H : trans_typ ?θ (` ?X) ?Aᵈ |- _ => fail
  | H : trans_typ ?θ ?Aᵃ (open_typ_wrt_typ _ _) |- _ => fail
  | H : trans_typ ?θ ?Aᵃ typ_unit |- _ => dependent destruction H
  | H : trans_typ ?θ ?Aᵃ typ_bot |- _ => dependent destruction H
  | H : trans_typ ?θ ?Aᵃ typ_top |- _ => dependent destruction H
  | H : trans_typ ?θ ?Aᵃ (`?X) |- _ => dependent destruction H
  | H : trans_typ ?θ ?Aᵃ (?C_T _)  |- _ => dependent destruction H
  | H : trans_typ ?θ ?Aᵃ (?C_T _ _)  |- _ => dependent destruction H
  end.

Ltac destruct_trans :=
  repeat destruct_trans'.

Ltac rename_typ_rev_to_fresh' :=
  repeat 
    lazymatch goal with
    | H : trans_typ ?θ ?Aᵃ (open_typ_wrt_typ _ _)  |- _ => fail
    | H : trans_typ ?θ ?Aᵃ (?C_T _ _) |- _ => fail
    | H : trans_typ ?θ ?A1ᵃ ?A1ᵈ |- _ =>
      let A1ᵃ1 := fresh A1ᵈ"ᵃ0" in 
      rename A1ᵃ into A1ᵃ1;
      generalize dependent H
    end.
    
Ltac rename_typ_rev' :=
  repeat 
    lazymatch goal with
    | H : trans_typ ?θ ?Aᵃ (open_typ_wrt_typ _ _)  |- _ => fail
    | H : trans_typ ?θ ?Aᵃ (?C_T _ _) |- _ => fail
    | H : trans_typ ?θ ?A1ᵃ ?A1ᵈ |- _ =>
      let A1ᵃ1 := fresh A1ᵈ"ᵃ" in 
      rename A1ᵃ into A1ᵃ1;
      generalize dependent H
    end.

Ltac rename_typ_rev :=
  rename_typ_rev_to_fresh';
  intros;
  rename_typ_rev';
  intros.

Open Scope aworklist_scope.

#[local] Hint Resolve wf_ss_uniq trans_typ_wf_ss trans_wl_wf_ss : core.

Lemma wf_ss_strengthen_app : forall θ1 θ2,
  wf_ss (θ2 ++ θ1) ->
  wf_ss θ1.
Proof.
  intros. induction θ2; auto.
  - destruct a; destruct d; dependent destruction H; auto.
Qed.

Lemma wf_ss_etvar_bind_another : forall θ1 θ2 X T1 T2,
  wf_ss (θ2 ++ (X, dbind_typ T1) :: θ1) ->
  d_mono_typ (ss_to_denv θ1) T2 ->
  wf_ss (θ2 ++ (X, dbind_typ T2) :: θ1).
Proof.
  intros. induction θ2; auto.
  - dependent destruction H. constructor; auto.
  - destruct a; destruct d; dependent destruction H; try solve [constructor; auto].
    + simpl. constructor; auto.
      erewrite <- wf_ss_etvar_same_denv in H1; eauto.
      erewrite <- wf_ss_etvar_same_denv; eauto.
Qed.

Lemma wf_ss_tvar_notin_remaining : forall θ1 θ2 X b,
  wf_ss (θ2 ++ (X, b) :: θ1)->
  X `notin` dom θ2 `union` dom θ1.
Proof.
  intros. induction θ2; try dependent destruction H; auto.
  - simpl in *. apply IHθ2 in H; auto.
  - simpl in *. apply IHθ2 in H; auto.
  - simpl in *. apply IHθ2 in H; auto.
Qed.


Lemma wf_ss_late_dom_notin_ftver_bind_typ : forall θ1 θ2 X T,
  wf_ss (θ2 ++ (X, dbind_typ T) :: θ1) ->
  (forall Y, Y `in` dom θ2 -> Y `notin` ftvar_in_typ T).
Proof.
  intros. assert (wf_ss ((X, dbind_typ T) :: θ1)) by 
      (eapply wf_ss_strengthen_app; eauto).
  eapply wf_ss_binds_monotyp in H1; eauto.
  simpl in H1.
  dependent induction H1; auto.
  - apply notin_singleton. unfold not. intros. subst.
    apply wf_ss_uniq in H as Huniq.
    apply binds_ss_to_denv_binds_ss in H1.
    assert (Y ~ □ ∈ᵈ (θ2 ++ (X, dbind_typ ` Y) :: θ1)) by auto.
    eapply binds_app_uniq_iff in H2; auto. 
    inversion H2; destruct H3.
    + apply binds_dom_contradiction in H1; auto.
    + contradiction.
  - simpl. apply notin_union; eauto.
    + eapply IHd_mono_typ1; eauto.
      eapply wf_ss_etvar_bind_another; eauto.
    + eapply IHd_mono_typ2; eauto.
      eapply wf_ss_etvar_bind_another; eauto.
Qed.


Lemma d_mono_typ_strengthen : forall θ X b T,
  wf_ss ((X, b) :: θ) ->
  d_mono_typ (ss_to_denv ((X, b) :: θ)) T ->
  X `notin` ftvar_in_typ T ->
  d_mono_typ (ss_to_denv θ) T.
Proof.
  intros. dependent induction H0; eauto.
  - destruct b; simpl in *. 
    + inversion H0. dependent destruction H2. solve_notin_eq X0.
      constructor; auto.
    + inversion H0. dependent destruction H2.
      constructor; auto.
    + constructor; auto.
  - simpl in *. eauto.
Qed.

Lemma d_mono_typ_strengthen_app : forall θ1 θ2 X T1 T2,
  wf_ss (θ2 ++ (X, dbind_typ T1) :: θ1) ->
  d_mono_typ (ss_to_denv (θ2 ++ (X, dbind_typ T1) :: θ1)) T2 ->
  d_mono_typ (ss_to_denv θ1) T1 ->
  (∀ Y : atom, Y `in` ftvar_in_typ T2 → Y `in` ftvar_in_typ T1) ->
  d_mono_typ (ss_to_denv θ1) T2.
Proof.
  intros. induction θ2; simpl in *; auto.
  - destruct a as [X0 b]. destruct b.
    + apply IHθ2; auto.
      * dependent destruction H; auto.
      * eapply  d_mono_typ_strengthen; eauto.
        unfold not. intros. apply H2 in H3.
        rewrite_env (((X0, □) :: θ2) ++ (X, dbind_typ T1) :: θ1) in H.
        assert (X0 `in` dom ((X0, □) :: θ2)) by (simpl; auto).
        specialize (wf_ss_late_dom_notin_ftver_bind_typ _ _ _ _ H X0 H4).
        intros. contradiction.
    + apply IHθ2; auto.
      * dependent destruction H; auto.
      * eapply  d_mono_typ_strengthen; eauto.
        unfold not. intros. apply H2 in H3.
        rewrite_env (((X0, ■) :: θ2) ++ (X, dbind_typ T1) :: θ1) in H.
        assert (X0 `in` dom ((X0, ■) :: θ2)) by (simpl; auto).
        specialize (wf_ss_late_dom_notin_ftver_bind_typ _ _ _ _ H X0 H4).
        intros. contradiction.
    + apply IHθ2; auto.
      * dependent destruction H; auto.
Qed.


Corollary a_wf_wl_two_etvar_neq1 : forall X1 X2 b1 b2 Γ1 Γ2,
  ⊢ᵃʷ aworklist_constvar (Γ2 ⧺ (aworklist_constvar Γ1 X1 b1)) X2 b2 ->
  X1 <> X2.
Proof.
  intros.
  replace (aworklist_constvar (Γ2 ⧺ (aworklist_constvar Γ1 X1 b1)) X2 b2) with 
     ((aworklist_constvar Γ2 X2 b2) ⧺ (aworklist_constvar Γ1 X1 b1)) in H by auto.
  eapply a_wf_wl_tvar_notin_remaining in H.
  simpl in H. fsetdec.
Qed.

Corollary a_wf_wl_two_etvar_neq2 : forall X1 X2 b1 b2 Γ1 Γ2,
  ⊢ᵃʷ aworklist_constvar (Γ2 ⧺ (aworklist_constvar Γ1 X1 b1)) X2 b2 ->
  X2 <> X1.
Proof.
  intros. unfold not. intros.
  apply a_wf_wl_two_etvar_neq1 in H. subst. contradiction.
Qed.


Lemma trans_typ_tvar_stvar_notin : forall θ X1 X2 T Tᵈ Γ1 Γ2 Ω b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  (X2, b) :: θ ᵗ⫦ T ⇝ Tᵈ -> 
  (X2, b) :: θ ᵗ⫦ ` X1 ⇝ Tᵈ ->
  nil ⫦ Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ Γ1 ⇝ Ω ⫣ θ ->
  X2 `notin` ftvar_in_typ T.
Proof.
  intros.   
  apply trans_wl_split in H2. destruct H2 as [Ω1 [Ω2 [θ'' [Heq [Htrans1 Htrans2]]]]]. subst.
  apply trans_wl_split_ss in Htrans2. destruct Htrans2 as [θ0'']. subst.
  dependent destruction Htrans1.
  assert (wf_ss (((X2, b) :: θ0'') ++ (X1, dbind_typ T0) :: θ')) by eauto.
  eapply wf_ss_late_dom_notin_ftver_bind_typ with (Y:=X2) in H4; simpl...
  assert ((X2, b) :: θ0'' ++ (X1, dbind_typ T0) :: θ' ᵗ⫦ ` X1 ⇝ T0) by eauto 6.
  unify_trans_typ.
  unfold not. intros.
  eapply trans_typ_tvar_stvar_in_atyp_in_dtyp in H5; eauto.
  inversion H; subst; auto.
  auto.
Qed.

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp : core.

Lemma trans_typ_etvar_subst : forall θ1 θ2 Tᵃ Tᵈ X Aᵃ Aᵈ,
  lc_typ Aᵃ -> 
  wf_ss (θ2 ++ θ1) ->
  X `notin` dom (θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) Tᵈ ->
  θ2 ++ θ1 ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ2 ++ X ~ dbind_typ Tᵈ ++ θ1 ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  θ2 ++ θ1 ᵗ⫦ {Tᵃ /ᵗ X} Aᵃ ⇝ Aᵈ.
Proof with eauto using wf_ss_strengthen_etvar.
  intros * Hlc Hwfss Hnotin Hmono Hinstt Hinsta.
  generalize dependent θ2. generalize dependent X. generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros; try solve [simpl in *; dependent destruction Hinsta; 
                                                          eauto using wf_ss_strengthen_etvar].
  - destruct_eq_atom...
    + assert (θ2 ++ (X0, dbind_typ Tᵈ) :: θ1 ᵗ⫦ ` X0 ⇝ Tᵈ) by eauto.
      unify_trans_typ...
    + dependent destruction Hinsta...
      * apply trans_typ__tvar...
        apply binds_remove_mid in H0...
      * apply trans_typ__stvar...
        apply binds_remove_mid in H0...
      * apply trans_typ__etvar...
        apply binds_remove_mid in H0...
  - simpl in Hinsta. 
    dependent destruction Hinsta...
    inst_cofinites_for trans_typ__all; intros;
    inst_cofinites_with X0; rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    + apply s_in_subst_inv...
    + rewrite_env (((X0, □) :: θ2) ++ θ1).  
      apply H0; auto.
      * simpl. constructor; auto.
      * simpl. rewrite_env (nil ++ (X0 ~ □) ++ (θ2 ++ θ1)). 
        apply trans_typ_weaken; auto.
        constructor; auto.
Qed.


Lemma trans_typ_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X Aᵃ Aᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⫦ {Tᵃ /ᵗ X} Aᵃ ⇝ Aᵈ.
Proof.
  intros.
  assert (exists θ1 θ2, θ = θ2 ++ X ~ dbind_typ Tᵈ ++ θ1) by admit.
  destruct H4 as [θ1 [θ2 Heq]].
  rewrite  Heq in *.
  apply trans_typ_weaken; auto.
  apply trans_typ_strengthen_etvar in H2 as Htranst; auto.
  eapply trans_typ_etvar_subst with (Tᵈ:=Tᵈ); eauto.
  - apply wf_ss_tvar_notin_remaining in H.
    rewrite dom_app; auto.
  - apply wf_ss_strengthen_app in H. dependent destruction H; auto. 
Admitted.


Lemma trans_exp_etvar_subst_same_ss' : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᵉ⫦ eᵃ ⇝ eᵈ ->
  θ ᵉ⫦ (subst_tvar_in_exp Tᵃ X eᵃ) ⇝ eᵈ
with trans_body_etvar_subst_same_ss' : forall θ Tᵃ Tᵈ X bᵃ bᵈ,
  lc_body bᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᵇ⫦ bᵃ ⇝ bᵈ ->
  θ ᵇ⫦ (subst_tvar_in_body Tᵃ X bᵃ) ⇝ bᵈ.
Proof.
  - intros * Hlc.
    generalize dependent θ. generalize dependent eᵈ.
    induction Hlc; simpl in *; intros.
    + dependent destruction H3; constructor; auto.
    + dependent destruction H3; constructor; auto.
    + dependent destruction H5.
      inst_cofinites_for trans_exp__abs. intros.
      inst_cofinites_with x.
      apply H0 in H5; auto.
      rewrite subst_tvar_in_exp_open_exp_wrt_exp in H5...
      simpl in *. auto.
    + dependent destruction H3; eauto.
    + dependent destruction H4; eauto.
      inst_cofinites_for trans_exp__tabs.
      intros. inst_cofinites_with X0.
      eapply trans_body_etvar_subst_same_ss' in H4; eauto.
      * rewrite subst_tvar_in_body_open_body_wrt_typ in H4; simpl in *.
        destruct_eq_atom; auto.
        eapply trans_typ_lc_atyp; eauto.
      * rewrite_env (nil ++ (X0 ~ □) ++ θ). apply trans_typ_weaken; eauto.
        constructor; auto.
    + dependent destruction H4.
      constructor.
      * apply IHHlc; eauto.
      * eapply trans_typ_etvar_subst_same_ss; eauto.
    + dependent destruction H4.
      constructor.
      * apply IHHlc; eauto.
      * eapply trans_typ_etvar_subst_same_ss; eauto.
  - intros * Hlc. dependent destruction Hlc; intros; simpl in *.
    dependent destruction H5. constructor.
    + eapply trans_exp_etvar_subst_same_ss'; eauto.
    + eapply trans_typ_etvar_subst_same_ss; eauto.
Qed.


Lemma trans_exp_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᵉ⫦ eᵃ ⇝ eᵈ ->
  θ ᵉ⫦ (subst_tvar_in_exp Tᵃ X eᵃ) ⇝ eᵈ
with trans_body_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X bᵃ bᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᵇ⫦ bᵃ ⇝ bᵈ ->
  θ ᵇ⫦ (subst_tvar_in_body Tᵃ X bᵃ) ⇝ bᵈ.
Proof.
  - intros. clear trans_exp_etvar_subst_same_ss. clear  trans_body_etvar_subst_same_ss.
    apply trans_exp_lc_aexp in H3 as Hlce.
    apply trans_typ_lc_atyp in H2 as Hlct.
    eapply trans_exp_etvar_subst_same_ss'; eauto. 
  - intros. clear trans_exp_etvar_subst_same_ss. clear trans_body_etvar_subst_same_ss.
    apply trans_body_lc_abody in H3 as Hlcb.
    apply trans_typ_lc_atyp in H2 as Hlct.
    eapply trans_body_etvar_subst_same_ss'; eauto. 
Qed.


Lemma trans_conts_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X csᵃ csᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᶜˢ⫦ csᵃ ⇝ csᵈ ->
  θ ᶜˢ⫦ (subst_tvar_in_conts Tᵃ X csᵃ) ⇝ csᵈ
with trans_contd_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X cdᵃ cdᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ᶜᵈ⫦ cdᵃ ⇝ cdᵈ ->
  θ ᶜᵈ⫦ (subst_tvar_in_contd Tᵃ X cdᵃ) ⇝ cdᵈ.
Proof.
  intros. generalize dependent θ. generalize dependent csᵈ.
  induction csᵃ; intros; simpl in *; dependent destruction H3;
    constructor;
      try eapply trans_typ_etvar_subst_same_ss;
      try eapply trans_exp_etvar_subst_same_ss;
      try apply trans_contd_etvar_subst_same_ss; 
      try apply IHcsᵃ; eauto.
  intros. generalize dependent θ. generalize dependent cdᵈ.
  induction cdᵃ; intros; simpl in *; dependent destruction H3;
    constructor;
      try eapply trans_typ_etvar_subst_same_ss; 
      try eapply trans_exp_etvar_subst_same_ss;
      try apply trans_contd_etvar_subst_same_ss; 
      try apply IHcsᵃ; eauto.
Qed.

Lemma trans_work_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X wᵃ wᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ ⫦ʷ wᵃ ⇝ wᵈ ->
  θ ⫦ʷ (subst_tvar_in_work Tᵃ X wᵃ) ⇝ wᵈ.
Proof.
  intros. destruct wᵃ; try simpl in *; dependent destruction H3;
    constructor; 
      try eapply trans_typ_etvar_subst_same_ss; eauto;
      try eapply trans_exp_etvar_subst_same_ss; eauto;
      try eapply trans_conts_etvar_subst_same_ss; eauto;
      try eapply trans_contd_etvar_subst_same_ss; eauto.
Qed.

#[local] Hint Resolve a_wf_wl_two_etvar_neq1 a_wf_wl_two_etvar_neq2 : core.
#[local] Hint Resolve d_mono_typ_d_wf_typ : core.

Lemma trans_typ_etvar_binds : forall θ X Γ Ω T,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  θ ᵗ⫦ ` X ⇝ T ->
  binds X (dbind_typ T) θ.
Proof.
  intros. eapply trans_wl_a_wl_binds_etvar_ss in H0; eauto.
  destruct H0 as [T'].
  assert (θ ᵗ⫦ ` X ⇝ T') by eauto.
  unify_trans_typ. auto.
Qed.


Lemma a_worklist_subst_transfer_same_dworklist_rev_exist': forall Γ1 Γ2 Ω θ X T Tᵈ,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  X `notin` ftvar_in_typ T ->
  trans_worklist nil (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) Ω θ ->
  θ ᵗ⫦ T ⇝ Tᵈ ->
  θ ᵗ⫦ ` X ⇝ Tᵈ ->
  exists Γ'1 Γ'2 θ', 
      aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X T Γ'1 Γ'2 /\
      trans_worklist nil (awl_app (subst_tvar_in_aworklist T X Γ'2) Γ'1) Ω θ' /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      wf_ss θ'.
Proof with eauto.
  intros * Hwf Hnotin Htranswl Htranst Htransx. generalize dependent Ω. 
    generalize dependent Γ1. generalize dependent θ. induction Γ2; simpl in *; 
    intros.
  - dependent destruction Htranswl...
    exists Γ1, aworklist_empty, θ'. repeat split; intros; simpl in *...
    + inversion H2. dependent destruction H3. solve_notin_eq Y. auto.
  - dependent destruction Htranswl.
    apply IHΓ2 in Htranswl as Hws; auto... 
    destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
    exists Γ'1, (x ~ᵃ A1ᵃ;ᵃ Γ'2), θ'0. repeat split...
    + econstructor; auto.
      apply trans_typ_reorder with (θ:=θ')...
      * intros. apply Hbinds...
        unfold not. intros. subst.
        apply subst_tvar_in_typ_fresh_same in H0...
      * eapply trans_typ_etvar_subst_same_ss; eauto. 
        eapply trans_typ_etvar_binds; eauto.
        rewrite awl_to_aenv_app. simpl...
    + apply Hbinds; auto.
    + apply Hbinds; auto.
    + destruct_a_wf_wl; auto.
  - dependent destruction Htranswl.
    + apply IHΓ2 in Htranswl as Hws; auto.
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      assert (X0 `notin` dom θ'0) by (eapply notin_dom_reorder; eauto).
      exists Γ'1, (X0 ~ᵃ □ ;ᵃ Γ'2), ((X0, □) :: θ'0). 
        repeat split...
      * econstructor; auto.
        eapply a_wf_wl_two_etvar_neq2; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_tvar_empty); eauto.
      * simpl. constructor; auto... 
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * eapply trans_typ_strengthen_cons; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_tvar_empty); eauto.
      * eapply trans_typ_strengthen_cons; eauto. 
      * destruct_a_wf_wl...
    + apply IHΓ2 in Htranswl as Hws; auto.
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      assert (X0 `notin` dom θ'0) by (eapply notin_dom_reorder; eauto).
      exists Γ'1, (aworklist_constvar Γ'2 X0 abind_stvar_empty), ((X0, dbind_stvar_empty) :: θ'0). 
      repeat split; auto...
      * econstructor; auto.
        eapply a_wf_wl_two_etvar_neq2; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_stvar_empty); eauto.
      * simpl. constructor; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * eapply trans_typ_strengthen_cons; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_stvar_empty); eauto.
      * eapply trans_typ_strengthen_cons; eauto.
      * destruct_a_wf_wl; auto.
    + assert (Hdec: (X0 `in` ftvar_in_typ T) \/ (X0 `notin` ftvar_in_typ T)) by fsetdec.
      inversion Hdec.
      * apply trans_wl_split in Htranswl as Htranswlsplit. destruct Htranswlsplit as [Ω1 [Ω2 [θ'' [Heq [Htrans1 Htrans2]]]]].
        dependent destruction Htrans1. subst.
        apply trans_wl_split_ss in Htrans2 as Hsssplit. destruct Hsssplit as [θ'']. subst.
        assert (Hbindsx: binds X (dbind_typ T1) ((X0, dbind_typ T0) :: θ'' ++ (X, dbind_typ T1) :: θ'0)) by auto.
        apply trans_typ_binds_etvar in Hbindsx as Htransx'. unify_trans_typ.
        clear Hbindsx.
        assert (d_mono_typ (ss_to_denv θ'0) T0). {
          assert (binds X0 (dbind_typ T0) ( (X0, dbind_typ T0) :: θ'' ++ (X, dbind_typ T1) :: θ'0)) by auto.
          specialize (trans_typ_tvar_stvar_in_etvar_binds_in_atyp _ _ _ _ _ Htranst H4 H1). intros.
          eapply d_mono_typ_strengthen_app; eauto.
        }
        assert (nil ⫦ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X0 ~ᵃ ⬒ ;ᵃ Γ1 ⇝ (Ω2 ⧺ Ω0) ⫣ θ'' ++ (X, dbind_typ T1) :: (X0, dbind_typ T0) :: θ'0).
        { eapply trans_wl_app with (θ2:=(X, dbind_typ T1) :: (X0, dbind_typ T0) :: θ'0). 
          constructor; auto.
          rewrite_env ((X ~ dbind_typ T1) ++ (X0, dbind_typ T0) :: θ'0 ).
          rewrite_env (θ'' ++ X ~ dbind_typ T1 ++ (X0, dbind_typ T0) :: θ'0).
          eapply trans_wl_weaken_etvar...
          simpl. 
          dependent destruction Hwf. rewrite <- ftvar_in_aworklist_upper in H... 
          rewrite ftvar_in_aworklist'_awl_app in H...
        }
        apply IHΓ2 in H5 as Hws.
        destruct Hws as [Γ'1 [Γ'2 [θ'00 [Hws [Htrans [Hbinds Hwfss]]]]]].
        exists Γ'1, Γ'2, θ'00. repeat split; auto.
        -- intros. apply Hbinds... eapply binds_same_move_etvar_before... 
        -- intros. eapply binds_same_move_etvar_before... apply Hbinds...
        -- apply trans_typ_reorder with (θ:=(X0, dbind_typ T0) :: θ'' ++ (X, dbind_typ T1) :: θ'0); auto...
           intros. apply binds_same_move_etvar_before... 
        -- apply trans_typ_binds_etvar; eauto.
        -- apply a_wf_wl_move_etvar_back; auto.
        -- eapply trans_typ_wf_ss; eauto. 
      * apply IHΓ2 in Htranswl as Hws; auto.
        destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
        assert (X0 `notin` dom θ'0) by (eapply notin_dom_reorder; eauto).
        assert (d_mono_typ (ss_to_denv θ'0) T0). {
           apply d_mono_typ_reorder with (θ:=θ')...
           intros. apply Hbinds; auto.
           apply trans_typ_strengthen_cons in Htransx...
           eapply trans_typ_etvar_binds in Htransx...
           eapply wf_ss_typ_no_etvar with (A:=T0) in Htransx...
           unfold not. intros. subst. contradiction.
           ++ rewrite awl_to_aenv_app. simpl... 
        }
        exists Γ'1, (X0 ~ᵃ ⬒ ;ᵃ Γ'2), ((X0, dbind_typ T0) :: θ'0). 
          repeat split; auto.
        -- econstructor; auto.  
           eapply a_wf_wl_two_etvar_neq2; eauto.
        -- simpl. constructor; auto...
        -- intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
        -- intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
        -- eapply trans_typ_strengthen_cons; eauto.
        -- eapply trans_typ_strengthen_cons; eauto. 
        -- destruct_a_wf_wl; auto.
  - dependent destruction Htranswl.
    apply IHΓ2 in Htranswl as Hws.
    destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
    exists Γ'1, (aworklist_conswork Γ'2 w), θ'0. repeat (split; auto).
    + simpl. constructor; auto.
      apply trans_work_reorder with (θ:=θ')... 
      * intros. apply Hbinds...
        unfold not. intros. subst.
        apply subst_tvar_in_work_fresh_same in H0...
      * eapply trans_work_etvar_subst_same_ss; eauto.
        eapply trans_typ_etvar_binds; eauto.
        rewrite awl_to_aenv_app. simpl...
    + auto.
    + auto.
    + destruct_a_wf_wl; auto.
Qed.


Lemma aworklist_subst_det : forall Γ X T Γ1 Γ2 Γ3 Γ4,
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  aworklist_subst Γ X T Γ3 Γ4 ->
  Γ1 = Γ3 /\ Γ2 = Γ4.
Proof.
  intros * Hwf Hws1 Hws2. generalize dependent Γ3. generalize dependent Γ4. 
    induction Hws1; intros; dependent destruction Hws2; auto; destruct_a_wf_wl;
      try solve_notin_eq X;
      try solve_notin_eq Y;
      try solve [apply IHHws1 in Hws2; intuition; subst; auto].
  - apply worklist_split_etvar_det in x; auto; dependent destruction x.
    subst.
    apply IHHws1 in Hws2; intuition; subst; auto.
    apply a_wf_wl_move_etvar_back; auto.
    eapply a_wf_wl_tvar_notin_remaining in Hwf; eauto.
Qed.


Corollary a_worklist_subst_transfer_same_dworklist_rev_exist: forall Γ Ω θ X T Tᵈ,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ T ->
  trans_worklist nil Γ Ω θ ->
  θ ᵗ⫦ T ⇝ Tᵈ ->
  θ ᵗ⫦ ` X ⇝ Tᵈ ->
  exists Γ1 Γ2 θ', 
      aworklist_subst Γ X T Γ1 Γ2 /\
      trans_worklist nil (awl_app (subst_tvar_in_aworklist T X Γ2) Γ1) Ω θ' /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      wf_ss θ'.
Proof.
  intros. apply aworklist_binds_split in H0; auto.
  destruct H0 as [Γ' [Γ'' Heq]]. rewrite <- Heq in *. clear Heq.
  eapply a_worklist_subst_transfer_same_dworklist_rev_exist'; eauto.
Qed.

Corollary a_worklist_subst_transfer_same_dworklist_rev: forall Γ Ω θ X T Tᵈ Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  a_mono_typ (awl_to_aenv Γ) T ->
  X `notin` ftvar_in_typ T ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  trans_worklist nil Γ Ω θ ->
  θ ᵗ⫦ T ⇝ Tᵈ ->
  θ ᵗ⫦ ` X ⇝ Tᵈ ->
  exists θ', 
      trans_worklist nil (awl_app (subst_tvar_in_aworklist T X Γ2) Γ1) Ω θ' /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      wf_ss θ'.
Proof.
  intros.
  eapply a_worklist_subst_transfer_same_dworklist_rev_exist in H as Hwsex; eauto.
  destruct Hwsex as [Γ'1 [Γ'2 [θ' [Hsubst [Htrans [Hbinds Hwfss]]]]]].
  pose proof (aworklist_subst_det _ _ _ _ _ _ _ H H3 Hsubst). inversion H7. subst.
  exists θ'. repeat (split; auto).
Qed.

Inductive aworklist_ord : aworklist -> Prop :=
  | awl_t_o__empty : aworklist_ord aworklist_empty
  | awl_t_o__work : forall Γ w, aworklist_ord (aworklist_conswork Γ w)
  | awl_t_o__var : forall Γ x ab, aworklist_ord (aworklist_consvar Γ x ab)
  | awl_t_o__tvar : forall Γ X, aworklist_ord (aworklist_constvar Γ X abind_tvar_empty)
  | awl_t_o__stvar : forall Γ X, aworklist_ord (aworklist_constvar Γ X abind_stvar_empty).

Inductive aworklist_trailing_etvar : aworklist -> aworklist -> Prop :=
  | awl_t_e__base : forall Γ0, aworklist_ord Γ0 -> aworklist_trailing_etvar Γ0 Γ0
  | awl_t_e__etvar : forall Γ0 Γ X, aworklist_trailing_etvar Γ0 Γ -> aworklist_trailing_etvar Γ0 
    (aworklist_constvar Γ X abind_etvar_empty).

#[local] Hint Constructors aworklist_ord : core.
#[local] Hint Constructors aworklist_trailing_etvar : core.

Lemma aworklist_trailing_etvar_total : forall Γ,
  ⊢ᵃʷ Γ -> exists Γ0, aworklist_trailing_etvar Γ0 Γ.
Proof.
  intros. induction H; eauto.
  - destruct IHa_wf_wl as [Γ0].
    exists Γ0; eauto.
Qed.

Lemma aworklist_trailing_etvar_reduce_ord : forall Γ0 Γ,
  aworklist_trailing_etvar Γ0 Γ -> Γ0 ⟶ᵃʷ⁎⋅ -> Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros. induction H; auto.
Qed.

Lemma aworklist_trailing_etvar_trans : forall Γ0 Γ Ω θ θ',
  aworklist_trailing_etvar Γ0 Γ -> 
  θ ⫦ Γ ⇝ Ω ⫣ θ' ->
  exists θ'', θ ⫦ Γ0 ⇝ Ω ⫣ θ''.
Proof.
  intros. generalize dependent θ.  generalize dependent θ'.  generalize dependent Ω.
  induction H; eauto; intros.
  - dependent destruction H0.
    apply IHaworklist_trailing_etvar in H0.
    destruct H0 as [Θ'']; eauto.
Qed.

Lemma aworklist_trailing_base_ord : forall Γ0 Γ,
  aworklist_trailing_etvar Γ0 Γ -> 
  aworklist_ord Γ0.
Proof.
  intros. 
  induction H; eauto; intros.
Qed.

Lemma aworklist_trailing_wf_wl : forall Γ0 Γ,
  aworklist_trailing_etvar Γ0 Γ -> 
  ⊢ᵃʷ Γ ->
  ⊢ᵃʷ Γ0.
Proof.
  intros. induction H; eauto.
  - dependent destruction H0; eauto.
Qed.


Inductive aworklist_trailing_sub : aworklist -> aworklist -> Prop :=
  | awl_t_s__base : forall Γ0, aworklist_trailing_sub Γ0 Γ0
  | awl_t_s__work : forall Γ0 Γ T1 T2, 
      aworklist_trailing_sub Γ0 Γ ->
      a_mono_typ (awl_to_aenv Γ) T1 ->
      (forall X, binds X abind_etvar_empty (awl_to_aenv Γ) -> X `notin` ftvar_in_typ T1) ->
      a_mono_typ (awl_to_aenv Γ) T2 ->
      (forall X, binds X abind_etvar_empty (awl_to_aenv Γ) -> X `notin` ftvar_in_typ T2) ->
      aworklist_trailing_sub Γ0 (aworklist_conswork Γ (work_sub T1 T2)).

#[local] Hint Constructors aworklist_trailing_sub : core.


Lemma a_wl_red_aworklist_trailing_sub_weaken : forall Γ0 Γ,
  aworklist_trailing_sub Γ0 Γ ->
  Γ ⟶ᵃʷ⁎⋅ ->
  Γ0 ⟶ᵃʷ⁎⋅.
Proof.
  intros. induction H0; auto; try dependent destruction H; eauto.
  - apply IHa_wl_red.
    dependent destruction H0.
    dependent destruction H2.
    simpl in *.
    constructor; simpl; eauto.
    constructor; simpl; eauto.
    all: intros; apply H1 in H0 as Hfv1; apply H3 in H0 as Hfv2; intuition.
  - inversion H0.
  - inversion H0.
  - apply H1 in H4. solve_notin_eq X. 
  - apply H3 in H4. solve_notin_eq X. 
  - apply H3 in H4. solve_notin_eq X. 
  - apply H1 in H4. solve_notin_eq X. 
  - inversion H2.
  - inversion H0.
  - inversion H0.
  - inversion H2.
  - inversion H2.
  - inversion H0.
Qed.
  

(* transform (Γ0, ^X, ^Y, more existential tvars) to Γ0 *)
Ltac solve_awl_trailing_etvar :=
  match goal with
  | H_1 : ⊢ᵃʷ ?Γ, H_2: ?θ ⫦ ?Γ ⇝ ?Ω ⫣ ?θ' |- _ =>
    let Htr := fresh "Htr" in
    let Γ0 := fresh "Γ0" in
    let Htrans_et := fresh "Htrans_et" in
    let θ' := fresh "θ'" in
    let Hwf := fresh "Hwf" in
    apply aworklist_trailing_etvar_total in H_1 as Htr;
    destruct Htr as [Γ0 Htr];
    eapply aworklist_trailing_etvar_reduce_ord; eauto;
    apply aworklist_trailing_etvar_trans with (Γ0:=Γ0) in H_2 as Htrans_et ; auto;
    destruct Htrans_et as [θ' Htrans_et];
    dependent destruction Htrans_et;
    apply aworklist_trailing_wf_wl in Htr as Hwf; auto;
    match goal with
    | H_3 : aworklist_trailing_etvar (aworklist_constvar ?Γ0 ?X abind_etvar_empty) ?Γ |- _ =>
      apply aworklist_trailing_base_ord in H_3; inversion H_3
    | _ => idtac
    end
  end.

Lemma trans_apply_conts : forall θ csᵃ csᵈ Aᵃ Aᵈ wᵈ,
  θ ᶜˢ⫦ csᵃ ⇝ csᵈ ->
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  apply_conts csᵈ Aᵈ wᵈ ->
  exists wᵃ, apply_conts csᵃ Aᵃ wᵃ /\ θ ⫦ʷ wᵃ ⇝ wᵈ.
Proof.
  intros. induction H1; try dependent destruction H; eauto.
Qed.

Lemma trans_apply_contd : forall θ cdᵃ cdᵈ Aᵃ Aᵈ Bᵃ Bᵈ wᵈ,
  θ ᶜᵈ⫦ cdᵃ ⇝ cdᵈ ->
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⫦ Bᵃ ⇝ Bᵈ ->
  apply_contd cdᵈ Aᵈ Bᵈ wᵈ ->
  exists wᵃ, apply_contd cdᵃ Aᵃ Bᵃ wᵃ /\ θ ⫦ʷ wᵃ ⇝ wᵈ.
Proof.
  intros. induction H2; try dependent destruction H; eauto 6.
(* TODO *)
Admitted.

Lemma trans_typ_subst : forall θ1 θ2 Aᵃ Aᵈ Bᵃ Bᵈ X b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  θ2 ++ (X , b) :: θ1 ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  (forall Y T, binds Y (dbind_typ T) (θ2 ++ θ1) -> X `notin` ftvar_in_typ T) ->
  wf_ss (θ2 ++ θ1) ->
  θ2 ++ θ1 ᵗ⫦ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ᵗ⫦ {Bᵃ /ᵗ X} Aᵃ ⇝ {Bᵈ /ᵗ X} Aᵈ.
Proof with eauto.
  intros. generalize dependent Bᵃ. generalize dependent Bᵈ. 
  dependent induction H0; intros; simpl; destruct_eq_atom; eauto.
  - constructor... 
    apply binds_remove_mid in H0...
  - apply trans_typ__stvar...
    apply binds_remove_mid in H0...
  - assert (binds X b ((θ2 ++ (X, b) :: θ1))) by auto.
    unify_binds. inversion H; inversion H6.
  - constructor...
    apply binds_remove_mid in H0...
    apply H2 in H0 as Hfr...
    rewrite subst_tvar_in_typ_fresh_eq...
  - inst_cofinites_for trans_typ__all; intros;
    inst_cofinites_with X0; repeat rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2... 
    + apply s_in_subst_inv...
    + rewrite_env (((X0, □) :: θ2) ++ θ1).
      eapply H1; eauto...
      * intros. destruct_binds...
      * constructor...
      * simpl... apply trans_typ_weaken_cons...
Qed.


(* maybe only b=tvar is used *)
(* Lemma trans_typ_tvar_etvar : forall θ1 θ2 Aᵃ Aᵈ Tᵃ Tᵈ X b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  θ2 ++ (X , b) :: θ1 ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  d_mono_typ (ss_to_denv (θ2 ++ θ1)) Tᵈ ->
  θ1 ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  θ2 ++ (X , dbind_typ Tᵈ) :: θ1 ᵗ⫦ Aᵃ ⇝ {Tᵈ /ᵗ X} Aᵈ.
Proof.
  intros. generalize dependent Tᵃ. generalize dependent Tᵈ. 
  dependent induction H0; intros; simpl; destruct_eq_atom; eauto with Hdb_a_wl_red_completness.
  - apply trans_typ_binds_etvar; eauto. admit.
  - admit.
  - admit.
  - constructor. admit. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X0.
    admit.
Admitted. *)

Fixpoint num_arrow_in_typ (A : typ) : nat :=
  match A with
  | typ_arrow A1 A2 => 1 + num_arrow_in_typ A1 + num_arrow_in_typ A2
  | typ_all A => num_arrow_in_typ A
  | typ_union A1 A2 => min (num_arrow_in_typ A1) (num_arrow_in_typ A2)
  | typ_intersection A1 A2 => min (num_arrow_in_typ A1) (num_arrow_in_typ A2)
  | _ => 0
  end.

Lemma d_more_num_arr_open_typ_rec : forall A B n,
  num_arrow_in_typ (open_typ_wrt_typ_rec n B A) >= num_arrow_in_typ A.
Proof.
  intros. generalize dependent n. induction A; simpl; intros; try lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
  - specialize (IHA (S n)). lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
Qed.

Lemma d_more_num_arr_open_typ : forall A B,
  num_arrow_in_typ (open_typ_wrt_typ A B) >= num_arrow_in_typ A.
Proof.
  intros. unfold open_typ_wrt_typ. eapply d_more_num_arr_open_typ_rec.
Qed.

Lemma d_same_num_arr_open_typ_rec_tvar : forall A X n,
  num_arrow_in_typ (open_typ_wrt_typ_rec n `X A) = num_arrow_in_typ A.
Proof.
  intros. generalize dependent n. induction A; simpl; intros; try lia.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; auto.
    + auto.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
  - specialize (IHA (S n)). lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
Qed.

Lemma d_same_num_arr_open_typ_tvar : forall A X,
  num_arrow_in_typ (open_typ_wrt_typ A `X) = num_arrow_in_typ A.
Proof.
  intros. unfold open_typ_wrt_typ. eapply d_same_num_arr_open_typ_rec_tvar.
Qed.


Lemma d_sub_more_num_arrow_in_mono_typ : forall Ψ A B,
  Ψ ⊢ A <: B ->
  (d_mono_typ Ψ A -> num_arrow_in_typ A >= num_arrow_in_typ B) /\
  (d_mono_typ Ψ B -> num_arrow_in_typ B >= num_arrow_in_typ A).
Proof.
  intros. induction H; split; simpl; intros Hmono; try lia; 
    try solve [dependent destruction Hmono];
    try (intuition; auto with lia).
  - dependent destruction Hmono. intuition.
  - dependent destruction Hmono. intuition.
  - destruct IHd_sub. 
    apply H6 in Hmono.
    specialize (d_more_num_arr_open_typ A T). lia.
Qed.  



Lemma trans_typ_etvar_s_in_more_num_arrow' : forall θ Aᵃ Aᵈ X T,
  wf_ss θ ->
  binds X (dbind_typ T) θ ->
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  s_in X Aᵃ ->
  (num_arrow_in_typ Aᵈ) >= (num_arrow_in_typ T).
Proof.
  intros * Hwf Hbinds Htrans Hsin. dependent induction Htrans; simpl in *; dependent destruction Hsin; try lia.
  - apply wf_ss_etvar_tvar_false in Hbinds; auto. contradiction.
  - apply wf_ss_etvar_stvar_false in Hbinds; auto. contradiction.
  - unify_binds. auto.
  - apply IHHtrans1 in Hsin; auto. lia.
  - apply IHHtrans2 in Hsin; auto. lia.
  - inst_cofinites_by (L `union` L0) using_name X.
    rewrite <- d_same_num_arr_open_typ_tvar with (X:=X0).
    apply H1; eauto.
  - apply IHHtrans1 in Hsin1; auto. 
    apply IHHtrans2 in Hsin2; auto.
    lia.
  - apply IHHtrans1 in Hsin1; auto. 
    apply IHHtrans2 in Hsin2; auto.
    lia.
Qed.


Lemma trans_typ_etvar_s_in_more_num_arrow : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ X T,
  binds X (dbind_typ T) θ ->
  θ ᵗ⫦ (typ_arrow A1ᵃ A2ᵃ) ⇝ (typ_arrow A1ᵈ A2ᵈ) ->
  s_in X (typ_arrow A1ᵃ A2ᵃ) ->
  (num_arrow_in_typ (typ_arrow A1ᵈ A2ᵈ)) > (num_arrow_in_typ T).
Proof.
  intros. dependent destruction H0.
  dependent destruction H1.
  - eapply trans_typ_etvar_s_in_more_num_arrow' in H0_; eauto. simpl. lia.
  - eapply trans_typ_etvar_s_in_more_num_arrow' in H0_0; eauto. simpl. lia.
Qed.


Lemma trans_typ_tvar_etvar : forall θ1 θ2 Aᵃ Aᵈ Tᵃ Tᵈ X,
  θ2 ++ (X , dbind_tvar_empty) :: θ1 ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  d_mono_typ (ss_to_denv (θ2 ++ θ1)) Tᵈ ->
  θ1 ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  map (subst_tvar_in_dbind Tᵈ X) θ2 ++ (X , dbind_typ Tᵈ) :: θ1 ᵗ⫦ Aᵃ ⇝ {Tᵈ /ᵗ X} Aᵈ.
Proof with auto.
  intros. generalize dependent Tᵃ. generalize dependent Tᵈ. 
  dependent induction H; intros; simpl; destruct_eq_atom; eauto.
  - apply trans_typ_binds_etvar; eauto. 
    admit.
  - econstructor; auto. admit. admit.
  - assert (X ~ □ ∈ᵈ (θ2 ++ (X, □) :: θ1)) by auto.
    unify_binds.
  - apply trans_typ__stvar; auto.
    admit. admit.
  - admit.
  - constructor. admit.
  - constructor. admit.
  - constructor. admit.
  - inst_cofinites_for trans_typ__all; intros; 
    inst_cofinites_with X0...
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; eauto.
    rewrite_env (map (subst_tvar_in_dbind Tᵈ X) ((X0, □) :: θ2) ++ (X, dbind_typ Tᵈ) :: θ1).
    eapply H1; eauto.
    + simpl. admit.
Admitted.


Lemma trans_typ_tvar_etvar_cons : forall θ Aᵃ Aᵈ Tᵃ Tᵈ X,
  (X , dbind_tvar_empty) :: θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  d_mono_typ (ss_to_denv θ) Tᵈ ->
  θ ᵗ⫦ Tᵃ ⇝ Tᵈ ->
  (X , dbind_typ Tᵈ) :: θ ᵗ⫦ Aᵃ ⇝ {Tᵈ /ᵗ X} Aᵈ.
Proof.
  intros. rewrite_env ((map (subst_tvar_in_dbind Tᵈ X) nil) ++ (X ,  dbind_typ Tᵈ) :: θ). 
  eapply trans_typ_tvar_etvar; eauto.
Qed.


Ltac solve_right := 
  let Hcontra := fresh "Hcontra" in 
  right; intros Hcontra; inversion Hcontra.


#[local] Hint Constructors a_mono_typ : core.


Lemma a_mono_typ_dec : forall Γ A,
  ⊢ᵃʷ Γ ->
  a_wf_typ (awl_to_aenv Γ) A ->
  a_mono_typ (awl_to_aenv Γ) A \/ ~ a_mono_typ (awl_to_aenv Γ) A.
Proof.
  intros. dependent induction H0; auto; try solve [solve_right].  
  - right. unfold not. intros.
    dependent destruction H1.
    + unify_binds.
    + unify_binds. 
  - specialize (IHa_wf_typ1 _ H (eq_refl _)). 
    specialize (IHa_wf_typ2 _ H (eq_refl _)). 
    dependent destruction IHa_wf_typ1; dependent destruction IHa_wf_typ2.
    + left; auto.
    + right. unfold not. intros. dependent destruction H2. contradiction.
    + right. unfold not. intros. dependent destruction H2. contradiction.
    + right. unfold not. intros. dependent destruction H2. contradiction.
Qed.

Lemma trans_typ_subst_tvar_cons : forall θ Aᵃ Aᵈ Bᵃ Bᵈ X,
  (X , dbind_tvar_empty) :: θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⫦ Bᵃ ⇝ Bᵈ ->
  θ ᵗ⫦ {Bᵃ /ᵗ X} Aᵃ ⇝ {Bᵈ /ᵗ X} Aᵈ.
Proof.
  intros. rewrite_env (nil ++ θ). 
  eapply trans_typ_subst with (b:=dbind_tvar_empty); eauto.
  intros.
  apply trans_typ_wf_ss in H.
  dependent destruction H.
  rewrite wf_ss_ftvar_in_typ_upper with (θ:=θ); eauto.
Qed.

Lemma iuv_size_a_mono : forall Σ A,
  a_mono_typ Σ A ->
  iuv_size A = 0.
Proof.
  intros. induction H; simpl; lia.
Qed.

Lemma iuv_size_d_mono : forall Ψ A,
  d_mono_typ Ψ A ->
  iuv_size A = 0.
Proof.
  intros. induction H; simpl; lia.
Qed.

(* Lemma trans_typ_iuv_size_open : forall θ Aᵃ Aᵈ X,
  θ ᵗ⫦ Aᵃ ^ᵗ X ⇝ Aᵈ ^ᵗ X ->
  iuv_size (Aᵃ ^ᵗ X) = iuv_size (Aᵈ ^ᵗ X) ->
  iuv_size Aᵃ = iuv_size Aᵈ.
Proof.
  intros. simpl in *. lia.
Qed. *)

Lemma trans_typ_iuv_size : forall θ Aᵃ Aᵈ,
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  iuv_size Aᵃ = iuv_size Aᵈ.
Proof.
  intros θ Aᵃ Aᵈ Htrans. apply trans_typ_wf_ss in Htrans as Hwf.
  induction Htrans; simpl; auto.
  - eapply wf_ss_binds_monotyp in H0; auto.
    apply iuv_size_d_mono in H0. rewrite H0. simpl. reflexivity.
  - admit. (* TODO *)
Admitted.

Lemma trans_typ_exp_split_size_exp : forall Γ Ω θ eᵃ eᵈ,
  ⊢ᵃʷ Γ ->
  ⊢ᵈʷ Ω ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  θ ᵉ⫦ eᵃ ⇝ eᵈ ->
  exp_split_size (⌊ Γ ⌋ᵃ) eᵃ = exp_split_size (dwl_to_aenv Ω) eᵈ.
(* Proof.
  intros Γ Ω θ eᵃ eᵈ Hlc HwfΓ HwfΩ Htranswl Htranse.
  (* generalize dependent Ω. generalize dependent θ.  *)
  dependent induction HwfΓ; intros; simpl in *.
  - dependent destruction Htranswl. admit.
  - dependent destruction H4. dependent destruction H3. simpl.
    eapply IHa_wf_wl with (Ω := Ω) in H2 as He; eauto. admit.
    eapply trans_typ_iuv_size in H7 as Hiu. eauto.
  
  dependent destruction H2; auto. simpl. *)
Admitted.

#[local] Hint Resolve d_wf_wl_wf_env trans_wl_ss_binds_etvar_a_wl : core.

Lemma trans_wl_a_wl_binds_var_binds_d_wl_trans_typ' : forall θ Γ Ω x Aᵃ Aᵈ,
  ⊢ᵃʷ Γ ->
  ⊢ᵈʷ Ω ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds x (abind_var_typ Aᵃ) (awl_to_aenv Γ) ->
  binds x (dbind_typ Aᵈ) (dwl_to_denv Ω) ->
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  eapply trans_wl_a_wl_binds_var_binds_d_wl_and_trans in H2; eauto.
  destruct H2 as [Aᵈ' [Hbinds Htrans]].
  eapply binds_unique in H3; eauto. dependent destruction H3...
Qed.

Lemma trans_wl_a_wl_binds_var_binds_d_wl_trans_typ : forall θ Γ Ω x Aᵃ Aᵈ,
  ⊢ᵃʷ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds x (abind_var_typ Aᵃ) (awl_to_aenv Γ) ->
  binds x (dbind_typ Aᵈ) (dwl_to_denv Ω) ->
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ.
Proof.
  intros. eapply trans_wl_a_wf_wl_d_wf_wl in H0 as Hdwf; auto.
  eapply trans_wl_a_wl_binds_var_binds_d_wl_trans_typ'; eauto.
Qed.

#[local] Hint Constructors a_mono_typ : core.

Lemma trans_wl_d_mono_typ_a_mono_typ_no_etvar : forall θ Γ Ω A,
  ⊢ᵃʷ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  d_mono_typ (ss_to_denv θ) A ->
  a_mono_typ (awl_to_aenv Γ) A /\ forall X, binds X abind_etvar_empty (awl_to_aenv Γ) → X ∉ ftvar_in_typ A.
Proof with auto.
  intros. generalize dependent Γ. generalize dependent Ω.
  dependent induction H1; intros; simpl; try solve [intuition].
  - split... 
  - split... 
    + constructor. eapply trans_wl_ss_binds_tvar_a_wl; eauto. 
      apply binds_ss_to_denv_binds_ss...
    + intros. unfold not. intros. apply singleton_iff in H3. subst... 
      apply binds_ss_to_denv_binds_ss in H.
      eapply trans_wl_a_wl_binds_etvar_ss in H2; eauto.
      destruct H2 as [T].
      unify_binds; eauto.
  - split;
    specialize (IHd_mono_typ1 _ (eq_refl _) _ _ H H0);
    specialize (IHd_mono_typ2 _ (eq_refl _) _ _ H H0);
    simpl; intuition.
    apply union_iff in H6. inversion H6; eauto.
Qed.



Lemma trans_wl_aworklist_trailing_sub : forall Γ Ω θ A1 A2 B1 B2,
  ⊢ᵃʷ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  d_mono_typ (ss_to_denv θ) (typ_arrow A1 A2) ->
  d_mono_typ (ss_to_denv θ) (typ_arrow B1 B2) ->
  aworklist_trailing_sub Γ (work_sub A2 B2 ⫤ᵃ work_sub B1 A1 ⫤ᵃ Γ).
Proof.
  intros * Hwf Htrans Hmonoa Hmonob.
  destruct_mono_arrow.
  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in Hmonoa1; eauto.
  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in Hmonoa2; eauto.
  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in Hmonob1; eauto.
  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in Hmonob2; eauto.
  intuition.
Qed.

Lemma trans_typ_weaken_cons2 : forall θ X1 X2 b1 b2 Aᵃ Aᵈ,
  θ ᵗ⫦ Aᵃ ⇝ Aᵈ ->
  wf_ss ((X2, b2) :: (X1, b1) :: θ) ->
  (X2, b2) :: (X1, b1) :: θ ᵗ⫦ Aᵃ ⇝ Aᵈ.
Proof.
  intros. apply trans_typ_weaken_cons; auto. 
  dependent destruction H0; apply trans_typ_weaken_cons; auto.
Qed.

Lemma tvar_in_subst_typ_not_eq : forall A B X Y,
  X `notin` ftvar_in_typ B ->
  Y `in` ftvar_in_typ ({B /ᵗ X} A) ->
  X <> Y.
Proof.
  intros. unfold not. intros. subst.
  apply subst_tvar_in_typ_fresh_same in H0; auto.
Qed.

Ltac destruct_for_solve_mono := 
  destruct_mono_arrow;
  repeat
  match goal with
  | _ : _ |- d_mono_typ ?θ (typ_arrow ?A1 ?A2) =>
    constructor
  end.

Ltac solve_mono_typ :=
  destruct_for_solve_mono;
  match goal with 
  | H_1 : d_mono_typ (ss_to_denv ?θ) ?A,
    H_2: nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ |- d_mono_typ (dwl_to_denv ?Ω ) ?A =>
    eapply trans_wl_ss_mono_typ_d_wl_mono_typ; eauto
  | H_1 : a_mono_typ (awl_to_aenv ?Γ) ?Aᵃ,
    H_2: nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ,
    H_3: ?θ ᵗ⫦ ?Aᵃ ⇝ ?Aᵈ |- d_mono_typ (ss_to_denv ?θ) ?Aᵈ =>
    eapply trans_wl_a_mono_typ_d_mono_typ; eauto
  | H_1 : a_mono_typ (ss_to_aenv ?θ) ?Aᵃ,
    H_2: nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ,
    H_3: ?θ ᵗ⫦ ?Aᵃ ⇝ ?Aᵈ |- d_mono_typ (ss_to_denv ?θ) ?Aᵈ =>
    eapply trans_typ_a_mono_typ_d_mono_typ; eauto
 | H_1 : a_mono_typ (awl_to_aenv ?Γ) ?Aᵃ,
    H_2: nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ |- d_mono_typ (dwl_to_denv ?Ω ) ?Aᵈ =>
    eapply trans_wl_ss_mono_typ_d_wl_mono_typ with (θ:=θ) (Γ:=Γ); eauto; eapply trans_wl_a_mono_typ_d_mono_typ; eauto
  | _ : _ |- _ => idtac
  end.

Ltac solve_wf_typ_mono_to_wf :=
  destruct_mono_arrow;
  repeat
  match goal with
  | H_1 : d_mono_typ (ss_to_denv ?θ) ?A |- _ => 
    apply d_mono_typ_d_wf_typ in H_1
  | H_1 : a_mono_typ (ss_to_aenv ?θ) ?A |- _ => 
    apply a_mono_typ_wf in H_1
  end.

Ltac solve_wf_typ_preprocess :=
  try solve_wf_typ_mono_to_wf;
  match goal with
  | _ : _ |- d_wf_typ ?θ (typ_arrow ?A1 ?A2) =>
    constructor
  | _ : _ |- _ => idtac
  end.

Ltac solve_wf_typ := 
  solve_wf_typ_preprocess;
  match goal with
  | H_1 : a_wf_typ (awl_to_aenv ?Γ) ?Aᵃ,
    H_2: nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ,
    H_3: ?θ ᵗ⫦ ?Aᵃ ⇝ ?Aᵈ |- d_wf_typ (dwl_to_denv ?Ω) ?Aᵈ =>
    eapply trans_wl_a_wf_typ_d_wf_typ; eauto
  | H_1 : d_wf_typ (ss_to_denv ?θ) ?A,
    H_2: nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ |- dwl_to_denv ?Ω ⊢ ?A =>
    eapply trans_wl_ss_wf_typ_d_wf_typ; eauto
  | _ : _ |- _ => idtac
  end.

#[local] Hint Constructors a_mono_typ : core.

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp trans_wl_ss_mono_typ_d_wl_mono_typ trans_wl_d_wl_mono_typ_ss_mono_typ : core.

#[local] Hint Immediate trans_wl_ss_binds_tvar_a_wl trans_wl_ss_binds_stvar_a_wl trans_wl_ss_binds_etvar_a_wl : core.

#[local] Hint Resolve trans_wl_d_wf_typ_a_wf_typ trans_typ_refl trans_wl_a_wf_wl_d_wf_wl : core.

#[local] Hint Resolve trans_typ_weaken_cons2 : core.

Theorem a_wl_red_completeness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃʷ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with eauto.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros * Hwf Htrans;
    try destruct Htrans as [θ Htrans].
  - solve_awl_trailing_etvar.
  - solve_awl_trailing_etvar.
    constructor. apply IHd_wl_red...
    dependent destruction Hwf0...
  - solve_awl_trailing_etvar.
    constructor. eapply IHd_wl_red...
    dependent destruction Hwf0...
  - solve_awl_trailing_etvar.
    constructor. apply IHd_wl_red...
    dependent destruction Hwf0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction. 
    + constructor...
      apply IHd_wl_red...
      dependent destruction Hwf0...
 - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction. 
    + constructor...
      apply IHd_wl_red...
      dependent destruction Hwf0...
  - solve_awl_trailing_etvar.
    destruct_trans; destruct_a_wf_wl.
    + destruct (X0 == X).
      * subst...
      * eapply a_worklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=`X0) (Tᵈ:=typ_unit) in Htrans_et as Htransws... 
        destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
        eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2)...
        apply IHd_wl_red; eauto. eapply a_worklist_subst_wf_wl... 
    + eapply a_worklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=typ_unit) (Tᵈ:=typ_unit) in Htrans_et as Htransws... 
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2)...
      apply IHd_wl_red; eauto. eapply a_worklist_subst_wf_wl... 
    + eapply a_worklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=typ_unit) (Tᵈ:=typ_unit) in Htrans_et as Htransws... 
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      eapply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2)...
      apply IHd_wl_red; eauto. eapply a_worklist_subst_wf_wl... 
    + destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl... 
    + unify_binds.
    + apply a_worklist_subst_transfer_same_dworklist_rev_exist with (X:=X0) (T:=`X) (Tᵈ:=`X) 
        in Htrans_et as Htransws...
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      apply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
      * unfold not. intros. simpl in *. apply singleton_iff in H4. subst. apply wf_ss_etvar_tvar_false in H1; eauto.
      * apply IHd_wl_red; eauto. destruct_a_wf_wl. eapply a_worklist_subst_wf_wl; eauto.
      * destruct_a_wf_wl...
      * unfold not. intros. simpl in *. apply singleton_iff in H4. subst. apply wf_ss_etvar_tvar_false in H1; eauto.
    + exfalso. eapply wf_ss_tvar_stvar_false; eauto.
    + destruct_a_wf_wl... 
    + solve_binds_mono.
      dependent destruction Hmono.
      apply wf_ss_binds_monotyp in H1...
      apply binds_ss_to_denv_binds_ss in H4.
      apply wf_ss_tvar_stvar_false in H3... contradiction.
    + apply a_worklist_subst_transfer_same_dworklist_rev_exist with (X:=X0) (T:=`X) (Tᵈ:=`X) 
        in Htrans_et as Htransws...
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
      * unfold not. intros. simpl in *. apply singleton_iff in H4. subst. apply wf_ss_etvar_tvar_false in H3; eauto.
      * apply IHd_wl_red; eauto. destruct_a_wf_wl. eapply a_worklist_subst_wf_wl; eauto.
      * destruct_a_wf_wl...
      * unfold not. intros. simpl in *. apply singleton_iff in H4. subst. apply wf_ss_etvar_tvar_false in H3; eauto.
    + solve_binds_mono.
      dependent destruction Hmono.
      apply binds_ss_to_denv_binds_ss in H4.
      apply wf_ss_tvar_stvar_false in H4... contradiction.
    + destruct (X0 == X1)...
      * subst. destruct_a_wf_wl... 
      * apply a_worklist_subst_transfer_same_dworklist_rev_exist with (X:=X0) (T:=`X1) (Tᵈ:=`X) 
          in Htrans_et as Htransws...
        destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
        apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
        -- apply IHd_wl_red; eauto. destruct_a_wf_wl. eapply a_worklist_subst_wf_wl; eauto.
        -- destruct_a_wf_wl...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    (* ^X < ^Y *)
    + apply wf_ss_binds_monotyp in H1 as Hmonoa...
      apply wf_ss_binds_monotyp in H3 as Hmonob...
      destruct_mono_arrow.
      apply trans_wl_a_wf_wl_d_wf_wl in Htrans as Hwfd...
      destruct (X0 == X).
      * subst. assert ((work_sub A2 B2 ⫤ᵃ work_sub B1 A1 ⫤ᵃ Γ0) ⟶ᵃʷ⁎⋅)...
        apply IHd_wl_red...
        -- destruct_a_wf_wl. destruct_d_wl_wf. eauto. 
           repeat (constructor; simpl; auto); eauto.
        -- exists θ0; (repeat constructor; auto); apply trans_typ_refl...
        -- constructor...
           eapply a_wl_red_aworklist_trailing_sub_weaken with (Γ:=work_sub A2 B2 ⫤ᵃ work_sub B1 A1 ⫤ᵃ Γ0); eauto.
           eapply trans_wl_aworklist_trailing_sub; eauto. destruct_a_wf_wl...
      * destruct_d_wl_wf.
        destruct_a_wf_wl.
        apply d_wl_red_sound in H...
        dependent destruction H.
        dependent destruction H0; simpl in *...
        apply d_sub_mono_refl in H; solve_mono_typ. subst.
        apply d_sub_mono_refl in H0; solve_mono_typ. subst.
        -- eapply a_worklist_subst_transfer_same_dworklist_rev_exist with (T:=`X0) (Tᵈ:= typ_arrow A1 B2) 
              in Htrans_et as Htransws... 
           destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
           apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
           eapply a_wl_red_aworklist_trailing_sub_weaken with (Γ:=work_sub B2 B2 ⫤ᵃ work_sub A1 A1 ⫤ᵃ (subst_tvar_in_aworklist ` X0 X Γ2 ⧺ Γ1)); eauto.
           ++ eapply trans_wl_aworklist_trailing_sub...
              eapply a_worklist_subst_wf_wl...
           ++ apply IHd_wl_red; auto...
              ** assert (Hnotin: X `notin` ftvar_in_typ (typ_arrow A1 B2)).
                 { apply wf_ss_typ_no_etvar with (A:=typ_arrow A1 B2) in H5... }
                 simpl in Hnotin.
                 repeat (constructor; simpl; auto); try 
                 eapply a_worklist_subst_wf_typ; eauto.
                 eapply a_worklist_subst_wf_wl...
              ** exists θ'. repeat (constructor; auto); apply trans_typ_refl; auto;
                 eapply trans_wl_d_wf_typ_ss_wf_typ; eauto.
    (* A -> B > ^X *)
    + apply wf_ss_binds_monotyp in H2 as Hmonob...
      destruct_a_wf_wl.
      assert (a_wf_typ (awl_to_aenv Γ0) (typ_arrow A1ᵃ A2ᵃ)) by auto.
      assert ( ~ s_in X (typ_arrow A1ᵃ A2ᵃ)). {
        unfold not. intros Hcontra.
        eapply trans_typ_etvar_s_in_more_num_arrow in Hcontra...
        apply d_wl_red_sound in H.
        dependent destruction H. dependent destruction H0. simpl in *.
        assert (dwl_to_denv Ω ⊢ typ_arrow A1 A2 <: typ_arrow B1 B2) by auto.
        apply d_sub_more_num_arrow_in_mono_typ in H6 as [Harr1 Harr2].
        assert (d_mono_typ (dwl_to_denv Ω) (typ_arrow B1 B2)) by solve_mono_typ. 
        apply Harr2 in H6. simpl in *. lia.
        repeat (constructor; simpl; auto); solve_wf_typ...
      }
      apply a_mono_typ_dec in H0 as Hmono... inversion Hmono.
      * destruct_d_wl_wf.
        destruct_a_wf_wl.
        apply d_wl_red_sound in H.
        destruct_d_wl_del_red; simpl in *.
        rename_typ_rev. 
        assert (d_mono_typ (ss_to_denv θ0) A1) by solve_mono_typ.
        assert (d_mono_typ (ss_to_denv θ0) A2) by solve_mono_typ.
        apply d_sub_mono_refl in H; solve_mono_typ. subst.
        apply d_sub_mono_refl in H0; solve_mono_typ. subst.
        rename_typ_rev. 
        assert (X `notin` ftvar_in_typ (typ_arrow A1 B2)) by (eapply etvar_bind_no_etvar; eauto).
        assert (X `notin` ftvar_in_typ (typ_arrow A1ᵃ B2ᵃ)). {unfold not. intros. eapply a_mono_typ_in_s_in in H0; eauto. }
        simpl in *.
        eapply a_worklist_subst_transfer_same_dworklist_rev_exist with (T:=typ_arrow A1ᵃ B2ᵃ) (Tᵈ:= typ_arrow A1 B2) 
              in Htrans_et as Htransws... 
        ++ destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
           apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto. 
           eapply a_wl_red_aworklist_trailing_sub_weaken with 
            (Γ:=work_sub B2 B2 ⫤ᵃ work_sub A1 A1 ⫤ᵃ (subst_tvar_in_aworklist (typ_arrow A1ᵃ B2ᵃ) X Γ2 ⧺ Γ1)); eauto.
           ** eapply trans_wl_aworklist_trailing_sub; eauto. 
              eapply a_worklist_subst_wf_wl...
           ** apply IHd_wl_red...
              ---  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in H7; eauto.
              eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in H8; eauto. intuition.
              repeat (constructor; simpl; eauto using a_worklist_subst_wf_wl); eapply a_worklist_subst_wf_typ; eauto.
              --- exists θ'. repeat (constructor; auto); apply trans_typ_refl...
        ++ destruct_d_wl_wf. 
           dependent destruction Hmonob.
          repeat (constructor; simpl; auto); solve_wf_typ...
      * inst_cofinites_for a_wl_red__sub_arrow2... 
        destruct_mono_arrow.
        intros.
        assert (nil ⫦ (work_sub (typ_arrow ({typ_arrow ` X1 ` X2 /ᵗ X} A1ᵃ) ({typ_arrow ` X1 ` X2 /ᵗ X} A2ᵃ)) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) ⇝
                      (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2) ⫤ᵈ Ω) ⫣ ((X2, dbind_typ B2) :: (X1, dbind_typ B1) :: θ0)).
        { repeat (constructor; simpl; auto). 
          eapply trans_typ_etvar_subst_same_ss... econstructor... apply trans_typ_binds_etvar...
          eapply trans_typ_etvar_subst_same_ss... econstructor... apply trans_typ_binds_etvar... 
        }
        dependent destruction H8...
        assert (aworklist_subst (work_sub (typ_arrow A1ᵃ A2ᵃ) ` X  ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) X (typ_arrow ` X1 ` X2) 
                                Γ2 (work_sub (typ_arrow A1ᵃ A2ᵃ) ` X  ⫤ᵃ Γ3)) by auto...
        destruct_trans_wl.
        dependent destruction H11.
        eapply a_worklist_subst_transfer_same_dworklist_rev in H11 as Htransws; eauto.
        destruct Htransws as [θ' [Htransws [Hbinds Hwfss]]]; auto.
        -- simpl. destruct_eq_atom.
           simpl in *. destruct_eq_atom. 
           constructor. apply IHd_wl_red; eauto.
           ++ assert (binds X1 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2)))
                by (eapply a_worklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              assert (binds X2 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2)))
                by (eapply a_worklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              repeat (constructor; simpl; eauto)...
              ** eapply a_worklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto.
                 constructor... simpl. apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons...
              ** eapply a_worklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto.
                 constructor... simpl. apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons...
              ** eapply a_worklist_subst_wf_wl with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0))...
           ++ exists θ'... 
              repeat (constructor; simpl; auto).
              ** apply Hbinds... 
              ** apply trans_typ_reorder with (θ:=((X2, dbind_typ B2) :: (X1, dbind_typ B1) :: θ0))... 
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto... constructor...
              ** apply trans_typ_reorder with (θ:=((X2, dbind_typ B2) :: (X1, dbind_typ B1) :: θ0))...
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto... constructor...
              ** apply Hbinds; auto. 
        -- repeat (constructor; simpl; eauto). 
        -- constructor...
    (* ^X < A -> B *)
    + rename_typ_rev.
      apply wf_ss_binds_monotyp in H1 as Hmonob...
      destruct_a_wf_wl.
      assert (a_wf_typ (awl_to_aenv Γ0) (typ_arrow B1ᵃ B2ᵃ)) by auto.
      assert ( ~ s_in X (typ_arrow B1ᵃ B2ᵃ)). {
        unfold not. intros Hcontra.
        eapply trans_typ_etvar_s_in_more_num_arrow in Hcontra...
        apply d_wl_red_sound in H.
        dependent destruction H. dependent destruction H0. simpl in *.
        assert (dwl_to_denv Ω ⊢ typ_arrow A1 A2 <: typ_arrow B1 B2) by auto.
        apply d_sub_more_num_arrow_in_mono_typ in H6 as [Harr1 Harr2].
        assert (d_mono_typ (dwl_to_denv Ω) (typ_arrow A1 A2)) by (eapply trans_wl_ss_mono_typ_d_wl_mono_typ; eauto).
        apply Harr1 in H6.
        simpl in *. lia.
        repeat (constructor; simpl; auto); solve_mono_typ; solve_wf_typ...
      }
      (* ***, needs to know X notin (A1 -> A2) *)
      apply a_mono_typ_dec in H3 as Hmono... inversion Hmono.
      * destruct_d_wl_wf.
        destruct_a_wf_wl.
        apply d_wl_red_sound in H.
        destruct_mono_arrow.
        destruct_d_wl_del_red; simpl in *.
        rename_typ_rev.
        assert (d_mono_typ (ss_to_denv θ0) B1) by solve_mono_typ.
        assert (d_mono_typ (ss_to_denv θ0) B2) by solve_mono_typ.
        apply d_sub_mono_refl in H; solve_mono_typ. subst.
        apply d_sub_mono_refl in H0; solve_mono_typ. subst.
        rename_typ_rev.
        assert (X `notin` ftvar_in_typ (typ_arrow A1 B2)) by (eapply etvar_bind_no_etvar; eauto).
        assert (X `notin` ftvar_in_typ (typ_arrow A1ᵃ B2ᵃ)). {unfold not. intros. eapply a_mono_typ_in_s_in in H0; eauto. }
        simpl in *.
        eapply a_worklist_subst_transfer_same_dworklist_rev_exist with (T:=typ_arrow A1ᵃ B2ᵃ) (Tᵈ:= typ_arrow A1 B2) 
              in Htrans_et as Htransws... 
        ++ destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
           apply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2); eauto. 
           eapply a_wl_red_aworklist_trailing_sub_weaken with 
            (Γ:=work_sub B2 B2 ⫤ᵃ work_sub A1 A1 ⫤ᵃ (subst_tvar_in_aworklist (typ_arrow A1ᵃ B2ᵃ) X Γ2 ⧺ Γ1)); eauto.
           ** eapply trans_wl_aworklist_trailing_sub; eauto. 
              eapply a_worklist_subst_wf_wl...
           ** apply IHd_wl_red...
              --- eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in H6; eauto.
                  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar in H7; eauto. intuition.
                  repeat (constructor; simpl; eauto using a_worklist_subst_wf_wl); eapply a_worklist_subst_wf_typ; eauto.
              --- exists θ'. repeat (constructor; auto); apply trans_typ_refl...
        ++ destruct_d_wl_wf. repeat (constructor; simpl; auto); solve_wf_typ...
      * inst_cofinites_for a_wl_red__sub_arrow1... 
        destruct_mono_arrow.
        intros.
        rename_typ_rev.
        assert (nil ⫦ (work_sub ` X (typ_arrow ({typ_arrow ` X1 ` X2 /ᵗ X} B1ᵃ) ({typ_arrow ` X1 ` X2 /ᵗ X} B2ᵃ)) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) ⇝
                      (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2)  ⫤ᵈ Ω) ⫣ ((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0)).
        { repeat (constructor; simpl; auto).
          eapply trans_typ_etvar_subst_same_ss... econstructor... apply trans_typ_binds_etvar...
          eapply trans_typ_etvar_subst_same_ss... econstructor... apply trans_typ_binds_etvar... 
        }
        dependent destruction H8.
        assert (aworklist_subst (work_sub ` X (typ_arrow B1ᵃ B2ᵃ) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) X (typ_arrow ` X1 ` X2) 
                Γ2 (work_sub ` X (typ_arrow B1ᵃ B2ᵃ) ⫤ᵃ Γ3)) by auto.
        destruct_trans_wl.
        dependent destruction H11.
        eapply a_worklist_subst_transfer_same_dworklist_rev with (Ω:=Ω) in H11 as Htransws; eauto.
        destruct Htransws as [θ' [Htransws [Hbinds Hwfss]]]; auto.
        -- simpl. destruct_eq_atom.
           simpl in *. destruct_eq_atom. 
           constructor. apply IHd_wl_red; eauto.
           ++ assert (binds X1 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2)))
                by (eapply a_worklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              assert (binds X2 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2))) 
                by (eapply a_worklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              repeat (constructor; simpl; eauto)...
              ** eapply a_worklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto.
                 constructor... simpl. apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons...
              ** eapply a_worklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto.
                 constructor... simpl. apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons...
              ** eapply a_worklist_subst_wf_wl with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0))...
           ++ exists θ'... 
              repeat (constructor; simpl; auto).
              ** apply trans_typ_reorder with (θ:=((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0))... 
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto... constructor...
              ** apply Hbinds... 
              ** apply Hbinds... 
              ** apply trans_typ_reorder with (θ:=((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0))...
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto... constructor...
        -- repeat (constructor; simpl; eauto).
        -- constructor...
    (* A1 -> B1 < A2 -> B2 *)
    + destruct_a_wf_wl...
      constructor...
      apply IHd_wl_red...
      exists θ0...
  - solve_awl_trailing_etvar. 
    destruct_trans; try solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl. 
      dependent destruction H5.
      dependent destruction H7.
      pick fresh X and apply a_wl_red__sub_all. 
      inst_cofinites_with X.
      apply H0; auto.
      * constructor... constructor...
        simpl in *. apply a_wf_typ_tvar_stvar_cons...
        simpl in *. apply a_wf_typ_tvar_stvar_cons...
      * exists ((X , dbind_stvar_empty) :: θ0)...
        constructor...
        constructor...
        -- apply trans_typ_tvar_stvar_cons...
        -- apply trans_typ_tvar_stvar_cons...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl. dependent destruction H7. 
      pick fresh X and apply a_wl_red__sub_alll.
      inst_cofinites_with X.
      * eapply trans_typ_neq_all_rev...
      * eapply trans_typ_neq_intersection_rev...
      * eapply trans_typ_neq_union_rev...
      * inst_cofinites_with X.
        apply IHd_wl_red.
        -- repeat (constructor; auto).  
           ++ simpl in *. apply a_wf_typ_tvar_etvar_cons... 
           ++ apply a_wf_typ_weaken_cons...
        -- exists ((X, dbind_typ T) :: θ0).
           repeat (constructor; auto)...
           ++ eapply trans_typ_tvar_etvar_cons with (θ:=θ0) (Tᵃ:=T) (Tᵈ:=T) in H5; eauto...
              rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H5...
           ++ rewrite_env (nil ++ (X ~ dbind_typ T) ++ θ0). 
              apply trans_typ_weaken. auto.
              constructor...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor. apply IHd_wl_red; eauto.
      destruct_a_wf_wl...
      exists θ0...      
  - solve_awl_trailing_etvar. 
    + destruct_trans.
      * solve_binds_nonmono_contradiction.
      * constructor. apply IHd_wl_red; eauto.
        destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    + destruct_trans.
      * solve_binds_nonmono_contradiction.
      * apply a_wl_red__sub_intersection3. apply IHd_wl_red; eauto.
        destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor. apply IHd_wl_red; eauto.
      destruct_a_wf_wl...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + eapply a_wl_red__sub_union2. apply IHd_wl_red; eauto.
      destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor. apply IHd_wl_red; eauto.
      destruct_a_wf_wl...
      exists θ0...

  (** check **)
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl...
    constructor. 
    apply IHd_wl_red...
  (* λ x. e <= A -> B *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl. inst_cofinites_for a_wl_red__chk_absetvar; intros.
      eapply trans_wl_ss_binds_etvar_a_wl; eauto.
      inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
      assert (nil ⫦ work_check (eᵃ ^ᵉₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0 ⇝
                    work_check (e ^ᵉₑ exp_var_f x) A2 ⫤ᵈ x ~ᵈ A1;ᵈ Ω ⫣ (X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0).
      { apply wf_ss_binds_monotyp in H3 as Hmono...
        dependent destruction Hmono.
        repeat (constructor; auto); simpl in *.
        eapply trans_exp_weaken_cons...
        eapply trans_exp_weaken_cons...
      }
      eapply a_worklist_subst_transfer_same_dworklist_rev in H10 as Htransws...
      destruct Htransws as [θ' [Htransws [Hbinds Hwfss]]]...
      * apply H0; eauto. eapply a_worklist_subst_wf_wl with 
        (Γ:=(work_check (eᵃ ^ᵉₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0))... 
        repeat (econstructor; simpl; auto).
        eapply a_wf_exp_var_binds_another_cons with (A1:=T)...
        rewrite_env (x ~ abind_var_typ T ++ ((X2, abind_etvar_empty) :: (X1 ~ abind_etvar_empty)) ++ awl_to_aenv Γ0).
        apply a_wf_exp_weaken...
      * repeat (econstructor; simpl; auto).
        apply a_wf_exp_var_binds_another_cons with (A1:=T)...
        rewrite_env ((x ~ abind_var_typ T) ++ ((X2, abind_etvar_empty) :: (X1 ~ abind_etvar_empty)) ++ awl_to_aenv Γ0).
        apply a_wf_exp_weaken...
      * simpl... constructor...
      * constructor...
    + destruct_a_wf_wl. pick fresh x and apply a_wl_red__chk_absarrow.
      inst_cofinites_with x.
      eapply H0.
      * repeat constructor... 
        apply a_wf_exp_var_binds_another_cons with (A1:=T)...
        apply a_wf_typ_weaken_cons...
      * exists θ0. constructor...
  (* λx. e ⇐ ⊤ *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl.
      pick fresh x and apply a_wl_red__chk_abstop. 
      inst_cofinites_with x.
      apply H0.
      * repeat (constructor; auto). 
        simpl. apply a_wf_exp_var_binds_another_cons with (A1:=T)...
      * exists θ0. constructor...
  (* e ⇐ A1 ⊓ A2 *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + apply a_wl_red__chk_inter.
      apply IHd_wl_red...
      destruct_a_wf_wl...
      exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + apply a_wl_red__chk_union1.
      apply IHd_wl_red...
      destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + apply a_wl_red__chk_union2.
      apply IHd_wl_red...
      destruct_a_wf_wl...

  (* infer *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl.
    econstructor; eauto.
    apply IHd_wl_red; auto...
    + repeat (constructor; simpl; auto).
      eapply a_wf_wl_a_wf_bind_typ...
    + exists θ0...
      repeat constructor...
      eapply trans_wl_a_wl_binds_var_binds_d_wl_trans_typ; eauto.
  - solve_awl_trailing_etvar.
    destruct_trans.
    constructor.
    apply IHd_wl_red...
    + destruct_a_wf_wl...
    + exists θ0...
  (* Λ a. e : A => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans. destruct_a_wf_wl.
    destruct bᵃ.
    pick fresh X and apply a_wl_red__inf_tabs.
    inst_cofinites_with X.
    repeat rewrite open_body_wrt_typ_anno in H1.
    dependent destruction H1.
    apply H0.
    + dependent destruction H4. 
      dependent destruction H6.
      repeat (constructor; simpl; auto).
      replace (open_typ_wrt_typ_rec 0 ` X A0) with (open_typ_wrt_typ A0 ` X) in * by auto.
      inst_cofinites_for a_wf_typ__all. intros... 
      * apply s_in_rename with (Y:=X0) in H5. 
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H5...
      * intros. apply a_wf_typ_rename_tvar_cons with (Y:=X0) in H6.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H6...
    + exists ((X, dbind_tvar_empty) :: θ0). 
      repeat constructor...
      * inst_cofinites_for trans_typ__all; intros.
        -- dependent destruction H4...
           replace (open_typ_wrt_typ_rec 0 ` X A0) with (open_typ_wrt_typ A0 ` X) in * by auto.
           apply s_in_rename with (Y:=X0) in H5. rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H5...
        -- apply trans_typ_rename_tvar_cons with (X':=X0) in H2...
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
  - solve_awl_trailing_etvar.
    destruct_trans...
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...
  (* λ x. e => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__inf_abs_mono; auto.
    intros.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    apply H1.
    + repeat (constructor; simpl; eauto).
      * eapply a_wf_exp_var_binds_another_cons with (A1:=T)...
        rewrite_env (x ~ abind_var_typ T ++ ((X2, abind_etvar_empty) :: (X1 ~ abind_etvar_empty)) ++ awl_to_aenv Γ0).
        apply a_wf_exp_weaken...
      * rewrite_env (nil ++ ((X2, abind_etvar_empty) :: (X1 ~ abind_etvar_empty)) ++ awl_to_aenv Γ0). 
        apply a_wf_conts_weaken... 
    + exists ((X2 , dbind_typ T2) :: (X1 , dbind_typ T1) :: θ0)...
      dependent destruction H...
      assert (d_mono_typ (ss_to_denv θ0) T2) by eauto.
      assert (d_mono_typ (ss_to_denv θ0) T1) by eauto.
      assert (Hwfss: wf_ss θ0) by (now eapply trans_wl_wf_ss in Htrans_et).
      repeat (constructor; eauto).
      * apply trans_conts_weaken_cons... apply trans_conts_weaken_cons...
      * apply trans_exp_weaken_cons... apply trans_exp_weaken_cons...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...
    erewrite trans_typ_exp_split_size_exp with (Ω := Ω) (eᵈ := e1); eauto.
    exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...

  (* inftapp *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor.
      destruct_a_wf_wl...
      apply IHd_wl_red...
      * rename_typ_rev. 
        repeat (constructor; auto).
        apply a_wf_typ_all_open...
      * exists θ0. constructor...
        constructor...
        rename_typ_rev.
        pick fresh X. inst_cofinites_with X.
        erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2; eauto...
        erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2 with (A:=A); eauto...
        eapply trans_typ_subst_tvar_cons with (θ:=θ0) in H1; auto; eauto.
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor.
      apply IHd_wl_red...
      destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl...
      constructor... 
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl...
      apply a_wl_red__inftapp_inter2...
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl...
      constructor...
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl...
      constructor...
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl...
      constructor...
      apply IHd_wl_red...

  (* infabs *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + inst_cofinites_for a_wl_red__infabs_etvar.
      * eapply trans_wl_ss_binds_etvar_a_wl; eauto. 
      * intros.
        apply wf_ss_binds_monotyp in H1 as Hmono...
        dependent destruction Hmono.
        assert (exists Γ2', Γ2 = aworklist_conswork Γ2' (work_infabs (typ_arrow ` X1 ` X2) cdᵃ )).
        { dependent destruction H5. eauto. }
        destruct H6 as [Γ2' Heq]. subst.
        simpl. destruct_eq_atom.
        constructor.
        apply IHd_wl_red...
        -- dependent destruction H5. destruct_a_wf_wl...
           assert (binds X1 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ2' ⧺ Γ2))). {
              eapply a_worklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)) (b:=abind_etvar_empty); simpl in *...
           }
           assert (binds X2 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ2' ⧺ Γ2))). {
              eapply a_worklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)) (b:=abind_etvar_empty); simpl in *...
           }
           repeat (constructor; auto).
           ++ eapply a_worklist_subst_wf_contd_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); simpl in *; eauto...
              constructor...
              rewrite_env (nil ++ ((X2 , abind_etvar_empty) :: (X1 ~ abind_etvar_empty)) ++ awl_to_aenv Γ0).
              apply a_wf_contd_weaken...
           ++ eapply a_worklist_subst_wf_wl with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto. simpl...
        -- apply a_worklist_subst_transfer_same_dworklist_rev with 
             (Ω := (work_infabs (typ_arrow A B) cd ⫤ᵈ Ω)%dworklist) 
             (Tᵈ := typ_arrow A B)
             (θ := ((X2, dbind_typ B) :: (X1, dbind_typ A) :: θ0))
          in H5; simpl...  
          destruct H5 as [θ'' [Htransws [Hbinds Hwfss]]].    
          ++ exists θ''. simpl in *. destruct_eq_atom. auto.
             dependent destruction H. 
             dependent destruction Htransws.
             destruct_trans...
          ++ destruct_a_wf_wl. repeat (constructor; simpl; eauto).
             rewrite_env (nil ++ ((X2 , abind_etvar_empty) :: (X1 ~ abind_etvar_empty)) ++ (awl_to_aenv Γ0)).
             apply a_wf_contd_weaken...        
          ++ repeat (constructor; auto).
          ++ repeat (constructor; auto).  
             eapply trans_contd_weaken_cons... eapply trans_contd_weaken_cons...
          ++ constructor. 
             apply trans_typ_binds_etvar...
             apply trans_typ_binds_etvar...
    + destruct_a_wf_wl... 
      constructor...
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + econstructor. constructor.
      destruct_a_wf_wl... 
      apply IHd_wl_red...
      exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl. dependent destruction H4. 
      pick fresh X and apply a_wl_red__infabs_all.
      inst_cofinites_with X.
      apply IHd_wl_red. 
      * repeat (constructor; auto). 
        simpl in *. eapply a_wf_typ_tvar_etvar_cons...
        simpl. rewrite_env (nil ++ (X ~ abind_etvar_empty) ++ awl_to_aenv Γ0).
           apply a_wf_contd_weaken...
      * exists ((X, dbind_typ T)::θ0).
        repeat (constructor; eauto)...
        -- eapply trans_typ_tvar_etvar_cons with (θ:=θ0) (Tᵃ:=T) (Tᵈ:=T) in H2; eauto...
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
        -- apply trans_contd_weaken_cons; auto. constructor... 
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor...
      destruct_a_wf_wl...
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + apply a_wl_red__infabs_inter2.
      apply IHd_wl_red...
      destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl...
      constructor...
      apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    dependent destruction H0.
    destruct_trans.
    destruct_a_wf_wl...
    constructor...
    apply IHd_wl_red...
    exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl...
    constructor...
    apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl...
    constructor...
    apply IHd_wl_red...
    exists θ0...

  (* apply *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    eapply trans_apply_conts in H as Hacs; eauto.
    destruct Hacs as [wᵃ [Hacs Htransw]].
    eapply a_wl_red__applys with (w:=wᵃ)...
    apply IHd_wl_red; auto.
    destruct_a_wf_wl. constructor... eapply a_wf_work_apply_conts...
    exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    eapply trans_apply_contd in H as Hacd; eauto.
    destruct Hacd as [wᵃ [Hacd Htransw]].
    eapply a_wl_red__applyd with (w:=wᵃ)...
    apply IHd_wl_red; auto.
    destruct_a_wf_wl. constructor... eapply a_wf_work_apply_contd with (A:=Aᵃ)...
    exists θ0...
Admitted.
