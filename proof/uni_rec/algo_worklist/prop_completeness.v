Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import Lia.
Require Import List.


Require Import uni_rec.notations.
Require Import uni_rec.prop_basic.
Require Import uni_rec.decl.prop_basic.
Require Import uni_rec.decl.prop_subtyping.
Require Import uni_rec.decl_worklist.prop_equiv.
Require Import uni_rec.algo_worklist.def_extra.
Require Import uni_rec.algo_worklist.prop_basic.
Require Import uni_rec.algo_worklist.transfer.
Require Import uni_rec.ltac_utils.

Ltac destruct_trans_wl :=
  match goal with 
  | H : trans_worklist ?θ ?Γ (dworklist_cons_work ?Ω ?w) ?θ' |- _ => dependent destruction H
  end.

Ltac destruct_trans' :=
  lazymatch goal with
  | H : trans_work ?θ ?wᵃ (?wᵈ _) |- _ => dependent destruction H
  | H : trans_work ?θ ?wᵃ (?wᵈ _ _) |- _ => dependent destruction H
  | H : trans_work ?θ ?wᵃ (?wᵈ _ _ _) |- _ => dependent destruction H
  | H : trans_conts ?θ ?wᵃ (?C_CS _) |- _ => dependent destruction H
  | H : trans_conts ?θ ?wᵃ (?C_CS _ _) |- _ => dependent destruction H
  | H : trans_contd ?θ ?wᵃ (?C_CD _ _) |- _ => dependent destruction H
  | H : trans_contd ?θ ?wᵃ (?C_CD _ _ _) |- _ => dependent destruction H
  | H : trans_exp ?θ ?eᵃ (open_exp_wrt_exp _ _) |- _ => fail
  | H : trans_exp ?θ ?eᵃ exp_unit |- _ => dependent destruction H
  | H : trans_exp ?θ ?eᵃ exp_rcd_nil |- _ => dependent destruction H
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
(* Open Scope abind_scope. *)

#[local] Hint Resolve wf_ss_uniq trans_typ_wf_ss trans_wl_wf_ss : core.


Lemma wf_ss_etvar_bind_another : forall θ1 θ2 X T1 T2,
  wf_ss (θ2 ++ (X, dbind_typ T1) :: θ1) ->
  ⌈ θ1 ⌉ᵈ ᵗ⊢ᵈₘ T2 ->
  wf_ss (θ2 ++ (X, dbind_typ T2) :: θ1).
Proof.
  intros. induction θ2; auto.
  - dependent destruction H. constructor; auto.
  - destruct a; destruct d; dependent destruction H; try solve [constructor; auto].
    + simpl. constructor; auto.
      erewrite <- wf_ss_etvar_same_denv in H1; eauto.
      erewrite <- wf_ss_etvar_same_denv; eauto.
Qed.

Lemma wf_ss_late_dom_notin_ftver_bind_typ : forall θ1 θ2 X T,
  wf_ss (θ2 ++ (X, dbind_typ T) :: θ1) ->
  (forall Y, Y `in` dom θ2 -> Y ∉ ftvar_in_typ T).
Proof.
  intros. assert (wf_ss ((X, dbind_typ T) :: θ1)) by 
      (eapply wf_ss_strengthen_app; eauto).
  eapply wf_ss_binds_mono_typ in H1; eauto.
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


Corollary a_wf_wwl_two_etvar_neq1 : forall X1 X2 b1 b2 Γ1 Γ2,
  ⊢ᵃʷ (X2 ~ᵃ b2; Γ2 ⧺ X1 ~ᵃ b1; Γ1) ->
  X1 <> X2.
Proof.
  intros.
  replace (aworklist_cons_var (Γ2 ⧺ (aworklist_cons_var Γ1 X1 b1)) X2 b2) with 
     ((aworklist_cons_var Γ2 X2 b2) ⧺ (aworklist_cons_var Γ1 X1 b1)) in H by auto.
  eapply a_wf_wwl_tvar_notin_remaining in H.
  simpl in H. fsetdec.
Qed.

Corollary a_wf_wwl_two_etvar_neq2 : forall X1 X2 b1 b2 Γ1 Γ2,
  ⊢ᵃʷ (X2 ~ᵃ b2; Γ2 ⧺ X1 ~ᵃ b1; Γ1) ->
  X2 <> X1.
Proof.
  intros. unfold not. intros.
  apply a_wf_wwl_two_etvar_neq1 in H. subst. contradiction.
Qed.

#[local] Hint Resolve a_wf_wwl_two_etvar_neq1 a_wf_wwl_two_etvar_neq2 : core.

Lemma d_mono_typ_strengthen : forall θ X b T,
  wf_ss ((X, b) :: θ) ->
  ⌈ (X, b) :: θ ⌉ᵈ ᵗ⊢ᵈₘ T ->
  X ∉ ftvar_in_typ T ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ T.
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
  ⌈ θ2 ++ (X, dbind_typ T1) :: θ1 ⌉ᵈ ᵗ⊢ᵈₘ T2 ->
  ⌈ θ1 ⌉ᵈ ᵗ⊢ᵈₘ T1 ->
  (∀ Y : atom, Y `in` ftvar_in_typ T2 → Y `in` ftvar_in_typ T1) ->
  ⌈ θ1 ⌉ᵈ ᵗ⊢ᵈₘ T2.
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



Lemma trans_typ_tvar_stvar_notin : forall θ X1 X2 T Tᵈ Γ1 Γ2 Ω b,
  b = □ \/ b = ■ ->
  (X2, b) :: θ ᵗ⊩ T ⇝ Tᵈ -> 
  (X2, b) :: θ ᵗ⊩ ` X1 ⇝ Tᵈ ->
  nil ⊩ Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ Γ1 ⇝ Ω ⫣ θ ->
  X2 ∉ ftvar_in_typ T.
Proof.
  intros.   
  apply trans_wl_split in H2. destruct H2 as [Ω1 [Ω2 [θ'' [Heq [Htrans1 Htrans2]]]]]. subst.
  apply trans_wl_split_ss in Htrans2. destruct Htrans2 as [θ0'']. subst.
  dependent destruction Htrans1.
  assert (wf_ss (((X2, b) :: θ0'') ++ (X1, dbind_typ T0) :: θ')) by eauto.
  eapply wf_ss_late_dom_notin_ftver_bind_typ with (Y:=X2) in H4; simpl...
  assert ((X2, b) :: θ0'' ++ (X1, dbind_typ T0) :: θ' ᵗ⊩ ` X1 ⇝ T0) by eauto 6.
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
  X ∉ dom (θ2 ++ θ1) ->
  ⌈ θ1 ⌉ᵈ ᵗ⊢ᵈₘ Tᵈ ->
  θ2 ++ θ1 ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ2 ++ X ~ dbind_typ Tᵈ ++ θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ2 ++ θ1 ᵗ⊩ {Tᵃ ᵗ/ₜ X} Aᵃ ⇝ Aᵈ.
Proof with eauto using wf_ss_strengthen_etvar.
  intros * Hlc Hwfss Hnotin Hmono Hinstt Hinsta.
  generalize dependent θ2. generalize dependent X. generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros; try solve [simpl in *; dependent destruction Hinsta; 
                                                          eauto using wf_ss_strengthen_etvar].
  - destruct_eq_atom...
    + assert (θ2 ++ (X0, dbind_typ Tᵈ) :: θ1 ᵗ⊩ ` X0 ⇝ Tᵈ) by eauto.
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
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⊩ {Tᵃ ᵗ/ₜ X} Aᵃ ⇝ Aᵈ.
Proof.
  intros.
  apply ls_binds_split in H0.
  destruct H0 as [θ1 [θ2 Heq]]. subst.
  rewrite_env (θ1 ++ (X ~ dbind_typ Tᵈ) ++ θ2).
  apply trans_typ_weaken; auto.
  apply trans_typ_strengthen_etvar in H2 as Htranst; auto.
  eapply trans_typ_etvar_subst with (Tᵈ:=Tᵈ); eauto.
  - apply wf_ss_notin_remaining in H; auto.
  - apply wf_ss_strengthen_app in H. dependent destruction H; auto.
Qed.

Lemma trans_exp_etvar_subst_same_ss' : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  θ ᵉ⊩ {Tᵃ ᵉ/ₜ X} eᵃ ⇝ eᵈ.
Proof.
  intros * Hlc.
  generalize dependent θ. generalize dependent eᵈ.
  induction Hlc; simpl in *; intros.
  - dependent destruction H3; constructor; auto.
  - dependent destruction H3; constructor; auto.
  - dependent destruction H5.
    inst_cofinites_for trans_exp__abs. intros.
    inst_cofinites_with x.
    apply H0 in H5; auto.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H5...
    simpl in *. auto.
  - dependent destruction H3; eauto.
  - dependent destruction H5; eauto. simpl.
    inst_cofinites_for trans_exp__tabs;
    intros; inst_cofinites_with X0.
    + assert (Htrans :  (X0, □) :: θ ᵉ⊩ exp_anno eᵃ Aᵃ ᵉ^ₜ ` X0 ⇝ exp_anno (eᵈ ᵉ^ₜ ` X0) ( Aᵈ ᵗ^ₜ X0)). {
        constructor; eauto.
      }
      apply H0 in Htrans; eauto.
      simpl in Htrans. dependent destruction Htrans. rewrite subst_tvar_in_exp_open_exp_wrt_typ_fresh2; eauto.
      apply trans_typ_weaken_cons; eauto.
    + assert (Htrans :  (X0, □) :: θ ᵉ⊩ exp_anno eᵃ Aᵃ ᵉ^ₜ ` X0 ⇝ exp_anno (eᵈ ᵉ^ₜ ` X0) ( Aᵈ ᵗ^ₜ X0)). {
        constructor; eauto.
      }
      apply H0 in Htrans; eauto.
      simpl in Htrans. dependent destruction Htrans. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; eauto.
      apply trans_typ_weaken_cons; eauto.
    (* eapply trans_body_etvar_subst_same_ss' in H4; eauto.
    + rewrite subst_tvar_in_body_open_body_wrt_typ in H4; simpl in *.
      destruct_eq_atom; auto.
      eapply trans_typ_lc_atyp; eauto.
    + rewrite_env (nil ++ (X0 ~ □) ++ θ)%dbind. apply trans_typ_weaken; eauto.
      constructor; auto. *)
  - dependent destruction H4.
    constructor.
    + apply IHHlc; eauto.
    + eapply trans_typ_etvar_subst_same_ss; eauto.
  - dependent destruction H4.
    constructor.
    + apply IHHlc; eauto.
    + eapply trans_typ_etvar_subst_same_ss; eauto.
  - dependent destruction H3. auto.
  - dependent destruction H3. auto.
  - dependent destruction H3. auto.
Qed.


Lemma trans_exp_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  θ ᵉ⊩ {Tᵃ ᵉ/ₜ X} eᵃ ⇝ eᵈ.
Proof.
  intros.
  apply trans_exp_lc_aexp in H3 as Hlce.
  apply trans_typ_lc_atyp in H2 as Hlct.
  eapply trans_exp_etvar_subst_same_ss'; eauto. 
Qed.


Lemma trans_conts_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X csᵃ csᵈ,
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  θ ᶜˢ⊩ {Tᵃ ᶜˢ/ₜ X} csᵃ ⇝ csᵈ
with trans_contd_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X cdᵃ cdᵈ,
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  θ ᶜᵈ⊩ {Tᵃ ᶜᵈ/ₜ X} cdᵃ ⇝ cdᵈ.
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
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ʷ⊩ wᵃ ⇝ wᵈ ->
  θ ʷ⊩ {Tᵃ ʷ/ₜ X} wᵃ ⇝ wᵈ.
Proof.
  intros. destruct wᵃ; try simpl in *; dependent destruction H3;
    constructor; 
      try eapply trans_typ_etvar_subst_same_ss; eauto;
      try eapply trans_exp_etvar_subst_same_ss; eauto;
      try eapply trans_conts_etvar_subst_same_ss; eauto;
      try eapply trans_contd_etvar_subst_same_ss; eauto.
Qed.

#[local] Hint Resolve d_mono_typ_d_wf_typ : core.

Lemma trans_typ_etvar_binds : forall θ X Γ Ω T,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  θ ᵗ⊩ ` X ⇝ T ->
  X ~ T ∈ᵈ θ.
Proof.
  intros. eapply trans_wl_a_wl_binds_etvar_ss in H0; eauto.
  destruct H0 as [T'].
  assert (θ ᵗ⊩ ` X ⇝ T') by eauto.
  unify_trans_typ. auto.
Qed.


Lemma aworklist_subst_transfer_same_dworklist_rev_exist': forall Γ1 Γ2 Ω θ X T Tᵈ,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  X ∉ ftvar_in_typ T ->
  nil ⊩ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ T ⇝ Tᵈ ->
  θ ᵗ⊩ ` X ⇝ Tᵈ ->
  exists Γ'1 Γ'2 θ', 
      aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X T Γ'1 Γ'2 /\
      nil ⊩ {T ᵃʷ/ₜ X} Γ'2 ⧺ Γ'1 ⇝ Ω ⫣ θ' /\
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
    + apply IHΓ2 in Htranswl as Hws; auto.
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      assert (X0 ∉ dom θ'0) by (eapply notin_dom_reorder; eauto).
      exists Γ'1, (X0 ~ᵃ □ ;ᵃ Γ'2), ((X0, □) :: θ'0). 
        repeat split...
      * econstructor; auto.
        eapply a_wf_wwl_two_etvar_neq2; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_tvar_empty); eauto.
      * simpl. constructor; auto... 
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * eapply trans_typ_strengthen_cons; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_tvar_empty); eauto.
      * eapply trans_typ_strengthen_cons; eauto. 
      * dependent destruction Hwf... 
    + apply IHΓ2 in Htranswl as Hws; auto.
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      assert (X0 ∉ dom θ'0) by (eapply notin_dom_reorder; eauto).
      exists Γ'1, (X0 ~ᵃ ■;ᵃ Γ'2), ((X0, ■) :: θ'0). 
      repeat split; auto...
      * econstructor; auto.
        eapply a_wf_wwl_two_etvar_neq2; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_stvar_empty); eauto.
      * simpl. constructor; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * eapply trans_typ_strengthen_cons; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_stvar_empty); eauto.
      * eapply trans_typ_strengthen_cons; eauto.
      * dependent destruction Hwf... 
    + apply IHΓ2 in Htranswl as Hws; auto... 
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      exists Γ'1, (X0 ~ᵃ A1ᵃ ;ᵃ Γ'2), θ'0. repeat split...
      * econstructor; auto.
        apply trans_typ_reorder_ss with (θ:=θ')...
        -- intros. apply Hbinds...
           unfold not. intros. subst.
           apply subst_tvar_in_typ_fresh_same in H0...
        -- eapply trans_typ_etvar_subst_same_ss; eauto. 
           eapply trans_typ_etvar_binds; eauto.
           rewrite awl_to_aenv_app. simpl...
      * apply Hbinds; auto.
      * apply Hbinds; auto.
      * dependent destruction Hwf... 
    + assert (Hdec: (X0 `in` ftvar_in_typ T) \/ (X0 ∉ ftvar_in_typ T)) by fsetdec.
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
        assert (nil ⊩ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X0 ~ᵃ ⬒ ;ᵃ Γ1 ⇝ (Ω2 ⧺ Ω0) ⫣ θ'' ++ (X, dbind_typ T1) :: (X0, dbind_typ T0) :: θ'0).
        { eapply trans_wl_app with (θ2:=(X, dbind_typ T1) :: (X0, dbind_typ T0) :: θ'0). 
          constructor; auto.
          rewrite_env ((X ~ dbind_typ T1) ++ (X0, dbind_typ T0) :: θ'0 ).
          rewrite_env (θ'' ++ X ~ dbind_typ T1 ++ (X0, dbind_typ T0) :: θ'0).
          eapply trans_wl_weaken_etvar...
          simpl. 
          dependent destruction Hwf. rewrite <- ftvar_in_a_wf_wwl_upper in H... 
          rewrite ftvar_in_aworklist'_awl_app in H...
        }
        apply IHΓ2 in H5 as Hws.
        destruct Hws as [Γ'1 [Γ'2 [θ'00 [Hws [Htrans [Hbinds Hwfss]]]]]].
        exists Γ'1, Γ'2, θ'00. repeat split; auto.
        -- intros. apply Hbinds... eapply binds_same_move_etvar_before... 
        -- intros. eapply binds_same_move_etvar_before... apply Hbinds...
        -- apply trans_typ_reorder_ss with (θ:=(X0, dbind_typ T0) :: θ'' ++ (X, dbind_typ T1) :: θ'0); auto...
           intros. apply binds_same_move_etvar_before... 
        -- apply trans_typ_binds_etvar; eauto.
        -- apply a_wf_wwl_move_etvar_back; auto.
        -- eapply trans_typ_wf_ss; eauto. 
      * apply IHΓ2 in Htranswl as Hws; auto.
        destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
        assert (X0 ∉ dom θ'0) by (eapply notin_dom_reorder; eauto).
        assert (d_mono_typ (ss_to_denv θ'0) T0). {
           apply d_mono_typ_reorder_ss with (θ:=θ')...
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
           eapply a_wf_wwl_two_etvar_neq2; eauto.
        -- simpl. constructor; auto...
        -- intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
        -- intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
        -- eapply trans_typ_strengthen_cons; eauto.
        -- eapply trans_typ_strengthen_cons; eauto. 
        -- dependent destruction Hwf...  
  - dependent destruction Htranswl.
    apply IHΓ2 in Htranswl as Hws.
    destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
    exists Γ'1, (aworklist_cons_work Γ'2 w), θ'0. repeat (split; auto).
    + simpl. constructor; auto.
      apply trans_work_reorder_ss with (θ:=θ')... 
      * intros. apply Hbinds...
        unfold not. intros. subst.
        apply subst_tvar_in_work_fresh_same in H0...
      * eapply trans_work_etvar_subst_same_ss; eauto.
        eapply trans_typ_etvar_binds; eauto.
        rewrite awl_to_aenv_app. simpl...
    + auto.
    + auto.
    + dependent destruction Hwf... 
Qed.


Lemma aworklist_subst_det' : forall Γ X T Γ1 Γ2 Γ3 Γ4,
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
    apply a_wf_wwl_move_etvar_back; auto.
    eapply a_wf_wwl_tvar_notin_remaining in Hwf; eauto.
Qed.

Lemma aworklist_subst_det : forall Γ X T Γ1 Γ2 Γ3 Γ4,
  ⊢ᵃʷₛ Γ ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  aworklist_subst Γ X T Γ3 Γ4 ->
  Γ1 = Γ3 /\ Γ2 = Γ4.
Proof.
  intros. apply a_wf_wl_a_wf_wwl in H.
   eapply aworklist_subst_det'; eauto.
Qed.

#[local] Hint Resolve a_wf_wl_a_wf_wwl : core.

Corollary aworklist_subst_transfer_same_dworklist_rev_exist: forall Γ Ω θ X T Tᵈ,
  ⊢ᵃʷₛ Γ ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X ∉ ftvar_in_typ T ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ T ⇝ Tᵈ ->
  θ ᵗ⊩ ` X ⇝ Tᵈ ->
  exists Γ1 Γ2 θ', 
    aworklist_subst Γ X T Γ1 Γ2 /\
    nil ⊩ {T ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⇝ Ω ⫣ θ' /\
    (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
    wf_ss θ'.
Proof.
  intros. apply a_wf_wl_a_wf_wwl in H.
  apply awl_split_etvar in H0; auto.
  destruct H0 as [Γ' [Γ'' Heq]]. rewrite <- Heq in *. clear Heq.
  eapply aworklist_subst_transfer_same_dworklist_rev_exist'; eauto.
Qed.

Corollary aworklist_subst_transfer_same_dworklist_rev: forall Γ Ω θ X T Tᵈ Γ1 Γ2,
  ⊢ᵃʷₛ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ T ->
  X ∉ ftvar_in_typ T ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ T ⇝ Tᵈ ->
  θ ᵗ⊩ ` X ⇝ Tᵈ ->
  exists θ', 
    nil ⊩ {T ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⇝ Ω ⫣ θ' /\
    (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
    wf_ss θ'.
Proof.
  intros.
  eapply aworklist_subst_transfer_same_dworklist_rev_exist in H as Hwsex; eauto.
  destruct Hwsex as [Γ'1 [Γ'2 [θ' [Hsubst [Htrans [Hbinds Hwfss]]]]]].
  pose proof (aworklist_subst_det _ _ _ _ _ _ _ H H2 Hsubst). inversion H6. subst.
  exists θ'. repeat (split; auto).
  eapply aworklist_subst_target_is_etvar; eauto.
Qed.

Inductive aworklist_ord : aworklist -> Prop :=
  | awl_t_o__empty : aworklist_ord aworklist_empty
  | awl_t_o__work : forall Γ w, aworklist_ord (w ⫤ᵃ Γ)
  | awl_t_o__var : forall Γ x A, aworklist_ord (x ~ᵃ A ;ᵃ Γ)
  | awl_t_o__tvar : forall Γ X, aworklist_ord (X ~ᵃ □ ;ᵃ Γ)
  | awl_t_o__stvar : forall Γ X, aworklist_ord (X ~ᵃ ■ ;ᵃ Γ).

Inductive aworklist_trailing_etvar : aworklist -> aworklist -> Prop :=
  | awl_t_e__base : forall Γ0, aworklist_ord Γ0 -> aworklist_trailing_etvar Γ0 Γ0
  | awl_t_e__etvar : forall Γ0 Γ X, aworklist_trailing_etvar Γ0 Γ -> aworklist_trailing_etvar Γ0 
    (aworklist_cons_var Γ X abind_etvar_empty).

#[local] Hint Constructors aworklist_ord : core.
#[local] Hint Constructors aworklist_trailing_etvar : core.

Lemma a_wf_twl_aworklist_trailing_etvar_total : forall Γ,
  ⊢ᵃʷₜ Γ -> exists Γ0, aworklist_trailing_etvar Γ0 Γ.
Proof.
  intros. induction H; eauto.
  - destruct IHa_wf_twl as [Γ0].
    exists Γ0; eauto.
Qed.

Lemma a_wf_wl_aworklist_trailing_etvar_total : forall Γ,
  ⊢ᵃʷₛ Γ -> exists Γ0, aworklist_trailing_etvar Γ0 Γ.
Proof.
  intros. induction H; eauto.
  - apply a_wf_twl_aworklist_trailing_etvar_total. auto.
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
  θ ⊩ Γ ⇝ Ω ⫣ θ' ->
  exists θ'', θ ⊩ Γ0 ⇝ Ω ⫣ θ''.
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

Lemma a_wf_twl_rm_trailing_etvar : forall Γ0 Γ,
  aworklist_trailing_etvar Γ0 Γ -> 
  ⊢ᵃʷₜ Γ ->
  ⊢ᵃʷₜ Γ0.
Proof.
  intros. induction H; eauto.
  - dependent destruction H0; eauto.
Qed.

Lemma a_wf_wl_rm_trailing_etvar : forall Γ0 Γ,
  aworklist_trailing_etvar Γ0 Γ -> 
  ⊢ᵃʷₛ Γ ->
  ⊢ᵃʷₛ Γ0.
Proof.
  intros. induction H; eauto.
  - apply a_wf_wl_weaken_cons in H0; eauto.
Qed.

Inductive aworklist_trailing_sub : aworklist -> aworklist -> Prop :=
  | awl_t_s__base : forall Γ0, aworklist_trailing_sub Γ0 Γ0
  | awl_t_s__work : forall Γ0 Γ T1 T2, 
      aworklist_trailing_sub Γ0 Γ ->
      a_mono_typ (awl_to_aenv Γ) T1 ->
      (forall X, binds X abind_etvar_empty (awl_to_aenv Γ) -> X ∉ ftvar_in_typ T1) ->
      a_mono_typ (awl_to_aenv Γ) T2 ->
      (forall X, binds X abind_etvar_empty (awl_to_aenv Γ) -> X ∉ ftvar_in_typ T2) ->
      aworklist_trailing_sub Γ0 (aworklist_cons_work Γ (work_sub T1 T2)).

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
  


Lemma trans_apply_conts : forall θ csᵃ csᵈ Aᵃ Aᵈ wᵈ,
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  apply_conts csᵈ Aᵈ wᵈ ->
  exists wᵃ, apply_conts csᵃ Aᵃ wᵃ /\ θ ʷ⊩ wᵃ ⇝ wᵈ.
Proof.
  intros. induction H1; try dependent destruction H; eauto.
Qed.

Lemma trans_apply_contd : forall θ cdᵃ cdᵈ Aᵃ Aᵈ Bᵃ Bᵈ wᵈ,
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⊩ Bᵃ ⇝ Bᵈ ->
  apply_contd cdᵈ Aᵈ Bᵈ wᵈ ->
  exists wᵃ, apply_contd cdᵃ Aᵃ Bᵃ wᵃ /\ θ ʷ⊩ wᵃ ⇝ wᵈ.
Proof.
  intros. induction H2; try dependent destruction H; eauto 6.
Qed.

Lemma trans_typ_subst : forall θ1 θ2 Aᵃ Aᵈ Bᵃ Bᵈ X b,
  b = □ \/ b = ■ ->
  θ2 ++ (X , b) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  (forall Y T, binds Y (dbind_typ T) (θ2 ++ θ1) -> X ∉ ftvar_in_typ T) ->
  wf_ss (θ2 ++ θ1) ->
  θ2 ++ θ1 ᵗ⊩ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ᵗ⊩ {Bᵃ ᵗ/ₜ X} Aᵃ ⇝ {Bᵈ ᵗ/ₜ X} Aᵈ.
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
  num_arrow_in_typ (A ᵗ^^ₜ B) >= num_arrow_in_typ A.
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
  num_arrow_in_typ (A ᵗ^ₜ X) = num_arrow_in_typ A.
Proof.
  intros. unfold open_typ_wrt_typ. eapply d_same_num_arr_open_typ_rec_tvar.
Qed.


Lemma d_sub_more_num_arrow_in_mono_typ : forall Ψ A B,
  Ψ ⊢ A <: B ->
  (Ψ ᵗ⊢ᵈₘ A -> num_arrow_in_typ A >= num_arrow_in_typ B) /\
  (Ψ ᵗ⊢ᵈₘ B -> num_arrow_in_typ B >= num_arrow_in_typ A).
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
  X ~ T ∈ᵈ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  s_in X Aᵃ ->
  (num_arrow_in_typ Aᵈ) >= (num_arrow_in_typ T).
Proof.
  intros * Hwf Hbinds Htrans Hsin. dependent induction Htrans; simpl in *; dependent destruction Hsin; try lia.
  - unify_binds.
  - unify_binds.
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
  X ~ T ∈ᵈ θ ->
  θ ᵗ⊩ (typ_arrow A1ᵃ A2ᵃ) ⇝ (typ_arrow A1ᵈ A2ᵈ) ->
  s_in X (typ_arrow A1ᵃ A2ᵃ) ->
  (num_arrow_in_typ (typ_arrow A1ᵈ A2ᵈ)) > (num_arrow_in_typ T).
Proof.
  intros. dependent destruction H0.
  dependent destruction H1.
  - eapply trans_typ_etvar_s_in_more_num_arrow' in H0_; eauto. simpl. lia.
  - eapply trans_typ_etvar_s_in_more_num_arrow' in H0_0; eauto. simpl. lia.
Qed.


Lemma wf_ss_tvar_etvar : forall θ1 θ2 X T,
  wf_ss (θ2 ++ (X , dbind_tvar_empty) :: θ1) ->
  ⌈ θ1 ⌉ᵈ ᵗ⊢ᵈₘ T ->
  wf_ss (map (subst_tvar_in_dbind T X) θ2 ++ (X , dbind_typ T) :: θ1).
Proof with eauto.
  intros. induction θ2; simpl; auto.
  - dependent destruction H. constructor; auto.
  - destruct a as [Y]; destruct d; auto; dependent destruction H; eauto.
    + econstructor; eauto.
      replace (ss_to_denv (map (subst_tvar_in_dbind T X) θ2 ++ (X, dbind_typ T) :: θ1)) with 
        ((map (subst_tvar_in_dbind T X) (ss_to_denv θ2) ++ ss_to_denv ((X, dbind_typ T) :: θ1))).
      * simpl.
        apply d_mono_typ_subst_mono_mono; eauto.
        rewrite ss_to_denv_app in *; simpl in *...
      * rewrite ss_to_denv_app. rewrite ss_to_denv_subst_tvar_in_dbind_comm...
Qed.

Lemma d_mono_typ_strengthen_to_wf_env : forall Ψ1 Ψ2 A,
  wf_ss (Ψ2 ++ Ψ1) ->
  Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ A  ->
  Ψ1 ᵗ⊢ᵈ A ->
  Ψ1 ᵗ⊢ᵈₘ A.
Proof.
  intros * Hwfss Hmono Hwf. induction Hwf; try solve [dependent destruction Hmono]; auto.
  - dependent destruction Hmono.
    rewrite_env (nil ++ Ψ) in H0.
    apply binds_weaken with (F:=Ψ2) in H0.
    unify_binds.
  - dependent destruction Hmono; auto.
Qed.


Lemma trans_typ_tvar_etvar : forall θ1 θ2 Aᵃ Aᵈ Tᵃ Tᵈ X,
  θ2 ++ (X , □) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌈ θ1 ⌉ᵈ ᵗ⊢ᵈₘ Tᵈ ->
  θ1 ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  map (subst_tvar_in_dbind Tᵈ X) θ2 ++ (X , dbind_typ Tᵈ) :: θ1 ᵗ⊩ Aᵃ ⇝ {Tᵈ ᵗ/ₜ X} Aᵈ.
Proof with eauto using wf_ss_tvar_etvar, d_mono_typ_strengthen_to_wf_env.
  intros. generalize dependent Tᵃ. generalize dependent Tᵈ. 
  dependent induction H; intros; simpl; destruct_eq_atom; eauto...
  - econstructor; eauto...
    + apply binds_remove_mid in H0...
      apply binds_app_iff in H0; eauto.
      destruct H0.
      * apply binds_app_iff. left. apply binds_map with (f:=(subst_tvar_in_dbind Tᵈ X)) in H0...
      * apply binds_app_iff. right... 
  - apply trans_typ__stvar; eauto...
    + apply binds_remove_mid in H0...
      apply binds_app_iff in H0; eauto.
      destruct H0.
      * apply binds_app_iff. left. apply binds_map with (f:=(subst_tvar_in_dbind Tᵈ X)) in H0...
      * apply binds_app_iff. right... 
  - apply trans_typ__etvar; eauto...
    + apply binds_remove_mid in H0...
      apply binds_app_iff in H0; eauto.
      destruct H0.
      * apply binds_app_iff. left. apply binds_map with (f:=(subst_tvar_in_dbind Tᵈ X)) in H0...
      * apply binds_app_iff. right... 
        assert (wf_ss ((X, dbind_typ Tᵈ) :: θ1)). { constructor... apply wf_ss_notin_remaining in H... }
        eapply wf_ss_typ_no_etvar with (A:=A1) (X:=X) in H3...
        -- rewrite subst_tvar_in_typ_fresh_eq...
        -- simpl... eapply trans_typ_wf_dtyp...
      * unfold not. intros. subst. 
        assert (X ~ □ ∈ᵈ (θ2 ++ (X, □) :: θ1)) by auto.
        unify_binds.
  - inst_cofinites_for trans_typ__all; intros; 
    inst_cofinites_with X0...
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; eauto.
    rewrite_env (map (subst_tvar_in_dbind Tᵈ X) ((X0, □) :: θ2) ++ (X, dbind_typ Tᵈ) :: θ1).
    eapply H1; eauto.
Qed.


Lemma trans_typ_tvar_etvar_cons : forall θ Aᵃ Aᵈ Tᵃ Tᵈ X,
  (X , □) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ Tᵈ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  (X , dbind_typ Tᵈ) :: θ ᵗ⊩ Aᵃ ⇝ {Tᵈ ᵗ/ₜ X} Aᵈ.
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
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A \/ ~ ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A.
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
  (X , □) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⊩ Bᵃ ⇝ Bᵈ ->
  θ ᵗ⊩ {Bᵃ ᵗ/ₜ X} Aᵃ ⇝ {Bᵈ ᵗ/ₜ X} Aᵈ.
Proof.
  intros. rewrite_env (nil ++ θ). 
  eapply trans_typ_subst with (b:=□); eauto.
  intros.
  apply trans_typ_wf_ss in H.
  dependent destruction H.
  rewrite wf_ss_ftvar_in_typ_upper with (θ:=θ); eauto.
Qed.

#[local] Hint Resolve d_wf_wl_wf_env trans_wl_ss_binds_etvar_a_wl : core.


#[local] Hint Constructors a_mono_typ : core.


Lemma trans_wl_d_mono_typ_a_mono_typ_no_etvar : forall θ Γ Ω T,
  ⊢ᵃʷ Γ ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ T ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ T /\ forall X, X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ -> X ∉ ftvar_in_typ T.
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
  - split... 
Qed.



Lemma trans_wl_aworklist_trailing_sub_arrow : forall Γ Ω θ A1 A2 B1 B2,
  ⊢ᵃʷ Γ ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ typ_arrow A1 A2 ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ typ_arrow B1 B2 ->
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

Lemma trans_wl_a_wl_binds_var_binds_d_wl_trans_typ : forall θ Γ Ω x Aᵃ Aᵈ,
  uniq (⌊ Γ ⌋ᵃ) ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  x ~ Aᵃ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  x ~ Aᵈ ∈ᵈ ⌊ Ω ⌋ᵈ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  eapply trans_wl_a_wl_binds_var_binds_d_wl_and_trans in H0 as Htrans; eauto.
  destruct Htrans as [Aᵈ' [Hbinds Htrans]].
  eapply binds_unique with (b:=dbind_typ Aᵈ) in Hbinds; eauto. 
  dependent destruction Hbinds... 
  eapply a_wl_uniq_d_wl_uniq; eauto.
Qed.

Lemma trans_typ_weaken_cons2 : forall θ X1 X2 b1 b2 Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  wf_ss ((X2, b2) :: (X1, b1) :: θ) ->
  (X2, b2) :: (X1, b1) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof.
  intros. apply trans_typ_weaken_cons; auto. 
  dependent destruction H0; apply trans_typ_weaken_cons; auto.
Qed.

Lemma tvar_in_subst_typ_not_eq : forall A B X Y,
  X ∉ ftvar_in_typ B ->
  Y `in` ftvar_in_typ ({B ᵗ/ₜ X} A) ->
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
    H_2: nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ |- d_mono_typ (dwl_to_denv ?Ω ) ?A =>
    eapply trans_wl_ss_mono_typ_d_wl_mono_typ; eauto
  | H_1 : a_mono_typ (awl_to_aenv ?Γ) ?Aᵃ,
    H_2: nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ,
    H_3: ?θ ᵗ⊩ ?Aᵃ ⇝ ?Aᵈ |- d_mono_typ (ss_to_denv ?θ) ?Aᵈ =>
    eapply trans_wl_a_mono_typ_d_mono_typ; eauto
  | H_1 : a_mono_typ (ss_to_aenv ?θ) ?Aᵃ,
    H_2: nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ,
    H_3: ?θ ᵗ⊩ ?Aᵃ ⇝ ?Aᵈ |- d_mono_typ (ss_to_denv ?θ) ?Aᵈ =>
    eapply trans_typ_a_mono_typ_d_mono_typ; eauto
 | H_1 : a_mono_typ (awl_to_aenv ?Γ) ?Aᵃ,
    H_2: nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ |- d_mono_typ (dwl_to_denv ?Ω ) ?Aᵈ =>
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
    H_2: nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ,
    H_3: ?θ ᵗ⊩ ?Aᵃ ⇝ ?Aᵈ |- d_wf_typ (dwl_to_denv ?Ω) ?Aᵈ =>
    eapply trans_wl_a_wf_typ_d_wf_typ; eauto
  | H_1 : d_wf_typ (ss_to_denv ?θ) ?A,
    H_2: nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ |- dwl_to_denv ?Ω ᵗ⊢ᵈ ?A =>
    eapply trans_wl_ss_wf_typ_d_wf_typ; eauto
  | _ : _ |- _ => idtac
  end.


(* to short-cut the search of eauto  *)
Lemma trans_typ_etvar_arrow : forall X1 X2 A1 A2 θ,
  wf_ss ((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ) ->
  (X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ ᵗ⊩ typ_arrow ` X1 ` X2 ⇝ typ_arrow A1 A2.
Proof with eauto.
  intros. constructor; eauto...
Qed.

#[local] Hint Constructors a_mono_typ : core.

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp trans_wl_ss_mono_typ_d_wl_mono_typ trans_wl_d_wl_mono_typ_ss_mono_typ : core.

#[local] Hint Immediate trans_wl_ss_binds_tvar_a_wl trans_wl_ss_binds_stvar_a_wl trans_wl_ss_binds_etvar_a_wl : core.

#[local] Hint Resolve trans_wl_d_wf_typ_a_wf_typ trans_typ_refl trans_wl_a_wf_wl_d_wf_wl trans_typ_etvar_arrow : core.

#[local] Hint Resolve trans_typ_weaken_cons2 : core.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

(* reduce Γ with multiple trailing exsitential vars to the base case *)
Ltac solve_awl_trailing_etvar :=
  match goal with
  | H_1 : ⊢ᵃʷₛ ?Γ, H_2: ?θ ⊩ ?Γ ⇝ ?Ω ⫣ ?θ' |- _ =>
    let Htr := fresh "Htr" in
    let Γ0 := fresh "Γ0" in
    let Htrans_et := fresh "Htrans_et" in
    let θ' := fresh "θ'" in
    let Hwf := fresh "Hwf" in
    apply a_wf_wl_aworklist_trailing_etvar_total in H_1 as Htr;
    destruct Htr as [Γ0 Htr];
    eapply aworklist_trailing_etvar_reduce_ord; eauto;
    apply aworklist_trailing_etvar_trans with (Γ0:=Γ0) in H_2 as Htrans_et ; auto;
    destruct Htrans_et as [θ' Htrans_et];
    dependent destruction Htrans_et;
    apply a_wf_wl_rm_trailing_etvar in Htr as Hwf; auto;
    match goal with
    | H_3 : aworklist_trailing_etvar (aworklist_cons_var ?Γ0 ?X abind_etvar_empty) ?Γ |- _ =>
      apply aworklist_trailing_base_ord in H_3; inversion H_3
    | _ => idtac
    end
  end.

Theorem a_wl_red_completeness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃʷₛ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with eauto.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros * Hwf Htrans;
    try destruct Htrans as [θ Htrans].
  - solve_awl_trailing_etvar.
  - solve_awl_trailing_etvar.
    constructor. apply IHd_wl_red...
    destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    constructor. eapply IHd_wl_red...
    destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    constructor. apply IHd_wl_red...
    destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction. 
    + constructor...
      apply IHd_wl_red...
      destruct_a_wf_wl...
 - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction. 
    + constructor...
      apply IHd_wl_red...
      destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans; destruct_a_wf_wl.
    + destruct (X0 == X).
      * subst...
      * eapply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=`X0) (Tᵈ:=typ_unit) in Htrans_et as Htransws... 
        destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
        eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2)...
        apply IHd_wl_red; eauto. eapply aworklist_subst_wf_wl... 
    + eapply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=typ_unit) (Tᵈ:=typ_unit) in Htrans_et as Htransws... 
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2)...
      apply IHd_wl_red; eauto. eapply aworklist_subst_wf_wl... 
    + eapply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=typ_unit) (Tᵈ:=typ_unit) in Htrans_et as Htransws... 
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      eapply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2)...
      apply IHd_wl_red; eauto. eapply aworklist_subst_wf_wl... 
    + destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl... 
    + unify_binds.
    + assert (X0 <> X). { unfold not. intros. subst. unify_binds. }
      apply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X0) (T:=`X) (Tᵈ:=`X) 
        in Htrans_et as Htransws...
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      apply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
      * apply IHd_wl_red; eauto. destruct_a_wf_wl. eapply aworklist_subst_wf_wl; eauto.
      * destruct_a_wf_wl...
    + unify_binds. 
    + destruct_a_wf_wl... 
    + solve_binds_mono.
      dependent destruction Hmono.
      apply wf_ss_binds_mono_typ in H1...
      apply binds_ss_to_denv_binds_ss in H4.
      unify_binds.
    + assert (X0 <> X). { unfold not. intros. subst. unify_binds. }
      apply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X0) (T:=`X) (Tᵈ:=`X) 
        in Htrans_et as Htransws...
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
      * apply IHd_wl_red; eauto. destruct_a_wf_wl. eapply aworklist_subst_wf_wl; eauto.
      * destruct_a_wf_wl...
    + solve_binds_mono.
      dependent destruction Hmono.
      apply binds_ss_to_denv_binds_ss in H4.
      unify_binds.
    + destruct (X0 == X1)...
      * subst. destruct_a_wf_wl... 
      * apply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X0) (T:=`X1) (Tᵈ:=`X) 
          in Htrans_et as Htransws...
        destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
        apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
        -- apply IHd_wl_red; eauto. destruct_a_wf_wl. eapply aworklist_subst_wf_wl; eauto.
        -- destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans; destruct_a_wf_wl.
    + destruct (X0 == X).
      * subst...
      * eapply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=`X0) (Tᵈ:=typ_label l) in Htrans_et as Htransws... 
        destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
        eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2)...
        apply IHd_wl_red; eauto. eapply aworklist_subst_wf_wl... 
    + eapply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=typ_label l) (Tᵈ:=typ_label l) in Htrans_et as Htransws... 
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2)...
      apply IHd_wl_red; eauto. eapply aworklist_subst_wf_wl... 
    + eapply aworklist_subst_transfer_same_dworklist_rev_exist with (X:=X) (T:=typ_label l) (Tᵈ:=typ_label l) in Htrans_et as Htransws... 
      destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
      eapply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2)...
      apply IHd_wl_red; eauto. eapply aworklist_subst_wf_wl... 
    + destruct_a_wf_wl... 
  - solve_awl_trailing_etvar. 
    destruct_trans.
    (* ^X < ^Y *)
    + apply wf_ss_binds_mono_typ in H1 as Hmonoa...
      apply wf_ss_binds_mono_typ in H3 as Hmonob...
      destruct_mono_arrow.
      apply trans_wl_a_wf_wl_d_wf_wl in Htrans as Hwfd...
      destruct (X0 == X).
      * subst. assert ((work_sub A2 B2 ⫤ᵃ work_sub B1 A1 ⫤ᵃ Γ0) ⟶ᵃʷ⁎⋅)...
        apply IHd_wl_red...
        -- destruct_a_wf_wl. destruct_d_wf_wl...
           apply a_wf_wl__conswork_sub; simpl; eauto.  
           apply a_wf_wl__conswork_sub; simpl; eauto.  
        -- exists θ0; (repeat constructor; auto); apply trans_typ_refl...
        -- constructor...
           eapply a_wl_red_aworklist_trailing_sub_weaken with (Γ:=work_sub A2 B2 ⫤ᵃ work_sub B1 A1 ⫤ᵃ Γ0); eauto.
           eapply trans_wl_aworklist_trailing_sub_arrow; eauto. destruct_a_wf_wl... 
      * destruct_d_wf_wl. destruct_a_wf_wl. 
        apply d_wl_red_sound in H...
        dependent destruction H.
        dependent destruction H0; simpl in *...
        apply d_sub_mono_refl in H; solve_mono_typ. subst.
        apply d_sub_mono_refl in H0; solve_mono_typ. subst.
        -- eapply aworklist_subst_transfer_same_dworklist_rev_exist with (T:=`X0) (Tᵈ:= typ_arrow A1 B2) 
              in Htrans_et as Htransws... 
           destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
           apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto.
           eapply a_wl_red_aworklist_trailing_sub_weaken with (Γ:=work_sub B2 B2 ⫤ᵃ work_sub A1 A1 ⫤ᵃ (subst_tvar_in_aworklist ` X0 X Γ2 ⧺ Γ1)); eauto.
           ++ eapply trans_wl_aworklist_trailing_sub_arrow...
              eauto using aworklist_subst_wf_wl...
           ++ apply IHd_wl_red; auto...
              ** assert (Hnotin: X ∉ ftvar_in_typ (typ_arrow A1 B2)).
                 { apply wf_ss_typ_no_etvar with (A:=typ_arrow A1 B2) in H5... }
                 simpl in Hnotin.
                 apply a_wf_wl__conswork_sub; simpl. eapply aworklist_subst_wf_typ... eapply aworklist_subst_wf_typ...
                 apply a_wf_wl__conswork_sub; simpl. eapply aworklist_subst_wf_typ... eapply aworklist_subst_wf_typ...
                 eapply aworklist_subst_wf_wl...
              ** exists θ'. repeat (constructor; auto); apply trans_typ_refl; auto;
                 eapply trans_wl_d_wf_typ_ss_wf_typ; eauto.
    (* A -> B > ^X *)
    + apply wf_ss_binds_mono_typ in H2 as Hmonob...
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
        apply d_wf_wl__conswork_sub; simpl. solve_wf_typ. solve_wf_typ.
        apply d_wf_wl__conswork_sub; simpl. solve_wf_typ. solve_wf_typ.
        eauto.
      }
      apply a_mono_typ_dec in H0 as Hmono... inversion Hmono.
      * destruct_d_wf_wl.
        destruct_a_wf_wl.
        apply d_wl_red_sound in H.
        destruct_d_wl_del_red; simpl in *.
        rename_typ_rev. 
        assert (d_mono_typ (ss_to_denv θ0) A1) by solve_mono_typ.
        assert (d_mono_typ (ss_to_denv θ0) A2) by solve_mono_typ.
        apply d_sub_mono_refl in H; solve_mono_typ. subst.
        apply d_sub_mono_refl in H0; solve_mono_typ. subst.
        rename_typ_rev. 
        assert (X ∉ ftvar_in_typ (typ_arrow A1 B2)) by (eapply etvar_bind_no_etvar; eauto).
        assert (X ∉ ftvar_in_typ (typ_arrow A1ᵃ B2ᵃ)). {unfold not. intros. eapply a_mono_typ_in_s_in in H0; eauto. }
        simpl in *.
        eapply aworklist_subst_transfer_same_dworklist_rev_exist with (T:=typ_arrow A1ᵃ B2ᵃ) (Tᵈ:= typ_arrow A1 B2) 
              in Htrans_et as Htransws... 
        ++ destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
           apply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); eauto. 
           eapply a_wl_red_aworklist_trailing_sub_weaken with 
            (Γ:=work_sub B2 B2 ⫤ᵃ work_sub A1 A1 ⫤ᵃ (subst_tvar_in_aworklist (typ_arrow A1ᵃ B2ᵃ) X Γ2 ⧺ Γ1)); eauto.
           ** eapply trans_wl_aworklist_trailing_sub_arrow; eauto.
              eauto using aworklist_subst_wf_wl.
           ** apply IHd_wl_red...
              ---  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar with (Γ:=Γ0) in H7; eauto.
                  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar with (Γ:=Γ0) in H8; eauto. intuition.
              repeat (constructor; simpl; eauto using aworklist_subst_wf_wl); eapply aworklist_subst_wf_typ; eauto.
              --- exists θ'. repeat (constructor; auto); apply trans_typ_refl...
        ++ destruct_d_wf_wl. 
           dependent destruction Hmonob.
           apply d_wf_wl__conswork_sub; simpl. solve_wf_typ... solve_wf_typ...
           apply d_wf_wl__conswork_sub; simpl. solve_wf_typ... solve_wf_typ...
           eauto.
      * inst_cofinites_for a_wl_red__sub_arrow2... 
        destruct_mono_arrow.
        intros.
        assert (nil ⊩ (work_sub (typ_arrow ({typ_arrow ` X1 ` X2 ᵗ/ₜ X} A1ᵃ) ({typ_arrow ` X1 ` X2 ᵗ/ₜ X} A2ᵃ)) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) ⇝
                      (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2) ⫤ᵈ Ω) ⫣ ((X2, dbind_typ B2) :: (X1, dbind_typ B1) :: θ0)).
        { repeat (constructor; simpl; auto). 
          eapply trans_typ_etvar_subst_same_ss... 
          eapply trans_typ_etvar_subst_same_ss... 
        }
        dependent destruction H8...
        assert (aworklist_subst (work_sub (typ_arrow A1ᵃ A2ᵃ) ` X  ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) X (typ_arrow ` X1 ` X2) 
                                Γ2 (work_sub (typ_arrow A1ᵃ A2ᵃ) ` X  ⫤ᵃ Γ3)) by auto...
        destruct_trans_wl.
        dependent destruction H11.
        eapply aworklist_subst_transfer_same_dworklist_rev in H11 as Htransws; eauto.
        destruct Htransws as [θ' [Htransws [Hbinds Hwfss]]]; auto.
        -- simpl. destruct_eq_atom.
           simpl in *. destruct_eq_atom. 
           constructor. apply IHd_wl_red; eauto.
           ++ assert (binds X1 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2)))
                by (eapply aworklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              assert (binds X2 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2)))
                by (eapply aworklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              repeat (apply a_wf_wl__conswork_sub ; simpl; eauto)...
              ** eapply aworklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); simpl; eauto 7.
                 apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons... constructor... constructor...
              ** eapply aworklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); simpl; eauto 7.
                 apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons... constructor... constructor...
              ** eapply aworklist_subst_wf_wl with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); simpl; eauto 7.
           ++ exists θ'... 
              repeat (constructor; simpl; auto).
              ** apply Hbinds... 
              ** apply trans_typ_reorder_ss with (θ:=((X2, dbind_typ B2) :: (X1, dbind_typ B1) :: θ0))... 
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto 3... 
              ** apply trans_typ_reorder_ss with (θ:=((X2, dbind_typ B2) :: (X1, dbind_typ B1) :: θ0))...
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto 3...
              ** apply Hbinds; auto. 
        -- repeat (constructor; simpl; eauto). 
    (* ^X < A -> B *)
    + rename_typ_rev.
      apply wf_ss_binds_mono_typ in H1 as Hmonob...
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
        repeat (apply d_wf_wl__conswork_sub; simpl; auto); solve_mono_typ; solve_wf_typ...
      }
      apply a_mono_typ_dec in H3 as Hmono... inversion Hmono.
      * destruct_d_wf_wl.
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
        assert (X ∉ ftvar_in_typ (typ_arrow A1 B2)) by (eapply etvar_bind_no_etvar; eauto).
        assert (X ∉ ftvar_in_typ (typ_arrow A1ᵃ B2ᵃ)). {unfold not. intros. eapply a_mono_typ_in_s_in in H0; eauto. }
        simpl in *.
        eapply aworklist_subst_transfer_same_dworklist_rev_exist with (T:=typ_arrow A1ᵃ B2ᵃ) (Tᵈ:= typ_arrow A1 B2) 
              in Htrans_et as Htransws... 
        ++ destruct Htransws as [Γ1 [Γ2 [θ' [Hsubst [Htransws [Hbinds Hwfss]]]]]].
           apply a_wl_red__sub_etvarmono2 with (Γ1:=Γ1) (Γ2:=Γ2); eauto. 
           eapply a_wl_red_aworklist_trailing_sub_weaken with 
            (Γ:=work_sub B2 B2 ⫤ᵃ work_sub A1 A1 ⫤ᵃ (subst_tvar_in_aworklist (typ_arrow A1ᵃ B2ᵃ) X Γ2 ⧺ Γ1)); eauto.
           ** eapply trans_wl_aworklist_trailing_sub_arrow; eauto.
              eauto using aworklist_subst_wf_wl...
           ** apply IHd_wl_red...
              --- eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar with (Γ:=Γ0) in H6; eauto.
                  eapply trans_wl_d_mono_typ_a_mono_typ_no_etvar with (Γ:=Γ0) in H7; eauto. intuition.
                  repeat (constructor; simpl; eauto using aworklist_subst_wf_wl); eapply aworklist_subst_wf_typ; eauto.
              --- exists θ'. repeat (constructor; auto); apply trans_typ_refl...
        ++ destruct_d_wf_wl. repeat (apply d_wf_wl__conswork_sub; simpl; auto); solve_wf_typ...
      * inst_cofinites_for a_wl_red__sub_arrow1... 
        destruct_mono_arrow.
        intros.
        rename_typ_rev.
        assert (nil ⊩ (work_sub ` X (typ_arrow ({typ_arrow ` X1 ` X2 ᵗ/ₜ X} B1ᵃ) ({typ_arrow ` X1 ` X2 ᵗ/ₜ X} B2ᵃ)) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) ⇝
                      (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2)  ⫤ᵈ Ω) ⫣ ((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0)).
        { repeat (constructor; simpl; auto).
          eapply trans_typ_etvar_subst_same_ss... 
          eapply trans_typ_etvar_subst_same_ss... 
        }
        dependent destruction H8.
        assert (aworklist_subst (work_sub ` X (typ_arrow B1ᵃ B2ᵃ) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0) X (typ_arrow ` X1 ` X2) 
                Γ2 (work_sub ` X (typ_arrow B1ᵃ B2ᵃ) ⫤ᵃ Γ3)) by auto.
        destruct_trans_wl.
        dependent destruction H11.
        eapply aworklist_subst_transfer_same_dworklist_rev with (Ω:=Ω) in H11 as Htransws; eauto.
        destruct Htransws as [θ' [Htransws [Hbinds Hwfss]]]; auto.
        -- simpl. destruct_eq_atom.
           simpl in *. destruct_eq_atom. 
           constructor. apply IHd_wl_red; eauto.
           ++ assert (binds X1 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2)))
                by (eapply aworklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              assert (binds X2 abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ3 ⧺ Γ2))) 
                by (eapply aworklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto).
              repeat (apply a_wf_wl__conswork_sub; simpl; eauto)...
              ** eapply aworklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto.
                 constructor... simpl. apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons...
              ** eapply aworklist_subst_wf_typ_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto.
                 constructor... simpl. apply a_wf_typ_weaken_cons... apply a_wf_typ_weaken_cons...
              ** eapply aworklist_subst_wf_wl with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0))...
                 simpl. constructor...
           ++ exists θ'... 
              repeat (constructor; simpl; auto).
              ** apply trans_typ_reorder_ss with (θ:=((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0))... 
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto... 
              ** apply Hbinds... 
              ** apply Hbinds... 
              ** apply trans_typ_reorder_ss with (θ:=((X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0))...
                 --- intros. apply Hbinds; auto. eapply tvar_in_subst_typ_not_eq; eauto. simpl...
                 --- eapply trans_typ_etvar_subst_same_ss; eauto... 
        -- repeat (constructor; simpl; eauto).
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
      * apply a_wf_wl__conswork_sub...
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
        -- repeat (apply a_wf_wl__conswork_sub; auto).  
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
      assert (nil ⊩ work_check (eᵃ ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0 ⇝
                    work_check (e ᵉ^ₑ exp_var_f x) A2 ⫤ᵈ x ~ᵈ A1;ᵈ Ω ⫣ (X2, dbind_typ A2) :: (X1, dbind_typ A1) :: θ0).
      { apply wf_ss_binds_mono_typ in H3 as Hmono...
        dependent destruction Hmono.
        repeat (constructor; auto); simpl in *.
        eapply trans_exp_weaken_cons...
        eapply trans_exp_weaken_cons...
      }
      eapply aworklist_subst_transfer_same_dworklist_rev in H12 as Htransws...
      destruct Htransws as [θ' [Htransws [Hbinds Hwfss]]]...
      * apply H0; eauto. eapply aworklist_subst_wf_wl with 
        (Γ:=(work_check (eᵃ ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0))... 
        repeat (econstructor; simpl; auto).
        eapply a_wf_exp_weaken_etvar_twice...
        simpl. constructor...
      * repeat (econstructor; simpl; auto).
        eapply a_wf_exp_weaken_etvar_twice...
      * simpl... constructor...
    + destruct_a_wf_wl. pick fresh x and apply a_wl_red__chk_absarrow.
      inst_cofinites_with x.
      eapply H0.
      * repeat constructor... 
        apply a_wf_exp_var_binds_another_cons with (A1:=T)...
        apply a_wf_typ_weaken_cons...
      * exists θ0. eauto 6. 
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
      * exists θ0. eauto 6. 
  (* e ⇐ A1 ⊓ A2 *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + apply a_wl_red__chk_inter.
      apply IHd_wl_red...
      destruct_a_wf_wl... constructor...
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
      eapply trans_wl_a_wl_binds_var_binds_d_wl_trans_typ...
  (* e : A => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    constructor.
    apply IHd_wl_red...
    + destruct_a_wf_wl... constructor...
    + exists θ0...
  (* Λ a. e : A => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans. destruct_a_wf_wl.
    pick fresh X and apply a_wl_red__inf_tabs.
    inst_cofinites_with X.
    repeat rewrite open_body_wrt_typ_anno in H1.
    apply H0.
    + repeat (constructor; simpl; auto).
      inst_cofinites_for a_wf_typ__all. intros... 
      * apply s_in_rename with (Y:=X0) in H4. 
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H4...
      * intros. apply a_wf_typ_rename_tvar_cons with (Y:=X0) in H5.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H5...
    + exists ((X, dbind_tvar_empty) :: θ0). 
      repeat constructor...
      * inst_cofinites_for trans_typ__all; intros.
        -- apply s_in_rename with (Y:=X0) in H4. 
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H4...
        -- apply trans_typ_rename_tvar_cons with (X':=X0) in H2...
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
  - solve_awl_trailing_etvar.
    destruct_trans...
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans...
    destruct_a_wf_wl...
    econstructor... eapply IHd_wl_red...
  - solve_awl_trailing_etvar.
    destruct_trans...
    destruct_a_wf_wl...
    econstructor... eapply IHd_wl_red...
  (* λ x. e => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__inf_abs_mono; auto.
    intros.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    apply H1.
    + repeat (constructor; simpl; eauto).
      * eapply a_wf_exp_weaken_etvar_twice...
      * apply a_wf_conts_weaken_cons... apply a_wf_conts_weaken_cons...
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
    apply IHd_wl_red... constructor...
    exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...
    constructor...
    exists θ0... constructor... constructor...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...

  (* A ∘ B =>=> _ *)
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
        apply wf_ss_binds_mono_typ in H1 as Hmono...
        dependent destruction Hmono.
        assert (exists Γ2', Γ2 = aworklist_cons_work Γ2' (work_infabs (typ_arrow ` X1 ` X2) cdᵃ )).
        { dependent destruction H5. eauto. }
        destruct H6 as [Γ2' Heq]. subst.
        simpl. destruct_eq_atom.
        constructor.
        apply IHd_wl_red...
        -- dependent destruction H5. destruct_a_wf_wl...
           assert (X1 ~ ⬒ ∈ᵃ ⌊ {typ_arrow ` X1 ` X2 ᵃʷ/ₜ X} Γ2' ⧺ Γ2 ⌋ᵃ). {
              eapply aworklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)) (b:=abind_etvar_empty); simpl in *...
              constructor... constructor...
           }
           assert (X2 ~ ⬒ ∈ᵃ ⌊ {typ_arrow ` X1 ` X2 ᵃʷ/ₜ X} Γ2' ⧺ Γ2 ⌋ᵃ). {
              eapply aworklist_subst_binds_same_atvar with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)) (b:=abind_etvar_empty); simpl in *...
              constructor... constructor...
           }
           repeat (constructor; auto).
           ++ eapply aworklist_subst_wf_contd_subst with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); simpl in *; eauto...
              constructor... apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
              constructor... constructor...
           ++ eapply aworklist_subst_wf_twl with (Γ:=(X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ0)); eauto. simpl...
              simpl. constructor...
        -- apply aworklist_subst_transfer_same_dworklist_rev with 
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
             apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
          ++ repeat (constructor; auto).
          ++ repeat (constructor; auto).  
             eapply trans_contd_weaken_cons... eapply trans_contd_weaken_cons...
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
    apply IHd_wl_red... constructor...
    exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl...
    constructor... 
    apply IHd_wl_red... constructor...
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl...
    constructor...
    apply IHd_wl_red... constructor...
    exists θ0...
    constructor... constructor...
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
    constructor...
    exists θ0...
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
    destruct_a_wf_wl.  apply a_wf_wl_strengthen_work... eapply a_wf_work_apply_conts...
    exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    eapply trans_apply_contd in H as Hacd; eauto.
    destruct Hacd as [wᵃ [Hacd Htransw]].
    eapply a_wl_red__applyd with (w:=wᵃ)...
    apply IHd_wl_red; auto.
    destruct_a_wf_wl.  apply a_wf_wl_strengthen_work... eapply a_wf_work_apply_contd with (A:=Aᵃ)... 
    exists θ0...
Qed.
    