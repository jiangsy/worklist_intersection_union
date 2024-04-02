Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.decl.prop_basic.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import uni.algo_worklist.prop_basic.
Require Import ln_utils.


Ltac destruct_trans :=
  repeat
    lazymatch goal with
    (* | H : trans_worklist ?θ (aworklist_conswork ?Γ ?w) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ (aworklist_consvar ?Γ ?w ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ  (aworklist_constvar ?Γ ?X ?b) ?Ω ?θ' |- _ => dependent destruction H *)
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

Ltac rename_typ_rev :=
  lazymatch goal with
  | H : trans_typ ?θ ?Aᵃ (open_typ_wrt_typ _ _)  |- _ => fail
  | H : trans_typ ?θ ?Aᵃ (?C_T _ _) |- _ => fail
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ, _ : trans_typ ?θ ?A2ᵃ ?A2ᵈ, _ : trans_typ ?θ ?A3ᵃ ?A3ᵈ, _ : trans_typ ?θ ?A4ᵃ ?A4ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵈ"ᵃ0" in 
    rename A1ᵃ into A1ᵃ1; 
    let A2ᵃ1 := fresh A2ᵈ"ᵃ0" in
    rename A2ᵃ into A2ᵃ1;
    let A3ᵃ1 := fresh A3ᵈ"ᵃ0" in
    rename A3ᵃ into A3ᵃ1;
    let A4ᵃ1 := fresh A4ᵈ"ᵃ0" in
    rename A4ᵃ into A4ᵃ1;
    let A1ᵃ2 := fresh A1ᵈ"ᵃ" in 
    rename A1ᵃ1 into A1ᵃ2;
    let A2ᵃ2 := fresh A2ᵈ"ᵃ" in
    rename A2ᵃ1 into A2ᵃ2;
    let A3ᵃ2 := fresh A3ᵈ"ᵃ" in
    rename A3ᵃ1 into A3ᵃ2;
    let A4ᵃ2 := fresh A4ᵈ"ᵃ" in
    rename A4ᵃ1 into A4ᵃ2
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ, _ : trans_typ ?θ ?A2ᵃ ?A2ᵈ, _ : trans_typ ?θ ?A3ᵃ ?A3ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵈ"ᵃ0" in 
    rename A1ᵃ into A1ᵃ1;
    let A2ᵃ1 := fresh A2ᵈ"ᵃ0" in
    rename A2ᵃ into A2ᵃ1;
    let A3ᵃ1 := fresh A3ᵈ"ᵃ0" in
    rename A3ᵃ into A3ᵃ1;
    let A1ᵃ2 := fresh A1ᵈ"ᵃ" in 
    rename A1ᵃ1 into A1ᵃ2;
    let A2ᵃ2 := fresh A2ᵈ"ᵃ" in
    rename A2ᵃ1 into A2ᵃ2;
    let A3ᵃ2 := fresh A3ᵈ"ᵃ" in
    rename A3ᵃ1 into A3ᵃ2
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ, _ : trans_typ ?θ ?A2ᵃ ?A2ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵈ"ᵃ0" in 
    rename A1ᵃ into A1ᵃ1;
    let A2ᵃ1 := fresh A2ᵈ"ᵃ0" in
    rename A2ᵃ into A2ᵃ1;
    let A1ᵃ2 := fresh A1ᵈ"ᵃ" in 
    rename A1ᵃ1 into A1ᵃ2;
    let A2ᵃ2 := fresh A2ᵈ"ᵃ" in
    rename A2ᵃ1 into A2ᵃ2
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵈ"ᵃ0" in 
    rename A1ᵃ into A1ᵃ1;
    let A1ᵃ2 := fresh A1ᵈ"ᵃ" in 
    rename A1ᵃ1 into A1ᵃ2
  end. 

(* equiv to tex_wfs *)
(* lo* at wfs *)
(* Theorem aworklist_subst_total' : forall Γ1 Γ2 X Tᵃ Tᵈ Ω θ,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  nil ⫦ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ⇝ Ω ⫣ θ ->
  binds X (dbind_typ Tᵈ) θ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  exists Γ'1 Γ'2,
    aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X Tᵃ Γ'1 Γ'2.
Proof.
Admitted.


Theorem aworklist_subst_total : forall Γ X Tᵃ Tᵈ Ω θ,
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X (dbind_typ Tᵈ) θ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  exists Γ'1 Γ'2,
    aworklist_subst Γ X Tᵃ Γ'1 Γ'2.
Proof.
Admitted. *)

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
    assert (Y ~ □ ∈ (θ2 ++ (X, dbind_typ ` Y) :: θ1)) by auto.
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

Lemma d_mono_typ_strengthen_multi : forall θ1 θ2 X T1 T2,
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
     ((aworklist_constvar Γ2 X2 b2) ⧺ (aworklist_constvar Γ1 X1 b1))%aworklist in H by auto.
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
  (X2, b) :: θ ⫦ᵗ T ⇝ Tᵈ -> 
  (X2, b) :: θ ⫦ᵗ ` X1 ⇝ Tᵈ ->
  nil ⫦ Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ Γ1 ⇝ Ω ⫣ θ ->
  X2 `notin` ftvar_in_typ T.
Proof.
  intros.   
  apply trans_wl_split in H2. destruct H2 as [Ω1 [Ω2 [θ'' [Heq [Htrans1 Htrans2]]]]]. subst.
  apply trans_wl_split_ss in Htrans2. destruct Htrans2 as [θ0'']. subst.
  dependent destruction Htrans1.
  assert (wf_ss (((X2, b) :: θ0'') ++ (X1, dbind_typ T0) :: θ')) by eauto.
  eapply wf_ss_late_dom_notin_ftver_bind_typ with (Y:=X2) in H4; simpl...
  assert ((X2, b) :: θ0'' ++ (X1, dbind_typ T0) :: θ' ⫦ᵗ ` X1 ⇝ T0) by eauto 6.
  unify_trans_typ.
  unfold not. intros.
  eapply trans_typ_tvar_stvar_in_atyp_in_dtyp in H5; eauto.
  inversion H; subst; auto.
  auto.
Qed.

(* Hint Resolve  : idents …. *)

Lemma trans_typ_etvar_subst : forall θ1 θ2 Tᵃ Tᵈ X Aᵃ Aᵈ,
  lc_typ Aᵃ -> 
  wf_ss (θ2 ++ θ1) ->
  X `notin` dom (θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) Tᵈ ->
  θ2 ++ θ1 ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ2 ++ X ~ dbind_typ Tᵈ ++ θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ2 ++ θ1 ⫦ᵗ {Tᵃ /ᵗ X} Aᵃ ⇝ Aᵈ.
Proof with eauto using wf_ss_strengthen_etvar.
  intros * Hlc Hwfss Hnotin Hmono Hinstt Hinsta.
  generalize dependent θ2. generalize dependent X. generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros; try solve [simpl in *; dependent destruction Hinsta; 
                                                          eauto using wf_ss_strengthen_etvar].
  - destruct_eq_atom...
    + assert (θ2 ++ (X0, dbind_typ Tᵈ) :: θ1 ⫦ᵗ ` X0 ⇝ Tᵈ) by eauto.
      unify_trans_typ...
    + dependent destruction Hinsta...
      * apply trans_typ__tvar...
        admit.
      * apply trans_typ__stvar...
        admit.
      * apply trans_typ__etvar...
        admit.
  - simpl in Hinsta. 
    dependent destruction Hinsta...
    inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X0.
    rewrite_env (((X0, □) :: θ2) ++ θ1).
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    apply H0; auto.
    + simpl. constructor; auto.
    + simpl. rewrite_env (nil ++ (X0 ~ □) ++ (θ2 ++ θ1)). 
      apply trans_typ_weaken; auto.
      constructor; auto.
    + admit.
Admitted.

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp : core.

Lemma trans_typ_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X Aᵃ Aᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ ⫦ᵗ {Tᵃ /ᵗ X} Aᵃ ⇝ Aᵈ.
Proof.
  intros.
  assert (exists θ1 θ2, θ = θ2 ++ X ~ dbind_typ Tᵈ ++ θ1) by admit.
  destruct H4 as [θ1 [θ2 Heq]].
  rewrite  Heq in *.
  apply trans_typ_weaken; auto.
  apply trans_typ_strengthen_etvar in H2 as Htranst; auto.
  eapply trans_typ_etvar_subst with (Tᵈ:=Tᵈ); eauto.
  - apply wf_ss_tvar_notin_remaining in H. 
    admit.
  - apply wf_ss_strengthen_app in H. dependent destruction H; auto. 
Admitted.


Lemma trans_exp_etvar_subst_same_ss' : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ ⫦ᵉ (subst_tvar_in_exp Tᵃ X eᵃ) ⇝ eᵈ
with trans_body_etvar_subst_same_ss' : forall θ Tᵃ Tᵈ X bᵃ bᵈ,
  lc_body bᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ ⫦ᵇ (subst_tvar_in_body Tᵃ X bᵃ) ⇝ bᵈ.
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
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ ⫦ᵉ (subst_tvar_in_exp Tᵃ X eᵃ) ⇝ eᵈ
with trans_body_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X bᵃ bᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ ⫦ᵇ (subst_tvar_in_body Tᵃ X bᵃ) ⇝ bᵈ.
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
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᶜˢ csᵃ ⇝ csᵈ ->
  θ ⫦ᶜˢ (subst_tvar_in_conts Tᵃ X csᵃ) ⇝ csᵈ
with trans_contd_etvar_subst_same_ss : forall θ Tᵃ Tᵈ X cdᵃ cdᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᶜᵈ cdᵃ ⇝ cdᵈ ->
  θ ⫦ᶜᵈ (subst_tvar_in_contd Tᵃ X cdᵃ) ⇝ cdᵈ.
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
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
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

Lemma a_worklist_subst_transfer_same_dworklist_rev_exist': forall Γ1 Γ2 Ω θ X T Tᵈ,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  X `notin` ftvar_in_typ T ->
  trans_worklist nil (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) Ω θ ->
  θ ⫦ᵗ T ⇝ Tᵈ ->
  θ ⫦ᵗ ` X ⇝ Tᵈ ->
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
    exists Γ'1, (x ~ᵃ A1ᵃ;ᵃ Γ'2)%aworklist, θ'0. repeat split...
    + econstructor; auto.
      apply trans_typ_reorder with (θ:=θ')...
      * intros. apply Hbinds...
        unfold not. intros. subst.
        apply subst_tvar_in_typ_fresh_same in H0...
      * eapply trans_typ_etvar_subst_same_ss; eauto. 
        admit. (* *, binds *)
    + apply Hbinds; auto.
    + apply Hbinds; auto.
    + destruct_a_wf_wl; auto.
  - dependent destruction Htranswl.
    + apply IHΓ2 in Htranswl as Hws; auto.
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      exists Γ'1, (X0 ~ᵃ □ ;ᵃ Γ'2)%aworklist, ((X0, □) :: θ'0). 
        repeat split...
      * econstructor; auto.
        eapply a_wf_wl_two_etvar_neq2; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_tvar_empty); eauto.
      * simpl. constructor; auto. 
        admit. (* *, notin *)
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * constructor; auto.
        admit. (* *, notin *)
      * eapply trans_typ_strengthen_cons; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_tvar_empty); eauto.
      * eapply trans_typ_strengthen_cons; eauto. 
      * destruct_a_wf_wl...
    + apply IHΓ2 in Htranswl as Hws; auto.
      destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
      exists Γ'1, (aworklist_constvar Γ'2 X0 abind_stvar_empty), ((X0, dbind_stvar_empty) :: θ'0). 
      repeat split; auto...
      * econstructor; auto.
        eapply a_wf_wl_two_etvar_neq2; eauto.
        eapply trans_typ_tvar_stvar_notin with (b:=dbind_stvar_empty); eauto.
      * simpl. constructor; auto. admit. (* *, notin *)
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
      * constructor; auto. 
        admit. (* *, notin *)
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
          eapply d_mono_typ_strengthen_multi; eauto.
        }
        assert (nil ⫦ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X0 ~ᵃ ⬒ ;ᵃ Γ1 ⇝ (Ω2 ⧺ Ω0) ⫣ θ'' ++ (X, dbind_typ T1) :: (X0, dbind_typ T0) :: θ'0).
        { eapply trans_wl_app with (θ2:=(X, dbind_typ T1) :: (X0, dbind_typ T0) :: θ'0). 
          constructor; auto.
          rewrite_env ((X ~ dbind_typ T1) ++ (X0, dbind_typ T0) :: θ'0 ).
          rewrite_env (θ'' ++ X ~ dbind_typ T1 ++ (X0, dbind_typ T0) :: θ'0).
          eapply trans_wl_weaken_etvar...
          admit. (* *, notin *)
        }
        apply IHΓ2 in H5 as Hws.
        destruct Hws as [Γ'1 [Γ'2 [θ'00 [Hws [Htrans [Hbinds Hwfss]]]]]].
        exists Γ'1, Γ'2, θ'00. repeat split; auto.
        -- intros. admit. (* *, binds *)
        -- intros. admit. (* *, binds *)
        -- apply trans_typ_reorder with (θ:=(X0, dbind_typ T0) :: θ'' ++ (X, dbind_typ T1) :: θ'0); auto...
           intros. admit. (* *, binds *)
        -- apply trans_typ_binds_etvar; eauto.
        -- apply a_wf_wl_reorder; auto.
        -- eapply trans_typ_wf_ss; eauto. 
      * apply IHΓ2 in Htranswl as Hws; auto.
        destruct Hws as [Γ'1 [Γ'2 [θ'0 [Hws [Htrans [Hbinds Hwfss]]]]]].
        exists Γ'1, (X0 ~ᵃ ⬒ ;ᵃ Γ'2)%aworklist, ((X0, dbind_typ T0) :: θ'0). 
          repeat split; auto.
        -- econstructor; auto.  
           eapply a_wf_wl_two_etvar_neq2; eauto.
        -- simpl. constructor; auto...
           admit. (* *, notin *)
           admit. (* **, monotyp reorder *)
        -- intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
        -- intros. destruct_binds... apply binds_cons; auto. apply Hbinds; auto.
        -- constructor; auto.
           admit. (* *, notin *)
           admit. (* **, monotyp reorder *)
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
        admit. (* *, binds *)
    + auto.
    + auto.
    + destruct_a_wf_wl; auto.
Admitted.


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
    apply a_wf_wl_reorder; auto.
    eapply a_wf_wl_tvar_notin_remaining in Hwf; eauto.
Qed.


Corollary a_worklist_subst_transfer_same_dworklist_rev_exist: forall Γ Ω θ X T Tᵈ,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ T ->
  trans_worklist nil Γ Ω θ ->
  θ ⫦ᵗ T ⇝ Tᵈ ->
  θ ⫦ᵗ ` X ⇝ Tᵈ ->
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
  θ ⫦ᵗ T ⇝ Tᵈ ->
  θ ⫦ᵗ ` X ⇝ Tᵈ ->
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
  θ ⫦ᶜˢ csᵃ ⇝ csᵈ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  apply_conts csᵈ Aᵈ wᵈ ->
  exists wᵃ, apply_conts csᵃ Aᵃ wᵃ /\ θ ⫦ʷ wᵃ ⇝ wᵈ.
Proof.
  intros. induction H1; try dependent destruction H; eauto.
Qed.

Lemma trans_apply_contd : forall θ cdᵃ cdᵈ Aᵃ Aᵈ Bᵃ Bᵈ wᵈ,
  θ ⫦ᶜᵈ cdᵃ ⇝ cdᵈ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  apply_contd cdᵈ Aᵈ Bᵈ wᵈ ->
  exists wᵃ, apply_contd cdᵃ Aᵃ Bᵃ wᵃ /\ θ ⫦ʷ wᵃ ⇝ wᵈ.
Proof.
  intros. induction H2; try dependent destruction H; eauto 6.
Qed.

Ltac destruct_mono_arrow :=
  repeat
    lazymatch goal with
    | H : d_mono_typ ?θ (typ_arrow ?A1 ?A2) |- _ => dependent destruction H
    end. 


Ltac solve_binds_mono :=
  repeat
  match goal with
  | H1 : binds ?X (dbind_typ ?T) ?θ , H2 : wf_ss ?θ |- _ =>
    match goal with
    | H1 : d_mono_typ (ss_to_denv θ) T |- _ => fail 1
    | _ =>
      let Hmono := fresh "Hmono" in
      apply wf_ss_binds_monotyp in H1 as Hmono; auto
    end
  end;
  destruct_mono_arrow.


Ltac solve_binds_nonmono_contradiction :=
  solve_binds_mono; 
  match goal with
  | H1 : d_mono_typ ?θ typ_bot |- _ => inversion H1
  | H1 : d_mono_typ ?θ typ_top |- _ => inversion H1
  | H1 : d_mono_typ ?θ (typ_all ?A) |- _ => inversion H1
  | H1 : d_mono_typ ?θ (typ_intersection ?A1 ?A2) |- _ => inversion H1
  | H1 : d_mono_typ ?θ (typ_union ?A1 ?A2) |- _ => inversion H1
end.

Lemma trans_typ_subst : forall θ1 θ2 Aᵃ Aᵈ Bᵃ Bᵈ X b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  θ2 ++ (X , b) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss (θ2 ++ θ1) ->
  θ2 ++ θ1 ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ {Bᵈ /ᵗ X} Aᵈ.
Proof.
  intros. generalize dependent Bᵃ. generalize dependent Bᵈ. 
  dependent induction H0; intros; simpl; destruct_eq_atom; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X0.
    admit.
Admitted.


(* maybe only b=tvar is used *)
(* Lemma trans_typ_tvar_etvar : forall θ1 θ2 Aᵃ Aᵈ Tᵃ Tᵈ X b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  θ2 ++ (X , b) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  d_mono_typ (ss_to_denv (θ2 ++ θ1)) Tᵈ ->
  θ1 ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ2 ++ (X , dbind_typ Tᵈ) :: θ1 ⫦ᵗ Aᵃ ⇝ {Tᵈ /ᵗ X} Aᵈ.
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


Lemma trans_typ_tvar_etvar : forall θ1 θ2 Aᵃ Aᵈ Tᵃ Tᵈ X,
  θ2 ++ (X , dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  d_mono_typ (ss_to_denv (θ2 ++ θ1)) Tᵈ ->
  θ1 ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  map (subst_tvar_in_dbind Tᵈ X) θ2 ++ (X , dbind_typ Tᵈ) :: θ1 ⫦ᵗ Aᵃ ⇝ {Tᵈ /ᵗ X} Aᵈ.
Proof.
  intros. generalize dependent Tᵃ. generalize dependent Tᵈ. 
  dependent induction H; intros; simpl; destruct_eq_atom; eauto.
  - apply trans_typ_binds_etvar; eauto. 
    admit.
  - econstructor; auto. admit. admit.
  - admit. (* false *)
  - apply trans_typ__stvar; auto. admit. admit.
  - admit.
  - constructor. admit.
  - constructor. admit.
  - constructor. admit.
  - inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X0.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
    rewrite_env (map (subst_tvar_in_dbind Tᵈ X) ((X0, □) :: θ2) ++ (X, dbind_typ Tᵈ) :: θ1).
    eapply H0; eauto.
    admit.
    admit.
Admitted.


Lemma trans_typ_tvar_etvar_cons : forall θ Aᵃ Aᵈ Tᵃ Tᵈ X,
  (X , dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  d_mono_typ (ss_to_denv θ) Tᵈ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  (X , dbind_typ Tᵈ) :: θ ⫦ᵗ Aᵃ ⇝ {Tᵈ /ᵗ X} Aᵈ.
Proof.
  intros. rewrite_env ((map (subst_tvar_in_dbind Tᵈ X) nil) ++ (X ,  dbind_typ Tᵈ) :: θ). 
  eapply trans_typ_tvar_etvar; eauto.
Qed.


Ltac solve_right := 
  let Hcontra := fresh "Hcontra" in 
  right; intros Hcontra; inversion Hcontra.


Lemma a_mono_typ_dec : forall Γ A,
  ⊢ᵃʷ Γ ->
  a_wf_typ (awl_to_aenv Γ) A ->
  a_mono_typ (awl_to_aenv Γ) A \/ ~ a_mono_typ (awl_to_aenv Γ) A.
Proof.
  intros. dependent induction H0; auto; try solve [solve_right].  
  - right. unfold not. intros.
    dependent destruction H1.
    + admit.
    + admit.
  - left. admit.
Admitted.

Lemma trans_typ_subst_tvar_cons : forall θ Aᵃ Aᵈ Bᵃ Bᵈ X,
  (X , dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ {Bᵈ /ᵗ X} Aᵈ.
Proof.
  intros. rewrite_env (nil ++ θ). 
  eapply trans_typ_subst with (b:=dbind_tvar_empty); eauto.
Qed.

#[local] Hint Resolve d_wf_wl_wf_env : core.

Lemma trans_wl_a_wl_binds_var_binds_d_wl_trans_typ' : forall θ Γ Ω x Aᵃ Aᵈ,
  ⊢ᵃʷ Γ ->
  ⊢ᵈʷ Ω ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds x (abind_var_typ Aᵃ) (awl_to_aenv Γ) ->
  binds x (dbind_typ Aᵈ) (dwl_to_denv Ω) ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
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
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof.
  intros. eapply trans_wl_a_wf_wl_d_wf_wl in H0 as Hdwf; auto.
  eapply trans_wl_a_wl_binds_var_binds_d_wl_trans_typ'; eauto.
Qed.
  

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp trans_wl_d_wl_mono_ss : core.


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
    destruct_trans.
    + destruct (X0 == X).
      * subst. destruct_a_wf_wl... 
      * assert (exists Γ1, exists Γ2, aworklist_subst Γ0 X ` X0 Γ1 Γ2) by admit.    
        destruct H4 as [Γ1 [Γ2 Hws]].
        -- eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); auto.
           ++ eapply trans_wl_ss_binds_etvar_a_wl...
           ++ apply a_mono_typ__etvar. eapply trans_wl_ss_binds_etvar_a_wl...
           ++ eapply a_worklist_subst_transfer_same_dworklist_rev with (Ω:=Ω) (θ:=θ0) (Tᵈ:=typ_unit) in Hws; eauto.
              ** destruct Hws as [θ'' [Htranswl [Hbinds Hwfss]]].
                 apply IHd_wl_red; eauto. 
                 --- admit. (* wf *)
              ** destruct_a_wf_wl... 
              ** eapply trans_wl_ss_binds_etvar_a_wl; eauto. 
              ** apply a_mono_typ__etvar. eapply trans_wl_ss_binds_etvar_a_wl...
    + admit. (* Pending *)
    + admit. (* Pending *)
    + destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl... 
    + apply wf_ss_uniq in H0. 
      pose proof (binds_unique _ _ _ _ _ H1 H3 H0).
      inversion H4.
    + admit. (* Pending *)
    + exfalso. eapply wf_ss_tvar_stvar_false; eauto.
    + destruct_a_wf_wl... 
    + solve_binds_mono.
      dependent destruction Hmono.
      admit.
    + admit. (* Pending *)
    + solve_binds_mono.
      dependent destruction Hmono.
      admit.  
    + admit. (* Pending *)
  - solve_awl_trailing_etvar. 
    destruct_trans.
    (* ^X < ^Y *)
    + apply wf_ss_binds_monotyp in H1 as Hmonoa...
      apply wf_ss_binds_monotyp in H3 as Hmonob...
      admit. (* Pending *)
    (* A -> B > ^X *)
    + apply wf_ss_binds_monotyp in H2 as Hmonob...
      admit. (* Pending *)
    (* ^X < A -> B *)
    + apply wf_ss_binds_monotyp in H1 as Hmonoa...
      rename_typ_rev.
      admit. (* Pending *)
    (* A1 -> B1 < A2 -> B2 *)
    + destruct_a_wf_wl...
      constructor...
      apply IHd_wl_red...
      exists θ0...
  - solve_awl_trailing_etvar. 
    destruct_trans; try solve_binds_nonmono_contradiction.
    + dependent destruction Hwf0. 
      dependent destruction H3.
      dependent destruction H3.
      dependent destruction H5.
      pick fresh X and apply a_wl_red__sub_all. 
      inst_cofinites_with X.
      apply H0; auto.
      * constructor... constructor...
        admit. (* *, wf *)
        admit. (* *, wf *)
      * exists ((X , dbind_stvar_empty) :: θ0)...
        constructor...
        constructor...
        -- apply trans_typ_tvar_stvar_cons...
        -- apply trans_typ_tvar_stvar_cons...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + destruct_a_wf_wl. dependent destruction H6. 
      pick fresh X and apply a_wl_red__sub_alll.
      inst_cofinites_with X.
      * eapply trans_typ_neq_all_rev...
      * eapply trans_typ_neq_intersection_rev...
      * eapply trans_typ_neq_union_rev...
      * inst_cofinites_with X.
        apply IHd_wl_red.
        -- admit. (* *, wf *)
        -- exists ((X, dbind_typ T) :: θ0).
           repeat (constructor; auto)...
           ++ eapply trans_typ_tvar_etvar_cons with (θ:=θ0) (Tᵃ:=T) (Tᵈ:=T) in H4; eauto...
              rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H4... 
              apply trans_typ_refl...
              eapply trans_wl_d_wf_typ_ss_wf_typ...
              apply d_mono_typ_d_wf_typ...
           ++ rewrite_env (nil ++ (X ~ dbind_typ T) ++ θ0). 
              apply trans_typ_weaken...
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
    + inst_cofinites_for a_wl_red__chk_absetvar; intros.
      eapply trans_wl_ss_binds_etvar_a_wl; eauto.
      inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2. 
      admit. (* Pending *)
    + destruct_a_wf_wl. pick fresh x and apply a_wl_red__chk_absarrow.
      inst_cofinites_with x.
      eapply H0.
      * repeat constructor... 
        admit. (* *, wf *) 
        admit. (* *, wf weaken *)
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
        admit. (* *, wf *)
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
    admit. (* *, wf *)
    exists θ0...
    repeat constructor...
    eapply trans_wl_a_wl_binds_var_binds_d_wl_trans_typ; eauto.
  - solve_awl_trailing_etvar.
    destruct_trans.
    constructor.
    apply IHd_wl_red...
    + admit. (* *, wf *)
    + exists θ0...
  (* Λ a. e : A => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct bᵃ.
    pick fresh X and apply a_wl_red__inf_tabs.
    inst_cofinites_with X.
    repeat rewrite open_body_wrt_typ_anno in H1.
    dependent destruction H1.
    apply H0.
    + admit. (* *, wf *)
    + exists ((X, dbind_tvar_empty) :: θ0). 
      repeat constructor...
      * inst_cofinites_for trans_typ__all. intros.
        apply trans_typ_rename_tvar_cons with (X':=X0) in H2...
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
  - solve_awl_trailing_etvar.
    destruct_trans...
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...
  (* λ x. e => _ *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    inst_cofinites_for a_wl_red__inf_abs_mono; auto.
    intros.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    apply H1.
    + admit. (* *, wf *)
    + exists ((X2 , dbind_typ T2) :: (X1 , dbind_typ T1) :: θ0)...
      dependent destruction H...
      assert (d_mono_typ (ss_to_denv θ0) T2) by eauto.
      assert (d_mono_typ (ss_to_denv θ0) T1) by eauto.
      assert (Hwfss: wf_ss θ0) by (now eapply trans_wl_wf_ss in Htrans_et).
      repeat (constructor; auto).
      * admit. (* *, trans_cont_weaken *)
      * admit. (* *, trans_exp_weaken *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    destruct_a_wf_wl.
    constructor...
    apply IHd_wl_red...
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
      * admit. (* *, wf *)
      * exists θ0. constructor...
        constructor...
        rename_typ_rev.
        pick fresh X. inst_cofinites_with X.
        erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2; eauto...
        erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2 with (A:=A); eauto...
        eapply trans_typ_subst_tvar_cons with (θ:=θ0) in H0; auto; eauto.
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
        assert (exists Γ2', Γ2 = aworklist_conswork Γ2' (work_infabs (typ_arrow ` X1 ` X2) cdᵃ )).
        { dependent destruction H5. eauto. }
        destruct H6 as [Γ2' Heq]. subst.
        simpl. destruct_eq_atom.
        constructor.
        apply IHd_wl_red...
        admit. (* *, wf *)
        apply a_worklist_subst_transfer_same_dworklist_rev with 
          (Ω:=(work_infabs (typ_arrow A B) cd ⫤ Ω)%dworklist) 
          (Tᵈ:=typ_arrow A B)
          (θ:=((X2, dbind_typ B) :: (X1, dbind_typ A) :: θ0))
          in H5; simpl...  
        destruct H5 as [θ'' [Htransws [Hbinds Hwfss]]].    
        -- exists θ''. simpl in *. destruct_eq_atom. auto.
           dependent destruction H. 
           dependent destruction Htransws.
           destruct_trans.
           repeat (constructor; auto).
        -- admit. (* *, wf *)
        -- admit.
        -- simpl. constructor... 
        -- apply wf_ss_binds_monotyp in H1 as Hmono...
           dependent destruction Hmono...
           repeat (constructor; auto).
           admit.  (* *, trans_contd_strengthen *)
        -- solve_binds_mono. 
           constructor.
           apply trans_typ_binds_etvar...
           apply trans_typ_binds_etvar...
        -- solve_binds_mono. 
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
    + pick fresh X and apply a_wl_red__infabs_all.
      inst_cofinites_with X.
      apply IHd_wl_red. 
      * admit. (* *, wf *)
      * exists ((X, dbind_typ T)::θ0).
        repeat (constructor; auto)...
        -- eapply trans_typ_tvar_etvar_cons with (θ:=θ0) (Tᵃ:=T) (Tᵈ:=T) in H1; eauto...
           rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H1...
           apply trans_typ_refl...
           eapply trans_wl_d_wf_typ_ss_wf_typ...
           eapply d_mono_typ_d_wf_typ...
        -- admit. (* *, trans cont weaken *)
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
