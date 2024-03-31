Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import uni.algo_worklist.prop_basic.
Require Import ln_utils.


Hint Constructors a_wl_red : Hdb_a_wl_red_completness.
Hint Constructors wf_ss : Hdb_a_wl_red_completness.
Hint Constructors a_wf_wl : Hdb_a_wl_red_completness.
Hint Constructors trans_typ : Hdb_a_wl_red_completness.
Hint Constructors trans_exp : Hdb_a_wl_red_completness.
Hint Constructors trans_conts : Hdb_a_wl_red_completness.
Hint Constructors trans_contd : Hdb_a_wl_red_completness.
Hint Constructors trans_work : Hdb_a_wl_red_completness.
Hint Constructors trans_worklist : Hdb_a_wl_red_completness.


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
(* look at wfs *)
Theorem aworklist_subst_total' : forall Γ1 Γ2 X Tᵃ Tᵈ Ω θ,
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
Admitted.


Lemma a_worklist_subst_transfer_same_dworklist_rev: forall Γ Ω θ X T Tᵈ Γ1 Γ2,
  ⊢ᵃʷ Γ ->
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
  intros. generalize dependent θ. generalize dependent Ω. induction H2; intros; simpl in *.
  - dependent destruction H3.
    exists θ'; repeat split; auto.
    + intros. inversion H8. dependent destruction H9... 
      contradiction. auto.
    + apply trans_typ_wf_ss in H5. dependent destruction H5; auto.
  - dependent destruction H3.
    apply IHaworklist_subst in H3; auto.
    destruct H3 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists θ'0. repeat split; eauto.
    + constructor; auto.
      admit.
    + apply Hbinds; auto.
    + apply Hbinds; auto.
    + destruct_a_wf_wl; auto. 
    + admit. (* OK, mono strengthen *)
  - dependent destruction H5.
    apply IHaworklist_subst in H5; auto.
    destruct H5 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists ((Y, dbind_tvar_empty)::θ'0). repeat split; eauto.
    + constructor; auto.
      unfold not. intros. 
      apply binds_In_inv in H5. destruct H5 as [b].
      apply Hbinds in H5; auto. 
      apply binds_In in H5. contradiction.
    + intros. 
      inversion H9. dependent destruction H10; auto.
      apply binds_cons; auto. apply Hbinds; auto.
    + intros. inversion H9. dependent destruction H10; auto.
      apply binds_cons; auto. apply Hbinds; auto.
    + constructor; auto. unfold not. intros.
      apply binds_In_inv in H5. destruct H5 as [b].
      apply Hbinds in H5; auto. 
      apply binds_In in H5. contradiction.
    + destruct_a_wf_wl; auto.
    + admit.
    + rewrite_env (nil ++ θ'). eapply trans_typ_strengthen; eauto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ θ'). eapply trans_typ_strengthen; eauto.
      eapply trans_wl_wf_ss; eauto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5; auto.
    destruct H5 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists ((Y, dbind_stvar_empty)::θ'0). repeat split; eauto.
    + constructor; auto.
      unfold not. intros. 
      apply binds_In_inv in H5. destruct H5 as [b].
      apply Hbinds in H5; auto. 
      apply binds_In in H5. contradiction.
    + intros. 
      inversion H9. dependent destruction H10; auto.
      apply binds_cons; auto. apply Hbinds; auto.
    + intros. inversion H9. dependent destruction H10; auto.
      apply binds_cons; auto. apply Hbinds; auto.
    + constructor; auto. unfold not. intros.
      apply binds_In_inv in H5. destruct H5 as [b].
      apply Hbinds in H5; auto. 
      apply binds_In in H5. contradiction.
    + destruct_a_wf_wl; auto.
    + admit.
    + rewrite_env (nil ++ θ'). eapply trans_typ_strengthen; eauto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ θ'). eapply trans_typ_strengthen; eauto.
      eapply trans_wl_wf_ss; eauto.
  - dependent destruction H3.
    apply IHaworklist_subst in H3; auto.
    destruct H3 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists θ'0. repeat split; eauto.
    + constructor; auto. admit.
    + apply Hbinds; auto.
    + apply Hbinds; auto.
    + destruct_a_wf_wl; auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5; auto.
    destruct H5 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists ((Y, dbind_typ T)::θ'0). repeat split; eauto.
    + constructor; auto. admit. admit.
    + intros. inversion H10. dependent destruction H11; auto.
      apply binds_cons; auto. apply Hbinds; auto.
    + intros. inversion H10. dependent destruction H11; auto.
      apply binds_cons; auto. apply Hbinds; auto.
    + constructor; auto. unfold not. intros.
      apply binds_In_inv in H5. destruct H5 as [b].
      apply Hbinds in H5; auto. 
      apply binds_In in H5. contradiction.
      admit.
    + destruct_a_wf_wl; auto.
    + admit.
    + rewrite_env (nil ++ θ'). eapply trans_typ_strengthen; eauto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ θ'). eapply trans_typ_strengthen; eauto.
      eapply trans_wl_wf_ss; eauto.
  - dependent destruction H5.
    assert 
      (Hwft: forall X, X `in` ftvar_in_typ T -> X `in` ftvar_in_typ Tᵈ) by admit.  (* since Y in A *)
    apply trans_wl_split in H5. destruct H5 as [Ω1 [Ω2 [θ'' [Heq [Htrans1 Htrans2]]]]].
    dependent destruction Htrans1.
    apply trans_wl_split_ss in Htrans2 as Htransss2.
    destruct Htransss2 as [θ''].
    assert (nil ⫦ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1 ⇝ ((Ω2 ⧺ Ω0)%dworklist) ⫣ 
      (θ'' ++ (X, dbind_typ T0) :: (Y, dbind_typ T) :: θ'0)).
    { eapply trans_wl_app with (θ2:=(X, dbind_typ T0) :: (Y, dbind_typ T) :: θ'0).
      econstructor; eauto.
      econstructor; eauto. admit. admit.
      admit.
    }
    apply IHaworklist_subst in H12.
    destruct H12 as [θ'1 [Htrans [Hbinds Hwfss]]].
    exists θ'1. repeat split; eauto. rewrite Heq. auto.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
    admit.
Admitted.


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
  constructor; auto.
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
    eapply aworklist_trailing_etvar_reduce_ord; eauto 
    ;
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
  exists wᵃ, apply_conts csᵃ Aᵃ wᵃ.
Proof.
  intros. induction H1.
  - dependent destruction H.
    exists (work_infabs Aᵃ cdᵃ). constructor.
  - dependent destruction H.
    admit.
  - dependent destruction H.
    admit.
Admitted.



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
  | H1 :  d_mono_typ ?θ typ_bot |- _ => inversion H1
  | H1 :  d_mono_typ ?θ typ_top |- _ => inversion H1
  | H1 :  d_mono_typ ?θ (typ_all ?A) |- _ => inversion H1
  | H1 :  d_mono_typ ?θ (typ_intersection ?A1 ?A2) |- _ => inversion H1
  | H1 :  d_mono_typ ?θ (typ_union ?A1 ?A2) |- _ => inversion H1
end.


Hint Resolve trans_wl_wf_ss : Hdb_a_wl_red_completness.


Lemma trans_typ_subst : forall θ1 θ2 Aᵃ Aᵈ Bᵃ Bᵈ X b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  θ2 ++ (X , b) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss (θ2 ++ θ1) ->
  θ2 ++ θ1 ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ {Bᵈ /ᵗ X} Aᵈ.
Proof.
  intros. generalize dependent Bᵃ. generalize dependent Bᵈ. 
  dependent induction H0; intros; simpl; destruct_eq_atom; eauto with Hdb_a_wl_red_completness.
  - admit.
  - admit.
  - admit.
  - admit.
  - inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X0.
    admit.
Admitted.


Lemma trans_typ_subst_tvar_cons : forall θ Aᵃ Aᵈ Bᵃ Bᵈ X,
  (X , dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ {Bᵈ /ᵗ X} Aᵈ.
Proof.
  intros. rewrite_env (nil ++ θ). eapply trans_typ_subst with (b:=dbind_tvar_empty); eauto.
  apply trans_typ_wf_ss in H. dependent destruction H; auto.
Qed.


Hint Resolve trans_typ_lc_atyp : Hdb_a_wl_red_completness.
Hint Resolve trans_typ_lc_dtyp : Hdb_a_wl_red_completness.


Theorem d_a_wl_red_completness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃʷ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_completness.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros * Hwf Htrans;
    try destruct Htrans as [θ Htrans].
  - solve_awl_trailing_etvar.
    + dependent destruction Hwf...
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
    + assert (exists Γ1, exists Γ2, aworklist_subst Γ0 X ` X0 Γ1 Γ2) by admit.    
      destruct H4 as [Γ1 [Γ2 Hws]].
      * eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); auto.
        -- admit.
        -- admit.
        -- admit.
        -- eapply a_worklist_subst_transfer_same_dworklist_rev with (Ω:=Ω) (θ:=θ0) (Tᵈ:=typ_unit) in Hws; auto.
            ++ destruct Hws as [θ'' [Htranswl [Hbinds Hwfss]]].
               apply IHd_wl_red; eauto. 
               ** admit. (* wf *)
            ++ admit.
            ++ admit.
            ++ admit.
            ++ apply trans_typ_binds_etvar; auto.
            ++ apply trans_typ_binds_etvar; auto.
    + admit.
    + admit.
    + destruct_a_wf_wl...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + destruct_a_wf_wl... 
    + apply wf_ss_uniq in H0. 
      pose proof (binds_unique _ _ _ _ _ H1 H3 H0).
      inversion H4.
    + admit.
    + apply wf_ss_uniq in H0. 
      pose proof (binds_unique _ _ _ _ _ H1 H3 H0).
      inversion H4.
    + destruct_a_wf_wl... 
    + admit. (* OK, false *)
    + admit.
    + admit. (* OK, false *)
    + admit.
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + apply wf_ss_binds_monotyp in H1 as Hmonoa...
      apply wf_ss_binds_monotyp in H3 as Hmonob...
      admit.
    + apply wf_ss_binds_monotyp in H2 as Hmonob...
      admit.
    + apply wf_ss_binds_monotyp in H1 as Hmonoa...
      admit.
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
        admit. (* OK, wf *)
        admit. (* OK, wf *)
      * exists ((X , dbind_stvar_empty) :: θ0)...
        constructor...
        constructor...
        -- apply trans_typ_tvar_stvar_cons...
        -- apply trans_typ_tvar_stvar_cons...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + pick fresh X and apply a_wl_red__sub_alll.
      inst_cofinites_with X.
      * eapply trans_typ_neq_all_rev...
      * eapply trans_typ_neq_intersection_rev...
      * eapply trans_typ_neq_union_rev...
      * inst_cofinites_with X.
        apply IHd_wl_red.
        -- admit.
        -- exists ((X, dbind_typ T) :: θ0).
           repeat (constructor; auto with Hdb_a_wl_red_completness).
           ++ admit.
           ++ admit.
           ++ rewrite_env (nil ++ (X ~ dbind_typ T) ++ θ0). 
              apply trans_typ_weaken...
              admit.
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
        exists θ0...
  - solve_awl_trailing_etvar.
    + destruct_trans.
      * solve_binds_nonmono_contradiction.
      * apply a_wl_red__sub_intersection3. apply IHd_wl_red; eauto.
        destruct_a_wf_wl...
        exists θ0...
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + constructor. apply IHd_wl_red; eauto.
      destruct_a_wf_wl...
      exists θ0...
  - solve_awl_trailing_etvar. 
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + eapply a_wl_red__sub_union2. apply IHd_wl_red; eauto.
      destruct_a_wf_wl...
      exists θ0...
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
      admit.
       inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2. 
       admit.
    + destruct_a_wf_wl. pick fresh x and apply a_wl_red__chk_absarrow.
      inst_cofinites_with x.
      eapply H0.
      * repeat constructor... 
        admit. (* OK, wf *) 
        admit.
      * exists θ0. constructor...
  (* λx. e ⇐ ⊤ *)
  - solve_awl_trailing_etvar.
    destruct_trans.
    + solve_binds_nonmono_contradiction.
    + pick fresh x and apply a_wl_red__chk_abstop. 
      inst_cofinites_with x.
      apply H0.
      * admit. (* OK, wf *)
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
    admit. (* OK, wf *)
    exists θ0...
    repeat constructor...
    admit.
  - solve_awl_trailing_etvar.
    destruct_trans.
    constructor.
    apply IHd_wl_red...
    + admit. (* OK, wf *)
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
    + admit. (* OK, wf *)
    + exists ((X, dbind_tvar_empty) :: θ0). 
      repeat constructor...
      * inst_cofinites_for trans_typ__all. intros.
        apply trans_typ_rename_tvar_cons with (X':=X0) in H2...
        rewrite subst_typ_in_typ_open_typ_in_typ_tvar2 in H2...
        rewrite subst_typ_in_typ_open_typ_in_typ_tvar2 in H2...
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
    + admit. (* OK, wf *)
    + exists ((X2 , dbind_typ T2) :: (X1 , dbind_typ T1) :: θ0)...
      dependent destruction H.
      assert (d_mono_typ (ss_to_denv θ0) T2) by admit.
      assert (d_mono_typ (ss_to_denv θ0) T1) by admit.
      assert (Hwfss: wf_ss θ0) by (now eapply trans_wl_wf_ss in Htrans_et).
      repeat (constructor; eauto with Hdb_a_wl_red_completness).
      * admit. (* OK, trans_cont_weaken *)
      * admit. (* OK, trans_exp_weaken *)
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
      * admit. (* OK, wf *)
      * exists θ0. constructor...
        constructor...
        rename_typ_rev.
        pick fresh X. inst_cofinites_with X.
        erewrite <- subst_typ_in_typ_open_typ_in_typ_tvar2; eauto...
        erewrite <- subst_typ_in_typ_open_typ_in_typ_tvar2 with (A:=A); eauto...
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
      * admit.
      * intros.
        assert (exists Γ2', Γ2 = aworklist_conswork Γ2' (work_infabs (typ_arrow ` X1 ` X2) cdᵃ )).
        { dependent destruction H5. eauto. }
        destruct H6 as [Γ2' Heq]. subst.
        simpl. destruct_eq_atom.
        constructor.
        apply IHd_wl_red...
        admit. (* OK, wf *)
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
           repeat (constructor; auto with Hdb_a_wl_red_completness).
        -- admit. (* OK, Hwf *)
        -- simpl. constructor... 
        -- apply wf_ss_binds_monotyp in H1 as Hmono...
            dependent destruction Hmono...
            repeat (constructor; auto with Hdb_a_wl_red_completness).
          admit.  (* OK, trans_contd_strengthen *)
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
      * admit. (* OK, wf *)
      * exists ((X, dbind_typ T)::θ0).
        repeat (constructor; auto with Hdb_a_wl_red_completness).
        admit.
        admit.
        admit.
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
    destruct Hacs as [wᵃ Hacs].
    eapply a_wl_red__applys with (w:=wᵃ)...
    apply IHd_wl_red; auto.
    admit.
    exists θ0... constructor...
    admit.
  - solve_awl_trailing_etvar.
    destruct_trans.
    admit.
Admitted.
