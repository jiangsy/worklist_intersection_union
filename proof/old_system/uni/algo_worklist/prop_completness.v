Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wl_red : Hdb_a_wl_red_completness.



Ltac destruct_trans :=
  repeat
    lazymatch goal with
    (* | H : trans_worklist ?θ (aworklist_conswork ?Γ ?w) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ (aworklist_consvar ?Γ ?w ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ  (aworklist_constvar ?Γ ?X ?b) ?Ω ?θ' |- _ => dependent destruction H *)
    | H : trans_work ?θ ?wᵃ (?wᵈ _) |- _ => dependent destruction H
    | H : trans_work ?θ ?wᵃ (?wᵈ _ _) |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _ _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_cont ?θ (?C_C _) ?wᵈ |- _ => dependent destruction H
    | H : trans_cont ?θ (?C_C _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ (` ?X) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ ?Aᵃ (open_typ_wrt_typ _ _) |- _ => fail
    | H : trans_typ ?θ ?Aᵃ typ_unit |- _ => dependent destruction H
    | H : trans_typ ?θ ?Aᵃ typ_bot |- _ => dependent destruction H
    | H : trans_typ ?θ ?Aᵃ typ_top |- _ => dependent destruction H
    | H : trans_typ ?θ ?Aᵃ (`?X) |- _ => dependent destruction H
    | H : trans_typ ?θ ?Aᵃ (?C_T _ _)  |- _ => dependent destruction H
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
    + admit.
    + admit. 
  - dependent destruction H3.
    apply IHaworklist_subst in H3; auto.
    destruct H3 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists θ'0. repeat split; eauto.
    + constructor; auto.
      admit.
    + apply Hbinds; auto.
    + apply Hbinds; auto.
    + admit.
    + admit.
  - dependent destruction H5.
    apply IHaworklist_subst in H5; auto.
    destruct H5 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists ((Y, dbind_tvar_empty)::θ'0). repeat split; eauto.
    + constructor; auto. admit.
    + intros. admit.
    + intros. admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - dependent destruction H5.
    apply IHaworklist_subst in H5; auto.
    destruct H5 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists ((Y, dbind_stvar_empty)::θ'0). repeat split; eauto.
    + constructor; auto. admit.
    + intros. admit.
    + intros. admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - admit.
  - dependent destruction H5.
    apply IHaworklist_subst in H5; auto.
    destruct H5 as [θ'0 [Htrans [Hbinds Hwfss]]].
    exists ((Y, dbind_typ T)::θ'0). repeat split; eauto.
    + constructor; auto. admit. admit.
    + intros. admit.
    + intros. admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
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

Ltac solve_awl_trailing_etvar :=
  match goal with
  | H_1 : ⊢ᵃʷ ?Γ, H_2: ?θ ⫦ ?Γ ⇝ ?Ω ⫣ ?θ' |- _ =>
    let Htr := fresh "Htr" in
    let Γ0 := fresh "Γ0" in
    let Htrans_et := fresh "Htrans_et" in
    let θ' := fresh "θ'" in
    apply aworklist_trailing_etvar_total in H_1 as Htr;
    destruct Htr as [Γ0 Htr];
    eapply aworklist_trailing_etvar_reduce_ord; eauto 
    ;
    apply aworklist_trailing_etvar_trans with (Γ0:=Γ0) in H_2 as Htrans_et ; auto;
    destruct Htrans_et as [θ' Htrans_et];
    dependent destruction Htrans_et;
    match goal with
    | H_3 : aworklist_trailing_etvar (aworklist_constvar ?Γ0 ?X abind_etvar_empty) ?Γ |- _ =>
      apply aworklist_trailing_base_ord in H_3; inversion H_3
    | _ => idtac
    end
  end.

Theorem d_a_wl_red_completness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃʷ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_completness.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros * Hwf Htrans;
    try destruct Htrans as [θ Htrans].
  - solve_awl_trailing_etvar.
    + dependent destruction Hwf... 
  - solve_awl_trailing_etvar.
    constructor. apply IHd_wl_red...
    admit.
  - solve_awl_trailing_etvar.
    constructor. eapply IHd_wl_red...
    admit.
  - solve_awl_trailing_etvar.
    constructor. apply IHd_wl_red...
    admit.
  - solve_awl_trailing_etvar.
    destruct_trans.
    + admit.
    + constructor...
      apply IHd_wl_red...
      admit.
  - solve_awl_trailing_etvar.
    destruct_trans.
    + admit.
    + constructor...
      apply IHd_wl_red...
      admit.
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
    + admit.
  - solve_awl_trailing_etvar.
    destruct_trans.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - solve_awl_trailing_etvar. 
    destruct_trans. 
    + admit.
    + admit.
    + admit.
    + admit.
  - solve_awl_trailing_etvar. 
    + admit.
  - solve_awl_trailing_etvar. 
    + admit.
  - solve_awl_trailing_etvar. 
    + admit.
  - solve_awl_trailing_etvar. 
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.

  (* check *)
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.

  (* infer *)
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.

  (* inftapp *)
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.

  (* infabs *)
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.
  - solve_awl_trailing_etvar.
    + admit.

  (* apply *)
  - solve_awl_trailing_etvar.
    + admit.
Admitted.
