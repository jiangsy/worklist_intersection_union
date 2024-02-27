Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_typing.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wf_wl : Hdb_a_wl_red_soundness.
Hint Constructors trans_typ : Hdb_a_wl_red_soundness.
Hint Constructors trans_cont : Hdb_a_wl_red_soundness.
Hint Constructors trans_work : Hdb_a_wl_red_soundness.
Hint Constructors trans_worklist : Hdb_a_wl_red_soundness.
Hint Constructors wf_ss : Hdb_a_wl_red_soundness.
Hint Constructors d_wl_del_red : Hdb_a_wl_red_soundness.


Hint Resolve wf_ss_uniq : Hdb_a_wl_red_soundness.
Hint Resolve a_wf_wl_d_wf_env : Hdb_a_wl_red_soundness.


Hint Constructors d_sub : Hdb_a_wl_red_soundness.
Hint Constructors d_typing : Hdb_a_wl_red_soundness.
Hint Constructors d_infabs : Hdb_a_wl_red_soundness.
Hint Constructors d_inftapp : Hdb_a_wl_red_soundness.


Theorem a_mono_typ_wf : forall aE A,
  a_mono_typ aE A -> a_wf_typ aE A.
Proof.
  intros. induction H; auto.
  eapply a_wf_typ__etvar; eauto.
Qed.

Hint Resolve a_mono_typ_wf : Hdb_a_wl_red_soundness.


Ltac unify_trans_typ :=
  match goal with
  | H_1 : trans_typ ?θ ?Aᵃ ?A1ᵈ, H_2 : trans_typ ?θ ?Aᵃ ?A2ᵈ |- _ => eapply trans_typ_det in H_1; 
      eauto with Hdb_a_wl_red_soundness; subst
  end.

Ltac unify_trans_exp :=
  match goal with
  | H_1 : trans_exp ?θ ?eᵃ ?e1ᵈ, H_2 : trans_exp ?θ ?eᵃ ?e2ᵈ |- _ => eapply trans_exp_det in H_1; 
      eauto with Hdb_a_wl_red_soundness; subst
  end.
  


(* depedent destruction all non-atomic trans_* relation *)
Ltac destruct_trans :=
  repeat
    lazymatch goal with
    | H : trans_worklist ?θ (aworklist_conswork ?Γ ?w) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ (aworklist_consvar ?Γ ?w ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ  (aworklist_constvar ?Γ ?X ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _ _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_cont ?θ (?C_C _) ?wᵈ |- _ => dependent destruction H
    | H : trans_cont ?θ (?C_C _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ typ_unit ?Aᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ typ_bot ?Aᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ typ_top ?Aᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ (open_typ_wrt_typ _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ (?C_T _ _) ?Aᵈ |- _ => dependent destruction H
    end;
    try unify_trans_typ;
    try unify_trans_exp.

(* match the name of a_typ and d_typ in trans_typ *)
Ltac rename_typ :=
  lazymatch goal with
  | H : trans_typ ?θ (open_typ_wrt_typ _ _) ?Aᵈ |- _ => fail
  | H : trans_typ ?θ (?C_T _ _) ?Aᵈ |- _ => fail
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ, _ : trans_typ ?θ ?A2ᵃ ?A2ᵈ, _ : trans_typ ?θ ?A3ᵃ ?A3ᵈ, _ : trans_typ ?θ ?A4ᵃ ?A4ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵃ"ᵈ0" in 
    rename A1ᵈ into A1ᵃ1;
    let A2ᵃ1 := fresh A2ᵃ"ᵈ0" in
    rename A2ᵈ into A2ᵃ1;
    let A3ᵃ1 := fresh A3ᵃ"ᵈ0" in
    rename A3ᵈ into A3ᵃ1;
    let A4ᵃ1 := fresh A4ᵃ"ᵈ0" in
    rename A4ᵈ into A4ᵃ1;
    let A1ᵃ2 := fresh A1ᵃ"ᵈ" in 
    rename A1ᵃ1 into A1ᵃ2;
    let A2ᵃ2 := fresh A2ᵃ"ᵈ" in
    rename A2ᵃ1 into A2ᵃ2;
    let A3ᵃ2 := fresh A3ᵃ"ᵈ" in
    rename A3ᵃ1 into A3ᵃ2;
    let A4ᵃ2 := fresh A4ᵃ"ᵈ" in
    rename A4ᵃ1 into A4ᵃ2
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ, _ : trans_typ ?θ ?A2ᵃ ?A2ᵈ, _ : trans_typ ?θ ?A3ᵃ ?A3ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵃ"ᵈ0" in 
    rename A1ᵈ into A1ᵃ1;
    let A2ᵃ1 := fresh A2ᵃ"ᵈ0" in
    rename A2ᵈ into A2ᵃ1;
    let A3ᵃ1 := fresh A3ᵃ"ᵈ0" in
    rename A3ᵈ into A3ᵃ1;
    let A1ᵃ2 := fresh A1ᵃ"ᵈ" in 
    rename A1ᵃ1 into A1ᵃ2;
    let A2ᵃ2 := fresh A2ᵃ"ᵈ" in
    rename A2ᵃ1 into A2ᵃ2;
    let A3ᵃ2 := fresh A3ᵃ"ᵈ" in
    rename A3ᵃ1 into A3ᵃ2
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ, _ : trans_typ ?θ ?A2ᵃ ?A2ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵃ"ᵈ0" in 
    rename A1ᵈ into A1ᵃ1;
    let A2ᵃ1 := fresh A2ᵃ"ᵈ0" in
    rename A2ᵈ into A2ᵃ1;
    let A1ᵃ2 := fresh A1ᵃ"ᵈ" in 
    rename A1ᵃ1 into A1ᵃ2;
    let A2ᵃ2 := fresh A2ᵃ"ᵈ" in
    rename A2ᵃ1 into A2ᵃ2
  | _ : trans_typ ?θ ?A1ᵃ ?A1ᵈ |- _ => 
    let A1ᵃ1 := fresh A1ᵃ"ᵈ0" in 
    rename A1ᵈ into A1ᵃ1;
    let A1ᵃ2 := fresh A1ᵃ"ᵈ" in 
    rename A1ᵃ1 into A1ᵃ2
  end. 


(* assert the well-formedness and apply the induction hypothesis  *)
Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵃ ?Γ) -> ?P |- _ => destruct_a_wf_wl; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃ Γ) by auto with Hdb_a_wl_red_soundness;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2;
      destruct H2 as [Ω [Htrans Hdred]];
      destruct Htrans as [θ Htrans]
    end.

Hint Resolve a_wf_wl_wf_ss : Hdb_a_wl_red_soundness.

Ltac trans_all_typ :=
  match goal with 
  | H5 : nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ |- _ => 
    repeat
    match goal with 
    | H1 : a_wf_typ (awl_to_aenv ?Γ) ?C |- _ =>
      let H3 := fresh "Htrans" in
      let H4 := fresh "Htrans"  in
      let C1 := fresh C"ᵈ" in
        lazymatch goal with
        | _ : trans_typ θ C ?Cᵈ |- _ => fail
        | _ : _ |- _ =>
        eapply a_wf_typ_trans_typ in H1 as H3; eauto with Hdb_a_wl_red_soundness
        end;
        destruct H3 as [C1]
    end
  end.


(* define a extended relation of a_update_bound extended with Ω and θ ? *)

(* Lemma a_update_bound_transfer_same_dworklist: forall Γ Ω θ X A E m Γ1 Γ2 LB UB,
  a_update_bound Γ X A m E Γ1 Γ2 LB UB ->
  trans_worklist nil (awl_rev_app Γ2 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ1) X (abind_bound LB UB)) )  Ω θ ->
  exists θ', trans_worklist nil Γ Ω θ'.
Proof with auto with Hdb_a_wl_red_soundness.
  intros. generalize dependent θ. generalize dependent Ω. dependent induction H.
  - intros. simpl in *. exists θ. auto. admit. 
  - intros. simpl in *. admit.
  - admit.
  - intros. admit.
  - admit.
  - admit.
  - intros. admit.
  - intros. simpl in *. exists θ.
     admit.
  - intros. simpl in H0. dependent destruction H0.
Admitted. *)

Inductive d_more_constr_worklist : dworklist -> dworklist -> Prop :=
  | d_mc_worklist__empty : d_more_constr_worklist dworklist_empty dworklist_empty
  | d_mc_worklist__consvar : forall Ω Ω' x b,
    d_more_constr_worklist Ω Ω' ->
    d_more_constr_worklist (dworklist_consvar Ω x b) (dworklist_consvar Ω' x b)
  | d_mc_worklist__constvar : forall Ω Ω' X b,
    d_more_constr_worklist Ω Ω' ->
    d_more_constr_worklist (dworklist_constvar Ω X b) (dworklist_constvar Ω' X b)
  | d_mc_worklist__conswork : forall Ω Ω' w,
    d_more_constr_worklist Ω Ω' ->
    d_more_constr_worklist (dworklist_conswork Ω w) (dworklist_conswork Ω' w)
  | d_mc_worklist__skipwork : forall Ω Ω' w,
    d_more_constr_worklist Ω Ω' ->
    d_more_constr_worklist (w ⫤ Ω) Ω'
  | d_mc_worklist__mcsub : forall Ω Ω' A1 A2 B1 B2,
    d_more_constr_worklist Ω Ω' ->
    dwl_to_denv Ω ⊢ A1 <: A2 ->
    dwl_to_denv Ω ⊢ B2 <: B1 ->
    d_more_constr_worklist (work_sub A1 B1 ⫤ Ω) (work_sub A2 B2 ⫤ Ω')
  .

    
Lemma d_more_constr_worklist_refl : forall Ω, d_more_constr_worklist Ω Ω.
Proof.
  intros. induction Ω; try constructor; auto.
Qed.


Lemma d_more_constr_worklist_red_weakeing : forall Ω' Ω,
  d_more_constr_worklist Ω' Ω ->
  Ω'⟶ᵈ⁎⋅ ->
  Ω ⟶ᵈ⁎⋅.
Proof.
  intros. induction H.
  - auto.
Admitted.


Lemma d_morew_worklist_trans : forall Ω1 Ω2 Ω3, d_more_constr_worklist Ω3 Ω2 -> d_more_constr_worklist Ω2 Ω1 ->
  d_more_constr_worklist Ω3 Ω1.
Proof.
  intros. generalize dependent Ω1. generalize dependent Ω2. induction Ω3; intros. 
  - dependent destruction H. 
    dependent destruction H0. constructor. 
  - dependent destruction H. 
    dependent induction H0. 
    constructor. eapply IHΩ3; eauto.
  - dependent destruction H. 
    dependent induction H0. 
    constructor. eapply IHΩ3; eauto.
  - dependent induction H. 
    + dependent induction H0.   
      * apply d_mc_worklist__conswork. eapply IHΩ3; eauto.
      * apply d_mc_worklist__skipwork. eapply IHΩ3; eauto.
      * apply d_mc_worklist__mcsub. eapply IHΩ3; eauto.
        admit. admit.
    + econstructor. eapply IHΩ3; eauto. 
    + dependent induction H2.
      * apply d_mc_worklist__mcsub. eapply IHΩ3; eauto.
        admit. admit.
      * apply d_mc_worklist__skipwork. eapply IHΩ3; eauto.
      * apply d_mc_worklist__mcsub. eapply IHΩ3; eauto.
        admit. admit.
  all: fail.
Admitted.
(* inversion lemma for θ *)

Lemma a_insert_fresh_evar_before_similar_worklist : forall Γ Γ' Γ'' X Y Ω' θ',
  a_insert_fresh_evar_before Γ X Y Γ' Γ'' ->
  trans_worklist nil (awl_app Γ'' Γ') Ω' θ' ->
  exists θ Ω, trans_worklist nil Γ Ω θ /\ d_more_constr_worklist Ω' Ω.
Proof.
  intros. generalize dependent θ'. generalize dependent Ω'. dependent induction H; intros.
  - simpl in H0.
    dependent destruction H0.
    dependent destruction H0. simpl in *.
    simpl in *. exists ((X , dbind_typ T) :: θ').
    exists (dworklist_conswork Ω (work_sub Aᵈ Bᵈ)); split; auto.
    econstructor; eauto.
    admit. (* trans_weaken *)
    admit. (* trans_weaken *)
    apply d_mc_worklist__conswork.
    apply d_mc_worklist__skipwork.
    apply d_more_constr_worklist_refl.
  - simpl in H1.
    dependent destruction H1.
    + apply IHa_insert_fresh_evar_before in H1.
      destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
      exists ((X1 , dbind_tvar_empty) :: θ'1). 
      exists (dworklist_constvar Ω' X1 dbind_tvar_empty); split.
      constructor; auto.
      constructor; auto.
    + apply IHa_insert_fresh_evar_before in H1.
      destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
      exists ((X1 , dbind_stvar_empty) :: θ'1). 
      exists (dworklist_constvar Ω' X1 dbind_stvar_empty); split.
      constructor; auto.
      constructor; auto.
    + apply IHa_insert_fresh_evar_before in H1.
      destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
      exists ((X1 , dbind_typ T) :: θ'1). 
      exists (dworklist_conswork Ω' (work_sub Aᵈ Bᵈ)); split.
      econstructor; eauto.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
  - simpl in H0.
    dependent destruction H0.
    admit.
  - simpl in H0.
    dependent destruction H0.
    apply IHa_insert_fresh_evar_before in H0.
    destruct H0 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists (wᵈ ⫤ Ω')%dworklist. 
    split; auto.
    constructor; auto.
Admitted.


Lemma a_insert_fresh_evar_before_similar_worklist' : forall Γ Γ' Γ'' X Y Ω' θ',
  a_insert_fresh_evar_before Γ X Y Γ' Γ'' ->
  trans_worklist nil (awl_app Γ'' Γ') Ω' θ' ->
  exists θ Ω, trans_worklist nil Γ Ω θ /\ d_more_constr_worklist Ω' Ω /\ (forall X b, X <> Y -> binds X b θ <-> binds X b θ').
Proof.
  intros. generalize dependent θ'. generalize dependent Ω'. dependent induction H; intros.
  - simpl in H0.
    dependent destruction H0.
    dependent destruction H0. simpl in *.
    simpl in *. exists ((X , dbind_typ T) :: θ').
    exists (dworklist_conswork Ω (work_sub Aᵈ Bᵈ)); repeat split; auto.
    econstructor; eauto.
    admit. (* trans_weaken *)
    admit. (* trans_weaken *)
    apply d_mc_worklist__conswork.
    apply d_mc_worklist__skipwork.
    apply d_more_constr_worklist_refl.
    admit.
    admit.
  - simpl in H1.
    dependent destruction H1.
    + apply IHa_insert_fresh_evar_before in H1.
      destruct H1 as [θ'1 [Ω' [Htrans [Hmw Hb]]]].
      exists ((X1 , dbind_tvar_empty) :: θ'1). 
      exists (dworklist_constvar Ω' X1 dbind_tvar_empty); repeat split.
      constructor; auto.
      constructor; auto.
      admit.
      admit.
    + apply IHa_insert_fresh_evar_before in H1.
      destruct H1 as [θ'1 [Ω' [Htrans [Hmw Hb]]]].
      exists ((X1 , dbind_stvar_empty) :: θ'1). 
      exists (dworklist_constvar Ω' X1 dbind_stvar_empty); repeat split.
      constructor; auto.
      constructor; auto.
      admit.
      admit.
    + apply IHa_insert_fresh_evar_before in H1.
      destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
      exists ((X1 , dbind_typ T) :: θ'1). 
      exists (dworklist_conswork Ω' (work_sub Aᵈ Bᵈ)); split.
      econstructor; eauto.
      admit.
      admit.
      admit.
      admit.
      admit.
      admit.
  - simpl in H0.
    dependent destruction H0.
    admit.
  - simpl in H0.
    dependent destruction H0.
    apply IHa_insert_fresh_evar_before in H0.
    destruct H0 as [θ'1 [Ω' [Htrans [Hmw Hb]]]].
    exists θ'1. exists (wᵈ ⫤ Ω')%dworklist. 
    repeat split; eauto.
    constructor; auto.
    admit.
    admit.
    now apply Hb.
    now apply Hb.
Admitted.


Lemma a_update_transfer_similar_worklist : forall Γ Γ' X A B Ω' θ' m,
  a_bound_update m Γ X A Γ' B ->
  trans_worklist nil Γ' Ω' θ' ->
  exists θ Ω, trans_worklist nil Γ Ω θ /\ d_more_constr_worklist Ω' Ω.
Proof.
  intros. generalize dependent θ'. generalize dependent Ω'. dependent induction H.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros. apply IHa_bound_update2 in H1. 
    destruct H1 as [θ1 [Ω1 [Htrans1 Hmw1]]].
    apply IHa_bound_update1 in Htrans1.
    destruct Htrans1 as [θ2 [Ω2 [Htrans2 Hmw2]]].
    exists θ2, Ω2. split; auto.
    eapply d_morew_worklist_trans; eauto.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros.
    dependent destruction H4.
    dependent destruction H4.
    dependent destruction H5.
    dependent destruction H7.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ) in H3; auto.
    destruct H3 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros. 
    dependent destruction H4.
    dependent destruction H4.
    dependent destruction H5.
    dependent destruction H7.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ) in H3; auto.
    destruct H3 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros.    
    dependent destruction H2.
    dependent destruction H2.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ') in H1; auto.
    destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros.    
    dependent destruction H2.
    dependent destruction H2.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ') in H1; auto.
    destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros. apply IHa_bound_update2 in H1. 
    destruct H1 as [θ1 [Ω1 [Htrans1 Hmw1]]].
    apply IHa_bound_update1 in Htrans1.
    destruct Htrans1 as [θ2 [Ω2 [Htrans2 Hmw2]]].
    exists θ2, Ω2. split; auto.
    eapply d_morew_worklist_trans; eauto.
  - intros. exists θ'. exists Ω'. split; auto. apply d_more_constr_worklist_refl.
  - intros.
    dependent destruction H4.
    dependent destruction H4.
    dependent destruction H5.
    dependent destruction H7.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ) in H3; auto.
    destruct H3 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros. 
    dependent destruction H4.
    dependent destruction H4.
    dependent destruction H5.
    dependent destruction H7.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ) in H3; auto.
    destruct H3 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros.    
    dependent destruction H2.
    dependent destruction H2.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ') in H1; auto.
    destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
  - intros.    
    dependent destruction H2.
    dependent destruction H2.
    eapply a_insert_fresh_evar_before_similar_worklist  with (Ω':=Ω) (θ':=θ') in H1; auto.
    destruct H1 as [θ'1 [Ω' [Htrans Hmw]]].
    exists θ'1. exists Ω'. split. auto.
    apply d_mc_worklist__skipwork. apply d_mc_worklist__skipwork. auto.
Qed.

Lemma a_reorder_transfer_similar_worklist: forall Γ Ω θ X A E m Γ1 Γ2 LB UB,
  a_reorder Γ X A m E Γ1 Γ2 LB UB ->
  trans_worklist nil (awl_rev_app Γ2 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ1) X (abind_bound LB UB)) ) Ω θ ->
  exists θ' Ω', trans_worklist nil Γ Ω' θ' /\ d_morew_worklist Ω Ω'.
Proof with auto with Hdb_a_wl_red_soundness.
  intros. generalize dependent θ. generalize dependent Ω. dependent induction H.
  - intros. simpl in *. admit.
  - intros. simpl in *. admit.
  - admit.
  - intros. admit.
  - admit.
  - admit.
  - intros. admit.
  - intros. simpl in *. exists θ.
     admit.
Admitted.



(* Hint Resolve d_chk_inf_wft : Hdb_a_wl_red_soundness. *)

Hint Constructors trans_typ : Hdb_a_wl_red_soundness.
Hint Constructors trans_exp : Hdb_a_wl_red_soundness.
Hint Constructors trans_cont : Hdb_a_wl_red_soundness.
Hint Constructors trans_work : Hdb_a_wl_red_soundness.
Hint Constructors trans_worklist : Hdb_a_wl_red_soundness.

Hint Resolve trans_typ_lc_atyp : Hdb_a_wl_red_soundness.

Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto with Hdb_a_wl_red_soundness.
  intros * Hwfa Hared. dependent induction Hared; auto; unfold transfer in *;
    try _apply_IH_a_wl_red; try destruct_trans; try trans_all_typ; try rename_typ.
  - exists dworklist_empty. intuition...
  - exists (dworklist_consvar Ω x (dbind_typ Aᵈ))...
  - exists (dworklist_constvar Ω X dbind_tvar_empty)...
    split... exists ((X, dbind_tvar_empty) :: θ)...
  - exists (dworklist_constvar Ω X dbind_stvar_empty)...
    split... exists ((X, dbind_stvar_empty) :: θ)...
  - destruct_a_wf_wl; intuition; subst; _apply_IH_a_wl_red.
    + apply a_mono_typ_wf in H2.
      apply a_mono_typ_wf in H0.
      destruct_trans.
      dependent destruction Hdred.
      exists Ω. split...
      exists (X ~ (dbind_typ A1ᵈ) ++ θ).
      econstructor... admit. admit.
    + dependent destruction Htrans. trans_all_typ. admit.
    + admit.
    + admit.
  - exists (dworklist_conswork Ω (work_sub B1ᵈ typ_top)); split...
    exists θ... econstructor... econstructor... admit.
  - exists (dworklist_conswork Ω (work_sub typ_bot Aᵈ)); split...
    exists θ... econstructor... econstructor... admit.
  - exists (dworklist_conswork Ω (work_sub typ_unit typ_unit)).
    split... exists θ... 
    econstructor...   econstructor...
  - clear H0. dependent destruction H.
    + admit.
    + admit.
    + admit.
  - exists ((work_sub (typ_arrow B1ᵈ B2ᵈ) (typ_arrow A1ᵈ A2ᵈ) ⫤ Ω)%dworklist).
    split. exists θ. auto...
    econstructor.
    econstructor.
    + apply d_wl_red_weaken_work1 in Hdred. dependent destruction Hdred...
    + apply d_wl_red_weaken_work2 in Hdred. dependent destruction Hdred...
    + dependent destruction Hdred. dependent destruction Hdred...
  (* forall x. A < B  *)
  - inst_cofinites_by (L `union` ftvar_in_typ A1) using_name X.
    assert ( ⊢ᵃ (work_sub (B1 ^ᵈ X) A1 ⫤ aworklist_constvar Γ X (abind_bound typ_bot typ_top))) by admit.
    destruct_a_wf_wl.
    _apply_IH_a_wl_red.
    destruct_trans.
    rename A1ᵈ into B1tᵈ. rename B1ᵈ into A1ᵈ.
    apply trans_typ_etvar_tvar_subst_cons in H16...
    destruct H16 as [B1xᵈ].
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) A1ᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ. econstructor...
      econstructor... econstructor.
      admit. admit.
    + econstructor. 
      eapply d_sub__alll with (T:=T) (L:=L)...
      * admit.
      * admit.
      * admit.
      * intros. inst_cofinites_with X0.
        erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X B1xᵈ)) by apply close_typ_notin.
        rewrite open_typ_wrt_typ_close_typ_wrt_typ.
        admit.
      * admit.
    + admit.
  - destruct_a_wf_wl.
    dependent destruction H. dependent destruction H1.
    inst_cofinites_by (L `union` L0 `union` L1 `union` dom (awl_to_aenv Γ)) using_name X.
    assert ( ⊢ᵃ (work_sub (B1 ^ᵈ X) (A1 ^ᵈ X) ⫤ aworklist_constvar Γ X abind_stvar_empty) ) by admit.
    _apply_IH_a_wl_red.
    destruct_trans...
    rename A1ᵈ into B1xᵈ. rename B1ᵈ into A1xᵈ.
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) (typ_all (close_typ_wrt_typ X A1xᵈ)) ⫤ Ω)%dworklist.
    split.
    + exists θ'. econstructor...
      econstructor...
      * econstructor... admit.
      * admit.
    + dependent destruction Hdred. 
      econstructor...
      admit.
      * dependent destruction Hdred...
  (* ^X < A1 -> A2 *)
  - inst_cofinites_by L using_name X1.
    inst_cofinites_by (L `union` singleton X1) using_name X2.
    admit.  
  (* A1 -> A2 < ^X  *)
  - inst_cofinites_by L using_name X1.
    inst_cofinites_by (L `union` singleton X1) using_name X2.
    admit.
  (* ^X < ^Y  *)
  - assert ( ⊢ᵃ awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB))) by admit.
    _apply_IH_a_wl_red.
    (* eapply a_update_bound_transfer_same_dworklist in Htrans... *)
    admit.
  (* ^X < ^Y  *)
  - admit.
  (* τ < ^X *)
  - admit.
  (* ^X < τ *)
  - admit.
  (* e <= A *)
  - exists (work_check eᵈ A1ᵈ ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
  (* \ x. e <= A1 -> A2 *)
  - admit.
  (* \ x. e <= ^X *)
  - admit.
  - destruct_a_wf_wl. inst_cofinites_by (L `union` L0).
    assert ( ⊢ᵃ (work_check (open_exp_wrt_exp e (exp_var_f x)) typ_top ⫤ (aworklist_consvar Γ x (abind_typ typ_bot)))) by admit.
    apply H3 in H4. 
    destruct H4 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans.
    admit.
  - destruct_a_wf_wl.
    assert (⊢ᵃ (work_apply c A0 ⫤ Γ)). econstructor... econstructor...
    admit.
    apply IHHared in H2. destruct H2 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans. rename_typ.
    exists (work_infer (exp_var_f x) cᵈ ⫤ Ω)%dworklist.
    split... exists θ. econstructor... econstructor...
    admit.
  - exists (work_infer (exp_anno eᵈ Aᵈ) cᵈ ⫤ Ω)%dworklist...
    split. exists θ...
    destruct_d_wl_del_red.
    econstructor...
    eapply d_typing__infanno...
    eapply d_chk_inf_wft...
  (* /\ a. e : A => _ *)
  - admit.
  - exists (work_infer exp_unit cᵈ ⫤ Ω)%dworklist...
    split. exists θ... 
    econstructor...
  - exists (work_infer (exp_app eᵈ eᵈ0) cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
    eapply d_wl_del_red__inf with (T1:=T3)...
    econstructor...
      apply d_wl_red_weaken_work1 in Hdred. dependent destruction Hdred...
    apply d_wl_red_weaken_work2 in Hdred...
  - exists (work_infapp  (typ_arrow A1ᵈ A2ᵈ) eᵈ cᵈ ⫤ Ω)%dworklist...
    split. destruct_d_wl_del_red. exists Θ...
    econstructor...
  - exists (work_infabs (typ_arrow A1ᵈ B1ᵈ) cᵈ ⫤ Ω)%dworklist...
    split. destruct_d_wl_del_red. exists θ... 
    econstructor... clear H2.
    econstructor... 
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A1)...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=B1)...
  - exists (work_infabs typ_bot cᵈ ⫤ Ω)%dworklist...
    split...
    destruct_d_wl_del_red...
    dependent destruction H5...
  (* ∀ a. A ▹ _ *)
  - admit.
  (* ^X ▹ _ *)
  - inst_cofinites_by L using_name X1.
    inst_cofinites_by (L `union` singleton X0) using_name X2.
    admit.
  - exists (work_infer (exp_tapp eᵈ Bᵈ) cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  (* ∀ a. A ∘ B =>=> _ *)
  - assert (⊢ᵃ (work_apply c (A ^^ᵈ B) ⫤ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    inst_cofinites_by (dom (awl_to_aenv Γ) `union` dom θ) using_name X.
    replace (A ^^ᵈ B) with ({B /ᵗ X} A ^ᵈ X) in H7 by admit.
    eapply trans_typ_rev_subs_cons in H7...
    admit.
    admit.
    admit.
    (* destruct H7 as [Axᵈ]. intuition.
    exists (work_inftapp (typ_all (close_typ_wrt_typ X Axᵈ )) Bᵈ cᵈ ⫤ Ω)%dworklist.
    split.
    exists θ.
    + econstructor...
      econstructor...
      admit.
    + eapply d_wl_del_red__inftapp with (T3:=A1ᵈ)...
      admit. *)
  - exists (work_inftapp typ_bot Bᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    econstructor... econstructor...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=B)...
  - destruct_a_wf_wl.
    eapply a_wf_work_applied in H1...
    assert ( ⊢ᵃ (w ⫤ Γ) ) by auto.
    apply IHHared in H2...
    destruct H2 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    trans_all_typ.
    admit.
Admitted.
