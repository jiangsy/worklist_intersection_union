Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wl_red : Hdb_a_wl_red_completness.



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
| awl_t_o__work : forall Γ w, aworklist_ord (aworklist_conswork Γ w)
| awl_t_o__var : forall Γ x ab, aworklist_ord (aworklist_consvar Γ x ab)
| awl_t_o__tvar : forall Γ X, aworklist_ord (aworklist_constvar Γ X abind_tvar_empty)
| awl_t_o__stvar : forall Γ X, aworklist_ord (aworklist_constvar Γ X abind_tvar_empty).

Inductive aworklist_trailing_etvar : aworklist -> aworklist -> Prop :=
| awl_t_e__base : forall Γ0, aworklist_ord Γ0 -> aworklist_trailing_etvar Γ0 Γ0
| awl_t_e__etvar : forall Γ0 Γ X, aworklist_trailing_etvar Γ0 Γ -> aworklist_trailing_etvar Γ0 
  (aworklist_constvar Γ X abind_etvar_empty).

Lemma aworklist_trailing_etvar_reduce_ord : forall Γ0 Γ,
  aworklist_trailing_etvar Γ0 Γ -> Γ0 ⟶ᵃʷ⁎⋅ -> Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros. induction H; auto.
  constructor; auto.
Qed.

Theorem d_a_wl_red_completness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃʷ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with auto with Hdb_a_wl_red_completness.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros * Hwf Htrans;
    try destruct Htrans as [θ Htrans].
  - dependent induction Htrans...
    + dependent destruction Hwf... 
  - dependent induction Htrans...
    + constructor. apply IHd_wl_red.
      dependent destruction Hwf... 
      exists θ'...
    + constructor. eapply IHHtrans; eauto.
      dependent destruction Hwf... 
  - dependent induction Htrans...
    + constructor. apply IHd_wl_red.
      dependent destruction Hwf... 
      exists θ'...
    + constructor. eapply IHHtrans; eauto.
      dependent destruction Hwf...
  - dependent induction Htrans...
      + constructor. apply IHd_wl_red.
        dependent destruction Hwf... 
        exists θ'...
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans...
    + dependent destruction H0.
      dependent destruction H0.
      * admit.
      * constructor; auto. 
        apply IHd_wl_red; auto.
        dependent destruction Hwf... 
        exists θ...
    + constructor. eapply IHHtrans; eauto.
      dependent destruction Hwf...
  - dependent induction Htrans...
      + dependent destruction H0.
        dependent destruction H.
        * admit.
        * constructor; auto. 
          apply IHd_wl_red; auto.
          dependent destruction Hwf... 
          exists θ...
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans...
    + dependent destruction H0.
      dependent destruction H. 
      * dependent destruction H1.
        assert (exists Γ1, exists Γ2, aworklist_subst Γ X0 ` X Γ1 Γ2) by admit.    
        destruct H4 as [Γ1 [Γ2 Hws]].
        -- eapply a_wl_red__sub_etvarmono1 with (Γ1:=Γ1) (Γ2:=Γ2); auto.
          ++ admit.
          ++ admit.
          ++ admit.
          ++ eapply a_worklist_subst_transfer_same_dworklist_rev with (Ω:=Ω) (θ:=θ) (Tᵈ:=typ_unit) in Hws; auto.
             ** destruct Hws as [θ'' [Htranswl [Hbinds Hwfss]]].
                apply IHd_wl_red; eauto. 
                --- admit. (* wf *)
             ** admit.
             ** admit.
             ** admit.
             ** apply trans_typ_binds_etvar; auto.
             ** apply trans_typ_binds_etvar; auto.
        -- admit.
      * dependent destruction H0.
        admit.
        admit.
    + constructor. eapply IHHtrans; eauto.
      dependent destruction Hwf...
  - dependent induction Htrans.
    + admit.
    + constructor. eapply IHHtrans; eauto.
      dependent destruction Hwf...
  - intros.
    assert (exists Γ0, aworklist_ord Γ0 /\ aworklist_trailing_etvar Γ0 Γ).
    admit.
    destruct H0 as [Γ0 [Haword Hawte]].
    apply aworklist_trailing_etvar_reduce_ord with (Γ0:=Γ0); auto.
    assert (exists θ', nil ⫦ Γ0 ⇝ work_sub (typ_arrow A1 A2) (typ_arrow B1 B2) ⫤ Ω ⫣ θ') by admit.
    destruct H0 as [θ'].
    dependent destruction H0.
    + dependent destruction H1. 
      dependent destruction H1.

    
    admit.
    + inversion Haword.

    
    (* induction H; intros.
    + constructor.
    + inversion Htrans.
    + inversion Htrans.
    + dependent destruction Htrans. admit.
    + constructor. eapply IHaworklist_trailing_etvar. *)

  - dependent destruction Htrans.
    + admit.
    +
  - dependent induction Htrans.
    + admit.
    + constructor. eapply IHHtrans; eauto.
      dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...

  (* check *)
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...

  (* infer *)
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...

  (* inftapp *)
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...

  (* infabs *)
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...

  (* apply *)
  - dependent induction Htrans.
      + admit.
      + constructor. eapply IHHtrans; eauto.
        dependent destruction Hwf...
Admitted.
