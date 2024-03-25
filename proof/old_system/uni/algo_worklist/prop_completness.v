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
  intros. induction H2; simpl in *.
  - dependent destruction H3.
    exists θ'; repeat split; auto.
    + admit.
    + admit. 
Admitted.


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
