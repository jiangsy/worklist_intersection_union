Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import uni.decl.prop_typing.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wf_wl : Hdb_a_wl_red_soundness.
Hint Constructors trans_typ : Hdb_a_wl_red_soundness.
Hint Constructors trans_exp : Hdb_a_wl_red_soundness.
Hint Constructors trans_cont : Hdb_a_wl_red_soundness.
Hint Constructors trans_work : Hdb_a_wl_red_soundness.
Hint Constructors trans_worklist : Hdb_a_wl_red_soundness.
Hint Constructors wf_ss : Hdb_a_wl_red_soundness.
Hint Constructors d_wl_del_red : Hdb_a_wl_red_soundness.
Hint Constructors aworklist_subst : Hdb_a_wl_red_soundness.

Hint Resolve wf_ss_uniq : Hdb_a_wl_red_soundness.
Hint Resolve a_wf_wl_d_wf_env : Hdb_a_wl_red_soundness.


Hint Constructors d_sub : Hdb_a_wl_red_soundness.
Hint Constructors d_typing : Hdb_a_wl_red_soundness.
Hint Constructors d_infabs : Hdb_a_wl_red_soundness.
Hint Constructors d_inftapp : Hdb_a_wl_red_soundness.


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


Theorem a_mono_typ_wf : forall aE A,
  a_mono_typ aE A -> a_wf_typ aE A.
Proof.
  intros. induction H; auto.
Qed.

Hint Resolve a_mono_typ_wf : Hdb_a_wl_red_soundness.

(* assert the well-formedness and apply the induction hypothesis  *)
Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵃʷ ?Γ) -> ?P |- _ => destruct_a_wf_wl; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃʷ Γ) by auto with Hdb_a_wl_red_soundness;
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
        eapply trans_typ_total in H1 as H3; eauto with Hdb_a_wl_red_soundness
        end;
        destruct H3 as [C1]
    end
  end.



Lemma a_worklist_subst_transfer_same_dworklist: forall Γ Ω θ X T Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  a_mono_typ (awl_to_aenv Γ) T ->
  X `notin` ftvar_in_typ T ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  trans_worklist nil (awl_app (subst_tvar_in_aworklist T X Γ2) Γ1)  Ω θ ->
  exists θ' Tᵈ, 
      trans_worklist nil Γ Ω θ' /\ 
      θ ⫦ᵗ T ⇝ Tᵈ /\ 
      θ' ⫦ᵗ T ⇝ Tᵈ /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      binds X (dbind_typ Tᵈ) θ' /\
      wf_ss θ'.
Proof with auto with Hdb_a_wl_red_soundness.
  intros. generalize dependent θ. generalize dependent Ω. dependent induction H2; intros.
  - simpl in *.
    assert (exists Aᵈ, θ ⫦ᵗ A ⇝ Aᵈ) by admit.
    destruct H2 as [Aᵈ].
    exists ((X ~ dbind_typ Aᵈ) ++ θ). 
    exists Aᵈ.
    repeat split; auto.
    + econstructor; auto.  
      * admit. (* OK, notin *)
      * admit. (* OK, mono *)
    + admit. (* OK, trans_typ_weaken *)
    + admit. (* OK, wf_ss *)
    + admit. (* OK, mono *)
  - dependent destruction H3. 
    apply IHaworklist_subst in H3 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].
    exists θ'1. exists Tᵈ. repeat split; auto.
    + constructor. auto.
      eapply trans_typ_etvar_subst_same_ss; eauto.
      eapply trans_typ_reorder with (θ:=θ'); eauto.
      eapply a_wf_wl_wf_ss; eauto.
      intros. apply Hbinds... 
      admit. (* OK, neq *)
    + intros. apply Hbinds; auto.
    + intros. apply Hbinds; auto.
    + destruct_a_wf_wl...
    + admit. (* OK, mono *)
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists ((Y , dbind_tvar_empty) :: θ'1), Tᵈ. repeat split; auto.
    + econstructor; auto.
      admit. (* OK, notin *)
    + rewrite_env (nil ++ (Y ~ □) ++ θ'). apply trans_typ_weaken...
      constructor; auto.
      eapply a_wf_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ □) ++ θ'1). apply trans_typ_weaken...
      constructor; auto.
      admit. (* OK, notin *)
    + intros. inversion H8.
      * dependent destruction H9... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. inversion H8.
      * dependent destruction H9... 
      * simpl. apply binds_cons... apply Hbinds...
    + simpl. constructor; eauto. admit. (* OK, notin *)
    + destruct_a_wf_wl...
    + admit. (* OK, mono *)
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists (Y ~ dbind_stvar_empty ++ θ'1), Tᵈ. repeat split; auto.
    + econstructor; auto.
      admit. (* OK, notin *)
    + rewrite_env (nil ++ (Y ~ ■) ++ θ'). apply trans_typ_weaken...
      econstructor; auto.
      eapply a_wf_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ ■) ++ θ'1). apply trans_typ_weaken... 
      admit. (* OK, wf_ss *)
    + intros. inversion H8.
      * dependent destruction H9... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. inversion H8.
      * dependent destruction H9... 
      * simpl. apply binds_cons... apply Hbinds...
    + simpl. constructor... 
      admit. (* OK, notin *)
    + destruct_a_wf_wl...
    + admit. (* OK, mono *)
    + auto.
  (* work_stay *)
  - dependent destruction H3.
    apply IHaworklist_subst in H3 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists θ'1. exists Tᵈ. repeat split; auto.
    + constructor; auto.
      eapply trans_work_etvar_subst_same_ss; eauto.
      apply trans_work_reorder with (θ:=θ'); eauto.
      * eapply a_wf_wl_wf_ss; eauto.
      * intros. apply Hbinds; auto.
        unfold not. intros. subst.
        apply subst_tvar_in_work_fresh_same in H5; auto.
    + apply Hbinds...
    + apply Hbinds...
    + destruct_a_wf_wl...
    + simpl in H0...
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists (Y ~ dbind_typ T ++ θ'1). exists Tᵈ. repeat split; auto.
    + econstructor; auto. 
      admit. (* OK, notin *)
      admit. (* OK, mono *)
    + rewrite_env (nil ++ (Y ~ dbind_typ T) ++ θ'). apply trans_typ_weaken...
      constructor; auto.
      eapply a_wf_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ dbind_typ T) ++ θ'1). apply trans_typ_weaken...
      constructor; auto.
      admit. (* OK, notin *)
      admit. (* OK, mono *)
    + intros. inversion H9.
      * dependent destruction H10... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. inversion H9.
      * dependent destruction H10... 
      * simpl. apply binds_cons... apply Hbinds...
    + constructor; auto. 
      admit. (* OK, notin *)
      admit. (* OK, monos *)
    + destruct_a_wf_wl...
    + admit. (* OK, mono *)
    + auto.
  - simpl in *.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].
    apply trans_wl_split in Htrans.
    destruct Htrans as [Ω1 [Ω2 [θ' [Heq [Htrans1 Htrans2]]]]].
    dependent destruction Htrans1.
    dependent destruction Htrans1.
    apply trans_wl_split_ss in Htrans2 as Hsplitss.
    destruct Hsplitss as [θ'' Heqss]. rewrite Heqss in *.
    exists ((Y, dbind_typ T0) :: θ'' ++ (X, dbind_typ T) :: θ').
    exists Tᵈ. repeat split; auto.
    + constructor.
      rewrite_env ((X ~ dbind_typ T) ++ (Y, dbind_typ T0) :: θ') in Htrans2.
      rewrite_env ((θ'' ++ X ~ dbind_typ T) ++ (Y, dbind_typ T0) :: θ') in Htrans2.
      apply trans_wl_strengthen_etvar_gen in Htrans2.
      replace (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with (Γ2 ⧺ (X ~ᵃ ⬒ ;ᵃ Γ1))%aworklist by admit.
      rewrite Heq.
      eapply trans_wl_app with (θ2:= X~ dbind_typ T ++ θ'); eauto.
      constructor; eauto.
      rewrite_env ((θ'' ++ X ~ dbind_typ T) ++ θ').  auto.
      admit. (* OK, notin *)
      admit. (* OK, notin *)
      admit. (* OK, mono *)
    + eapply trans_typ_reorder with (θ:=θ'' ++ (X, dbind_typ T) :: (Y, dbind_typ T0) :: θ'); auto.
      admit. (* OK, wf_ss *)
      admit. (* OK, binds *)
    + intros. admit. (* OK, binds *)
    + intros. admit. (* OK, binds *)
    + admit. (* OK, binds *)
    + admit. (* OK, wf_ss *)
    + admit. (* OK, wf *)
    + admit. (* OK, mono *)
    + auto.
Admitted.

(* Hint Resolve d_chk_inf_wft : Hdb_a_wl_red_soundness. *)

Hint Constructors aworklist_subst : Hdb_a_wl_red_soundness.


Hint Resolve trans_typ_lc_atyp : Hdb_a_wl_red_soundness.


Ltac solve_notin_dom :=
  rewrite awl_to_aenv_app in *; rewrite dom_aenv_app_comm in *; simpl in *; auto.

Lemma worklist_subst_fresh_etvar_total : forall Γ1 Γ2 X X1 X2,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  X1 `notin` dom (awl_to_aenv (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)) ->
  X2 `notin` add X1 (dom (awl_to_aenv (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1))) ->
  aworklist_subst (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X
    (typ_arrow ` X1 ` X2) (X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) Γ2.
Proof with auto with Hdb_a_wl_red_soundness.
  induction Γ2; intros; simpl in *; auto.
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
    constructor; simpl...
    replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X1 ~ᵃ ⬒ ;ᵃ aworklist_empty ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
    constructor; simpl...
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) x ab)%aworklist with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar Γ2 x ab) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
    constructor; simpl...
    replace (X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) x ab)%aworklist with
      ((X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar Γ2 x ab) ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist; 
    constructor; simpl...
    + dependent destruction H...
      simpl.
      constructor; auto.
      eapply IHΓ2 with (X1:=X1) (X2:=X2) in H1 as Hws...
      dependent destruction Hws...
      * simpl in *. solve_notin_eq X2.
      * simpl in *. solve_notin_eq X2.
      * replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
        ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist in x by auto.
        apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
        dependent destruction Hws; auto; simpl in *.
        -- solve_notin_eq X1.
        -- solve_notin_eq X1.
        -- replace (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist 
            with  (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist in x by auto.
            apply worklist_split_etvar_det in x; auto.
            destruct x; subst...
            apply a_wf_wl_tvar_notin_remaining in H1; auto.
        -- simpl. apply a_wf_wl_tvar_notin_remaining in H1...
           solve_notin_dom.
    + solve_notin_dom.
    + solve_notin_dom.
  - dependent destruction H.
    + replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ □ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ □ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
      constructor; simpl; auto.
      replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ □ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X1 ~ᵃ ⬒ ;ᵃ (X ~ᵃ □ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist;
      constructor; simpl; auto.
      * constructor; auto.
        eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
        dependent destruction Hws; auto.
        -- simpl in *. solve_notin_eq X2.
        -- simpl in *. solve_notin_eq X2.
        -- replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
             ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist in x by auto.
           apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
           dependent destruction Hws; auto; simpl in *.
           ++ solve_notin_eq X1.
           ++ solve_notin_eq X1.
           ++ replace (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist 
                with (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist in x by auto.
              apply worklist_split_etvar_det in x; auto.
              destruct x; subst; auto.
              apply a_wf_wl_tvar_notin_remaining in H0; auto.
              ++ simpl. apply a_wf_wl_tvar_notin_remaining in H0; auto.
                 solve_notin_dom.
        -- solve_notin_dom.
      * solve_notin_dom.
      * solve_notin_dom.
    + replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ■ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ■ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
      constructor; simpl; auto.
      replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ■ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X1 ~ᵃ ⬒ ;ᵃ (X ~ᵃ ■ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist;
      constructor; simpl; auto.
      * constructor; auto.
        eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
        dependent destruction Hws; auto.
        -- simpl in *. solve_notin_eq X2.
        -- simpl in *. solve_notin_eq X2.
        -- replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
            ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist in x by auto.
          apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
          dependent destruction Hws; auto; simpl in *.
          ++ solve_notin_eq X1.
          ++ solve_notin_eq X1.
          ++ replace (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist 
                with (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist in x by auto.
              apply worklist_split_etvar_det in x; auto.
              destruct x; subst; auto.
              apply a_wf_wl_tvar_notin_remaining in H0; auto.
              ++ simpl. apply a_wf_wl_tvar_notin_remaining in H0; auto.
                 solve_notin_dom.
        -- solve_notin_dom.
      * solve_notin_dom.
      * solve_notin_dom.
    + replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒  ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
      constructor; simpl; auto.
      replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (X1 ~ᵃ ⬒ ;ᵃ (X ~ᵃ ⬒  ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist;
      constructor; simpl; auto.
      * constructor; auto.
        eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
        dependent destruction Hws; auto.
        -- simpl in *. solve_notin_eq X2.
        -- simpl in *. solve_notin_eq X2.
        -- replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
            ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist in x by auto.
          apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
          dependent destruction Hws; auto; simpl in *.
          ++ solve_notin_eq X1.
          ++ solve_notin_eq X1.
          ++ replace (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist 
                with (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist in x by auto.
              apply worklist_split_etvar_det in x; auto.
              destruct x; subst; auto.
              apply a_wf_wl_tvar_notin_remaining in H0; auto.
              ++ simpl. apply a_wf_wl_tvar_notin_remaining in H0; auto.
                 solve_notin_dom.
        -- solve_notin_dom.
      * solve_notin_dom.
      * solve_notin_dom.
 - dependent destruction H. 
   replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ w ⫤ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
    (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ w ⫤ Γ2) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
   constructor; simpl; auto.
   replace (X1 ~ᵃ ⬒ ;ᵃ w ⫤ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
    (X1 ~ᵃ ⬒ ;ᵃ (w ⫤ Γ2) ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist;
   constructor; simpl; auto.
   + constructor; auto.
     eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
     dependent destruction Hws; auto.
     * simpl in *. solve_notin_eq X2.
     * simpl in *. solve_notin_eq X2.
     * replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
         ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist in x by auto.
       apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
       dependent destruction Hws; auto; simpl in *.
       -- solve_notin_eq X1.
       -- solve_notin_eq X1.
       -- replace (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
           (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1))%aworklist in x; auto.
          apply worklist_split_etvar_det in x; auto.
          destruct x; subst; auto.
          apply a_wf_wl_tvar_notin_remaining in H0; auto.
       -- apply a_wf_wl_tvar_notin_remaining in H0; auto. solve_notin_dom.
   + solve_notin_dom.
   + solve_notin_dom.
Qed.




Lemma worklist_subst_fresh_etvar_total' : forall Γ X X1 X2,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X1 `notin` dom (awl_to_aenv Γ) ->
  X2 `notin` add X1 (dom (awl_to_aenv Γ)) ->
  exists Γ1 Γ2, aworklist_subst (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
      (typ_arrow ` X1 ` X2) Γ1 Γ2.
Proof.
  intros. apply aworklist_binds_split in H0.
  destruct H0 as [Γ1 [Γ2 Heq]].
  rewrite <- Heq in *.
  eapply worklist_subst_fresh_etvar_total in H; eauto.
  auto.
Qed.


Ltac rewrite_close_open_subst :=
  match goal with
  | H : _ |- context [open_typ_wrt_typ (close_typ_wrt_typ ?X ?A) ?B] =>
      erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X A)) by apply close_typ_wrt_typ_notin;
      rewrite open_typ_wrt_typ_close_typ_wrt_typ
  | H : _ |- context [open_exp_wrt_typ (close_exp_wrt_typ ?X ?e) ?B] =>
      erewrite (subst_tvar_in_exp_intro X (close_exp_wrt_typ X e)) by apply close_exp_wrt_typ_notin;
      rewrite open_exp_wrt_typ_close_exp_wrt_typ
  | H : _ |- context [open_exp_wrt_exp (close_exp_wrt_exp ?x ?e) ?e'] =>
      erewrite (subst_var_in_exp_intro x (close_exp_wrt_exp x e)) by apply close_exp_wrt_exp_notin;
      rewrite open_exp_wrt_exp_close_exp_wrt_exp
  | H : _ |- _ => idtac
  end.

Ltac simpl_open_subst_typ' :=
  match goal with
  | H : context [ {?B /ᵗ ?X} (?A ^ᵗ (?X')) ] |- _ =>
    rewrite subst_tvar_in_typ_open_typ_wrt_typ in H; auto with Hdb_a_wl_red_soundness;
    simpl in H; try destruct_eq_atom; auto
    (* try solve [rewrite subst_tvar_in_typ_fresh_eq in H; auto] *)
  | H1 : context [ {?B /ᵗ ?X} ?A ], H2 : context [ftvar_in_typ ?A] |- _ =>
      let H := fresh "H" in
      try (
        assert (H : X `notin` ftvar_in_typ A) by auto;
        rewrite subst_tvar_in_typ_fresh_eq in H1; auto; clear H)
end.

Ltac  simpl_open_subst_typ :=
  repeat simpl_open_subst_typ'.

Ltac solve_trans_typ_open_close' :=
  match goal with
  | H : ?θ ⫦ᵗ ?A1ᵃ ⇝ ?Aᵈ |- ?θ' ⫦ᵗ ?A2ᵃ ⇝ ({(` ?X1') /ᵗ ?X} ?Aᵈ) => 
      apply trans_typ_rename_tvar_cons with (X':=X1') in H; eauto with Hdb_a_wl_red_soundness
  end.


Ltac solve_trans_typ_open_close :=
  rewrite_close_open_subst;
  solve_trans_typ_open_close';
  simpl_open_subst_typ.

Lemma trans_typ_binds_etvar : forall θ X T,
  wf_ss θ ->
  binds X (dbind_typ T) θ ->
  θ ⫦ᵗ ` X ⇝ T.
Proof.
  intros.
  constructor; auto.
Qed.

Lemma trans_apply_cont : forall θ c cᵈ A Aᵈ w wᵈ,
  θ ⫦ᶜ c ⇝ cᵈ ->
  θ ⫦ᵗ A ⇝ Aᵈ ->
  θ ⫦ʷ w ⇝ wᵈ ->
  apply_cont c A w ->
  apply_cont cᵈ Aᵈ wᵈ.
Proof.
  intros. induction H2.
  - dependent destruction H.
Admitted.


Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃʷ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto with Hdb_a_wl_red_soundness.
  intros * Hwfa Hared. dependent induction Hared; auto; unfold transfer in *;
    try _apply_IH_a_wl_red; try destruct_trans; try trans_all_typ; try rename_typ.
  - exists dworklist_empty. intuition...
  - exists (dworklist_consvar Ω x (dbind_typ Aᵈ))...
  - exists (dworklist_constvar Ω X dbind_tvar_empty)...
    split... exists ((X, dbind_tvar_empty) :: θ)...
    constructor... admit.
  - exists (dworklist_constvar Ω X dbind_stvar_empty)...
    split... exists ((X, dbind_stvar_empty) :: θ)...
    constructor... admit.
  - exists Ω.
    split... exists ((X, dbind_typ typ_unit) :: θ)...
    constructor... admit.
  - exists (dworklist_conswork Ω (work_sub B1ᵈ typ_top)); split...
    exists θ... econstructor... econstructor...
    admit. (* OK, wf *)
  - exists (dworklist_conswork Ω (work_sub typ_bot Aᵈ)); split...
    exists θ... econstructor... econstructor...
    admit. (* OK, wf *)
  - exists (dworklist_conswork Ω (work_sub typ_unit typ_unit)).
    split... exists θ... 
    econstructor...   econstructor...
  - clear H0. dependent destruction H.
    + exists (dworklist_conswork Ω (work_sub ` X ` X)). split.
      * exists θ... 
        eapply trans_wl_in_ss_tvar in H; eauto...
        constructor... constructor...
      * eapply trans_wl_in_dwl_tvar in H...
    + exists (dworklist_conswork Ω (work_sub ` X ` X)). split.
      * exists θ... 
        eapply trans_wl_in_ss_stvar in H...
        constructor... constructor...
      * eapply trans_wl_in_dwl_stvar in H... 
    + assert (Hbinds: exists Tᵈ, binds X (dbind_typ Tᵈ) θ) by admit.
      destruct Hbinds as [Tᵈ Hbinds].
      exists (dworklist_conswork Ω (work_sub Tᵈ Tᵈ)). split.
      * exists θ. constructor... constructor...
      * constructor. apply dsub_refl.
        -- admit. (* OK, wf *)
        -- admit. (* OK, wf *)
        -- auto.
  - exists ((work_sub (typ_arrow B1ᵈ B2ᵈ) (typ_arrow A1ᵈ A2ᵈ) ⫤ Ω)%dworklist).
    split. exists θ. auto...
    econstructor.
    econstructor.
    + apply d_wl_red_weaken_work1 in Hdred. dependent destruction Hdred...
    + apply d_wl_red_weaken_work2 in Hdred. dependent destruction Hdred...
    + dependent destruction Hdred. dependent destruction Hdred...
  (* forall x. A < B  *)
  - inst_cofinites_by (L `union` ftvar_in_typ A1 `union` ftvar_in_typ B1) using_name X.
    assert ( ⊢ᵃʷ (work_sub (B1 ^ᵗ X) A1 ⫤ aworklist_constvar Γ X abind_etvar_empty)) by admit.
    destruct_a_wf_wl.
    _apply_IH_a_wl_red.
    destruct_trans.
    rename A1ᵈ into B1tᵈ. rename B1ᵈ into A1ᵈ.
    apply trans_typ_etvar_tvar_subst_cons in H13...
    destruct H13 as [B1xᵈ [Hsubst Htransa]].
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) A1ᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all. intros.
        solve_trans_typ_open_close.
      * admit. (* trans_typ_strengthen *)
    + econstructor. 
      eapply d_sub__alll with (T:=T) (L:=L)...
      * admit. (* OK, trans neq_all *)
      * admit. (* OK, trans neq_intersection *)
      * admit. (* OK, trans neq_union *)
      * intros. inst_cofinites_with X0.
        rewrite_close_open_subst.
        admit. (* OK, s_in *)
      * admit. (* OK, mono *)
      * rewrite_close_open_subst.
        rewrite Hsubst.
        dependent destruction Hdred...
      * dependent destruction Hdred...
  - destruct_a_wf_wl.
    dependent destruction H. dependent destruction H1.
    inst_cofinites_by (L `union` L0 `union` L1 `union` dom (awl_to_aenv Γ)) using_name X.
    assert ( ⊢ᵃʷ (work_sub (B1 ^ᵗ X) (A1 ^ᵗ X) ⫤ aworklist_constvar Γ X abind_stvar_empty) ) by admit.
    _apply_IH_a_wl_red.
    destruct_trans...
    rename A1ᵈ into B1xᵈ. rename B1ᵈ into A1xᵈ.
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) (typ_all (close_typ_wrt_typ X A1xᵈ)) ⫤ Ω)%dworklist.
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all. intros.
        rewrite_close_open_subst.
        admit. (* OK, trans_typ_rename *)
      * inst_cofinites_for trans_typ__all. intros.
        rewrite_close_open_subst.
        admit. (* OK, trans_typ_rename *)
    + dependent destruction Hdred. 
      econstructor...
      inst_cofinites_for d_sub__all; intros.
      * rewrite_close_open_subst.
        admit. (* OK, s_in *)
      * rewrite_close_open_subst.
        admit. (* OK, s_in *)
      * repeat rewrite_close_open_subst.
        admit. (* OK, sub_rename *)
      * dependent destruction Hdred...
  (* ^X < A1 -> A2 *)
  - inst_cofinites_by (L `union` singleton X `union`  dom (awl_to_aenv Γ)) using_name X1.
    inst_cofinites_by (L `union` singleton X1 `union` singleton X `union` dom (awl_to_aenv Γ)) using_name X2.
    assert (Hws: exists Γ1 Γ2, 
      aworklist_subst (work_sub ` X (typ_arrow A1 A2) ⫤ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
        (typ_arrow ` X1 ` X2) Γ1 Γ2). {
    eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
    destruct H as [Γ1 [Γ2 Hws]].
    exists Γ1, (work_sub `X (typ_arrow A1 A2) ⫤ Γ2)%aworklist.
    econstructor. auto.
    destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H3 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: binds X1 (dbind_typ T0)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      assert (Hbindsx2: binds X2 (dbind_typ T)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      apply trans_typ_binds_etvar in Hbindsx1...
      apply trans_typ_binds_etvar in Hbindsx2...
      apply trans_typ_binds_etvar in Hbindsx as Htransx3...
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_sub (typ_arrow T0 T) (typ_arrow A1ᵈ0 A2ᵈ))). split.
      * exists θ'. econstructor...
        constructor. 
        -- apply trans_typ_binds_etvar; eauto.
           ++ admit. (* OK, wf_ss *) 
           ++ inversion Hbindsx. dependent destruction H9. solve_notin_eq X1. 
           inversion H9. dependent destruction H10. solve_notin_eq X2.
           auto.
        -- constructor. rewrite_env (nil ++ θ'). 
           eapply trans_typ_strengthen_etvar with (X:=X1) (T:=T0).
           eapply trans_typ_strengthen_etvar with (X:=X2) (T:=T). auto...
           admit. (* OK, notin *)
           admit. (* OK, notin *)
           admit. (* OK, binds X *)
      * auto.
      * admit. (* OK, wf *)
      * admit. (* OK, mono *)
    + admit. (* OK, wf *)
  (* A1 -> A2 < ^X  *)
  - inst_cofinites_by (L `union` singleton X `union`  dom (awl_to_aenv Γ) `union` ftvar_in_typ A1) using_name X1.
    inst_cofinites_by (L `union` singleton X1 `union` singleton X `union` dom (awl_to_aenv Γ) `union` ftvar_in_typ A1) 
      using_name X2.
    assert (Hws: exists Γ1 Γ2, 
      aworklist_subst (work_sub (typ_arrow A1 A2) ` X ⫤ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
        (typ_arrow ` X1 ` X2) Γ1 Γ2). {
      eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
      destruct H as [Γ1 [Γ2 Hws]].
      exists Γ1, (work_sub (typ_arrow A1 A2) `X ⫤ Γ2)%aworklist.
      econstructor. auto.
      destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H3 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: binds X1 (dbind_typ T0)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      assert (Hbindsx2: binds X2 (dbind_typ T)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      apply trans_typ_binds_etvar in Hbindsx1...
      apply trans_typ_binds_etvar in Hbindsx2...
      apply trans_typ_binds_etvar in Hbindsx as Htransx3...
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_sub(typ_arrow A1ᵈ A2ᵈ) (typ_arrow T0 T) )). split.
      * exists θ'. econstructor...
        constructor.
        -- constructor. 
           ++ rewrite_env (nil ++ θ'). 
              apply trans_typ_strengthen_etvar with (X:=X1) (T:=T0)...
              eapply trans_typ_strengthen_etvar with (X:=X2) (T:=T)...
           ++ admit. (* OK, trans_typ_strengthen_etvar *)
        -- apply trans_typ_binds_etvar; eauto.
           ++ admit. (* OK, wf_ss *) 
           ++ inversion Hbindsx. dependent destruction H8. solve_notin_eq X1. 
           inversion H8. dependent destruction H10. solve_notin_eq X2.
           auto.
      * auto.
      * admit. (* OK, wf *)
      * admit. (* OK, mono *)
    + admit. (* OK, wf *)
    (* τ < ^X *)
  - assert (⊢ᵃʷ awl_app (subst_tvar_in_aworklist A X Γ2) Γ1) by admit.
    _apply_IH_a_wl_red. 
    eapply a_worklist_subst_transfer_same_dworklist in H4 as Hws; eauto.
    destruct Hws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ Ω)%dworklist. split.
    + exists θ'1.
      constructor...
    + econstructor...
      apply dsub_refl...
      admit. (* OK, wf *)
  (* ^X < τ *)
  - assert (⊢ᵃʷ awl_app (subst_tvar_in_aworklist B X Γ2) Γ1) by admit.
    _apply_IH_a_wl_red. 
    eapply a_worklist_subst_transfer_same_dworklist in H4 as Hws; eauto.
    destruct Hws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ Ω)%dworklist. split.
    + exists θ'1.
      constructor...
    + econstructor...
      apply dsub_refl...
      admit.
  (* A < B1 /\ B2 *)
  - exists (work_sub A1ᵈ (typ_intersection B1ᵈ B2ᵈ) ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
  (* A1 /\ A2 < B *)
  - exists (work_sub (typ_intersection B1ᵈ B2ᵈ) A1ᵈ ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
    econstructor... econstructor...
    eapply tran_wl_wf_trans_typ with (Aᵃ:=B2)...
  (* A1 /\ A2 < B *)
  - exists (work_sub (typ_intersection B1ᵈ B2ᵈ) A1ᵈ ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
    econstructor... eapply d_sub__intersection3...
    eapply tran_wl_wf_trans_typ with (Aᵃ:=B1)...
  (* A < B1 \/ B2 *)
  - exists (work_sub B1ᵈ (typ_union A1ᵈ A2ᵈ) ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
    econstructor... eapply d_sub__union1...
    eapply tran_wl_wf_trans_typ with (Aᵃ:=A2)...
  (* A < B1 \/ B2 *)
  - exists (work_sub B1ᵈ (typ_union A1ᵈ A2ᵈ) ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
    econstructor... eapply d_sub__union2...
    eapply tran_wl_wf_trans_typ with (Aᵃ:=A1)...
  (* A1 \/ A2 < B *)
  - exists (work_sub (typ_union B1ᵈ B2ᵈ) A1ᵈ ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
  (* e <= A *)
  - exists (work_check eᵈ A1ᵈ ⫤ Ω)%dworklist. split...
    destruct_d_wl_del_red...
  (* \ x. e <= A1 -> A2 *)
  - destruct_a_wf_wl. inst_cofinites_by (L `union` L0)... 
    assert (⊢ᵃʷ (work_check (open_exp_wrt_exp e (exp_var_f x)) A2 ⫤ (aworklist_consvar Γ x (abind_var_typ A1)))) by admit.
    apply H2 in H3.
    destruct H3 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans. rename_typ.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) (typ_arrow A1ᵈ A2ᵈ) ⫤ Ω)%dworklist. split.
    + exists θ.
      econstructor...
      econstructor...
      eapply trans_exp__abs with (L:=fvar_in_exp e). intros.
      rewrite_close_open_subst.
      admit. (* OK, inf rename *)
    + destruct_d_wl_del_red.
      econstructor; auto.
      inst_cofinites_for d_typing__chk_abs; auto.
      * admit. (* OK, wf *)
      * intros. rewrite_close_open_subst.
        admit. (* OK, chk rename *)
  (* \ x. e <= ^X *)
  - inst_cofinites_by L.
    inst_cofinites_by (L `union` singleton x `union` singleton X `union`  dom (awl_to_aenv Γ)) using_name X1.
    inst_cofinites_by (L `union` singleton x `union` singleton X1 `union` singleton X `union` dom (awl_to_aenv Γ)) using_name X2.
    assert (Hws: exists Γ1 Γ2, aworklist_subst 
       (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
       (typ_arrow ` X1 ` X2) Γ1 Γ2). {
       eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
       destruct H as [Γ1 [Γ2 Hws]].
       exists Γ1, (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ x ~ᵃ ` X1 ;ᵃ Γ2)%aworklist.
       econstructor. econstructor; auto.
       auto.
       destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H1 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: binds X1 (dbind_typ T0)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      assert (Hbindsx2: binds X2 (dbind_typ T)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      apply trans_typ_binds_etvar in Hbindsx1...
      apply trans_typ_binds_etvar in Hbindsx2...
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) (typ_arrow T0 T))). split.
      * exists θ'. constructor; auto.
        constructor.
        -- inst_cofinites_for trans_exp__abs. intros.
           rewrite_close_open_subst.
           admit. (* Ok, trans rename *)
        -- apply trans_typ_binds_etvar; auto...
           inversion Hbindsx. dependent destruction H9. solve_notin_eq X1.
           inversion H9. dependent destruction H10. solve_notin_eq X2.
           auto.
      * constructor; auto.
         admit. 
         destruct_d_wl_del_red...
      * admit. (* OK, wf *)
      * admit. (* mono *)   
    + admit. (* OK, wf *)
  (* \ x. e <= ⊤ *)
  - destruct_a_wf_wl. inst_cofinites_by (L `union` L0).
    assert ( ⊢ᵃʷ (work_check (e ^ᵉₑ exp_var_f x) typ_top ⫤ x ~ᵃ typ_bot;ᵃ Γ)) by admit.
    apply H3 in H4. 
    destruct H4 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) typ_top ⫤ Ω)%dworklist. split.
    + exists θ. 
      econstructor...
      econstructor...
      inst_cofinites_for trans_exp__abs. intros.
      rewrite_close_open_subst.
      admit. (* OK, inf rename *)
    + destruct_d_wl_del_red...
      econstructor; auto.
      inst_cofinites_for d_typing__chk_abstop. intros.
      rewrite_close_open_subst.
      admit. (* OK, chk rename h*)
  (* e <= A1 /\ A2 *)
  - exists (work_check eᵈ (typ_intersection A1ᵈ A2ᵈ) ⫤ Ω)%dworklist...
    split...
    destruct_d_wl_del_red...
  (* e <= A1 \/ A2 *)
  - exists (work_check eᵈ (typ_union A1ᵈ A2ᵈ) ⫤ Ω)%dworklist...
    split...
    destruct_d_wl_del_red...
    econstructor... eapply d_typing__chk_union1...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A2)...
  (* e <= A1 \/ A2 *)
  - exists (work_check eᵈ (typ_union A1ᵈ A2ᵈ) ⫤ Ω)%dworklist...
    split...
    destruct_d_wl_del_red...
    econstructor... eapply d_typing__chk_union2...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A1)...
  (* x => _ *)
  - destruct_a_wf_wl.
    apply binds_unique with (a:=abind_var_typ A0) in H; auto.
    dependent destruction H; subst.
    assert (⊢ᵃʷ (work_apply c A ⫤ Γ)). econstructor... econstructor...
    admit. (* OK, wf *)
    apply IHHared in H as IH. destruct IH as [Ω [[θ Htrans] Hdred]].
    destruct_trans. rename_typ.
    exists (work_infer (exp_var_f x) cᵈ ⫤ Ω)%dworklist.
    split... exists θ. econstructor... econstructor...
    admit. (* OK, binds *)
    admit. (* OK, uniq *) 
  (* e : A => _ *)
  - exists (work_infer (exp_anno eᵈ Aᵈ) cᵈ ⫤ Ω)%dworklist...
    split. exists θ...
    destruct_d_wl_del_red.
    econstructor...
    eapply d_typing__inf_anno...
    eapply d_chk_inf_wft...
  (* /\ a. e : A => _ *)
  - destruct_a_wf_wl. 
    pick fresh X. inst_cofinites_with X.
    assert (Hwf: ⊢ᵃʷ (work_check (e ^ᵉₜ ` X) (A ^ᵗ X) ⫤ X ~ᵃ □ ;ᵃ work_apply c (typ_all A) ⫤ Γ)) by admit.
    apply H2 in Hwf as IHHared.
    destruct IHHared as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans.
    dependent destruction H5.
    (*  *)
    exists (work_infer (exp_tabs (body_anno (close_exp_wrt_typ X eᵈ) (close_typ_wrt_typ X A1ᵈ0))) cᵈ ⫤ Ω)%dworklist. split.
    + exists θ...
      econstructor...
      econstructor...
      inst_cofinites_for trans_exp__tabs.
      intros. simpl. unfold open_body_wrt_typ. simpl.
      constructor.
      -- replace (open_exp_wrt_typ_rec 0 ` X0 e) with (open_exp_wrt_typ e ` X0) by auto.  
         replace (open_exp_wrt_typ_rec 0 ` X0 (close_exp_wrt_typ X eᵈ)) 
          with (open_exp_wrt_typ  (close_exp_wrt_typ X eᵈ) `X0) by auto.
          rewrite_close_open_subst.
          apply trans_exp_rename_tvar_cons with (X':=X0) in H7; eauto.          
          admit. (* OK, inf rename *)
      -- replace (open_typ_wrt_typ_rec 0 ` X0 A) with (open_typ_wrt_typ A ` X0) by auto.  
         replace (open_typ_wrt_typ_rec 0 ` X0 (close_typ_wrt_typ X A1ᵈ0)) 
          with (open_typ_wrt_typ (close_typ_wrt_typ X A1ᵈ0) ` X0 ) by auto.
          solve_trans_typ_open_close.
    + assert (θ ⫦ᵗ typ_all A ⇝ typ_all A1ᵈ). {
        inst_cofinites_for trans_typ__all. intros.
        inst_cofinites_with X0. auto.
      }
      assert (θ ⫦ᵗ typ_all A ⇝ typ_all (close_typ_wrt_typ X A1ᵈ0)). {
        inst_cofinites_for trans_typ__all. intros.
        solve_trans_typ_open_close.
      }
      apply trans_typ_det with (A₁ᵈ:=typ_all (close_typ_wrt_typ X A1ᵈ0)) in H9...
      apply d_wl_del_red__inf with (T1:=typ_all (close_typ_wrt_typ X A1ᵈ0)).
      * eapply d_typing__inf_tabs. 
        admit. (* OK, wf *)
        intros. rewrite_close_open_subst.
        eapply d_typing__chk_sub with (B:={` X0 /ᵗ X} A1ᵈ0)...
        econstructor; eauto.
        admit. (* OK, wf rename *)
        rewrite_close_open_subst. admit. (* OK, chk rename *)
        admit. (* OK, sub rename *)
      * rewrite H9. auto. destruct_d_wl_del_red...
  (* \x. e => _ *)
  - destruct_a_wf_wl.
    pick fresh x. pick fresh X1. pick fresh X2.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    assert (Hwf: ⊢ᵃʷ (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ x ~ᵃ ` X1;ᵃ work_apply c (typ_arrow ` X1 ` X2)
            ⫤ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by admit.
    apply H3 in Hwf.
    destruct Hwf as [Ω [[θ Htrans] Hdred]].
    destruct_trans. unify_trans_typ.
    exists (work_infer (exp_abs (close_exp_wrt_exp x eᵈ)) cᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ'...
      econstructor...
      econstructor...
      * admit. (* trans_typ *)
      * admit. (* trans_cont_weaken *)
    + eapply d_wl_del_red__inf with (T1:=typ_arrow A1ᵈ A1ᵈ1). 
      * assert (Hbindsx1: binds X1 (dbind_typ T1)  ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ')) by auto.
        assert (Hbindsx2: binds X2 (dbind_typ T0)  ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ')) by auto.
        apply trans_typ_binds_etvar in Hbindsx1.
        apply trans_typ_binds_etvar in Hbindsx2.
        repeat unify_trans_typ.
        destruct_d_wl_del_red... simpl in H7.
        inst_cofinites_for d_typing__inf_abs_mono; auto.
        admit. (* OK, mono *)
        intros. rewrite_close_open_subst; auto. admit. (* OK, chk rename *)
        admit. (* OK, wf_ss *)
        admit. (* OK, wf_ss *)
      * destruct_d_wl_del_red...
  (* () => _ *)
  - exists (work_infer exp_unit cᵈ ⫤ Ω)%dworklist...
    split. exists θ... 
    econstructor...
  (* e1 e2 => _ *)
  - exists (work_infer (exp_app eᵈ eᵈ0) cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
    eapply d_wl_del_red__inf with (T1:=T3)...
    econstructor...
      apply d_wl_red_weaken_work1 in Hdred. dependent destruction Hdred...
    apply d_wl_red_weaken_work2 in Hdred...
  - exists (work_infapp  (typ_arrow A1ᵈ A2ᵈ) eᵈ cᵈ ⫤ Ω)%dworklist...
    split. destruct_d_wl_del_red. exists θ...
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
  - destruct_a_wf_wl. 
    dependent destruction H.
    inst_cofinites_by (L `union` L0 `union` ftvar_in_typ A) using_name X.
    assert (⊢ᵃʷ (work_infabs (A ^ᵗ X) c ⫤ X ~ᵃ ⬒ ;ᵃ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    eapply trans_typ_etvar_tvar_subst_cons in H11...
    destruct H11 as [Axᵈ [Hsubst Htransa]].
    exists (work_infabs (typ_all (close_typ_wrt_typ X Axᵈ)) cᵈ ⫤ Ω)%dworklist. split.
    exists θ'.
    + constructor...
      constructor...
      * inst_cofinites_for trans_typ__all.
        intros.
        solve_trans_typ_open_close.
      * admit. (* OK, trans_cont_strengthen *)
    + dependent destruction Hdred.  
      eapply d_wl_del_red__infabs with (T2:=T2) (T3:=T3); auto.
      eapply d_infabs__all with (T:=T)...
      * admit. (* OK, mono *)
      * admit. (* OK, wf *)
      * admit. (* OK, wf *)
      * rewrite_close_open_subst. rewrite Hsubst...
  - exists (work_infabs (typ_intersection A1ᵈ A2ᵈ) cᵈ ⫤ Ω)%dworklist...
    split...
    destruct_d_wl_del_red.
    econstructor...
    econstructor...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A2)...
  - exists (work_infabs (typ_intersection A1ᵈ A2ᵈ) cᵈ ⫤ Ω)%dworklist...
    split...
    destruct_d_wl_del_red.
    econstructor...
    eapply d_infabs__intersection2...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A1)...
  - exists (work_infabs (typ_union A1ᵈ A2ᵈ) cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  - exists (work_infabsunion (typ_arrow B1ᵈ C1ᵈ) A2ᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  - exists (work_unioninfabs (typ_arrow B1ᵈ C1ᵈ) (typ_arrow B2ᵈ C2ᵈ) cᵈ ⫤ Ω)%dworklist.
    split...
    exists θ...
  (* ^X ▹ _ *)
  - inst_cofinites_by (L `union` singleton X `union`  dom (awl_to_aenv Γ)) using_name X1.
    inst_cofinites_by (L `union` singleton X1 `union` singleton X `union` dom (awl_to_aenv Γ)) using_name X2.
    assert (Hws: exists Γ1 Γ2, aworklist_subst 
      (work_infabs (typ_arrow ` X1 ` X2) c ⫤ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
      (typ_arrow ` X1 ` X2) Γ1 Γ2). {
      eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
      destruct H as [Γ1 [Γ2 Hws]].
      exists Γ1, (work_infabs (typ_arrow ` X1 ` X2) c ⫤ Γ2)%aworklist.
      econstructor. 
      auto.
      destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H1 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: binds X1 (dbind_typ T0)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      assert (Hbindsx2: binds X2 (dbind_typ T)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      apply trans_typ_binds_etvar in Hbindsx1...
      apply trans_typ_binds_etvar in Hbindsx2...
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_infabs (typ_arrow T0 T) cᵈ)). split.
      * exists θ'. constructor; auto.
        constructor.
        -- apply trans_typ_binds_etvar; auto...
           inversion Hbindsx. dependent destruction H6. solve_notin_eq X1.
           inversion H6. dependent destruction H8. solve_notin_eq X2.
           auto.
        -- admit. (* trans_cont_stengthen *)
      * destruct_d_wl_del_red...       
      * admit. (* OK, wf *)
      * admit. (* mono *)   
    + admit. (* OK, wf *)
  - exists (work_infer (exp_tapp eᵈ Bᵈ) cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  (* ∀ a. A ∘ B =>=> _ *)
  - assert (⊢ᵃʷ (work_apply c (A ^^ᵗ B) ⫤ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    inst_cofinites_by (dom (awl_to_aenv Γ) `union` dom θ `union` ftvar_in_typ A) using_name X.
    trans_all_typ.
    replace (A ^^ᵗ B) with ({B /ᵗ X} A ^ᵗ X) in H7 by admit.
    eapply trans_typ_rev_subst_cons in H7...
    destruct H7 as [Axᵈ [Hsubst Htransa]].
    exists (work_inftapp (typ_all (close_typ_wrt_typ X Axᵈ)) Bᵈ cᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ.
      econstructor...
      econstructor...
      inst_cofinites_for trans_typ__all. intros.
      solve_trans_typ_open_close.
    + eapply d_wl_del_red__inftapp with (T3:=open_typ_wrt_typ (close_typ_wrt_typ X Axᵈ) Bᵈ)...
      econstructor; auto.
      * admit. (* OK, wf *)
      * admit. (* OK, wf *)
      * admit. (* OK, wf *)
      * rewrite_close_open_subst. rewrite Hsubst...
    + admit. (* OK, lc *)
  - exists (work_inftapp typ_bot Bᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    econstructor... econstructor...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=B)...
  - exists (work_inftapp (typ_intersection A1ᵈ A2ᵈ) Bᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
    econstructor... eapply d_inftapp__intersection1...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A2)...
  - exists (work_inftapp (typ_intersection A1ᵈ A2ᵈ) Bᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
    econstructor... eapply d_inftapp__intersection2...
    eapply tran_wl_wf_trans_typ with (Γ:=Γ) (Aᵃ:=A1)...
  - exists (work_inftapp (typ_union A1ᵈ A2ᵈ) Bᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  - exists (work_inftappunion C1ᵈ A2ᵈ Bᵈ cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  - exists (work_unioninftapp C1ᵈ C2ᵈ cᵈ ⫤ Ω)%dworklist.
    split...
  - destruct_a_wf_wl.
    eapply a_wf_work_applied in H1 as Hwf...
    assert ( ⊢ᵃʷ (w ⫤ Γ) ) by auto.
    apply IHHared in H2...
    destruct H2 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    trans_all_typ.
    assert (exists cᵈ, θ' ⫦ᶜ c ⇝ cᵈ) by admit. (* OK, trans cont total *)
    destruct H4 as [cᵈ Htransc].
    exists (work_apply cᵈ T1ᵈ ⫤ Ω)%dworklist. split.
    exists θ'. econstructor...
    eapply trans_apply_cont in H2; eauto.
    econstructor; eauto.
  all: fail.
Admitted.
