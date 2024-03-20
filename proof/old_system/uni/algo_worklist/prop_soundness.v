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
  exists θ'1 θ'2 Tᵈ, 
      trans_worklist nil Γ Ω (θ'2 ++ (X ~ dbind_typ Tᵈ) ++ θ'1 ) /\ 
      θ ⫦ᵗ T ⇝ Tᵈ /\ 
      θ'1 ⫦ᵗ T ⇝ Tᵈ /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b  (θ'2 ++ (X ~ dbind_typ Tᵈ) ++ θ'1 )) /\ 
      wf_ss (θ'2 ++ (X ~ dbind_typ Tᵈ) ++ θ'1 ).
Proof with auto with Hdb_a_wl_red_soundness.
  intros. generalize dependent θ. generalize dependent Ω. dependent induction H2; intros.
  - simpl in *.
    assert (exists Aᵈ, θ ⫦ᵗ A ⇝ Aᵈ) by admit.
    destruct H2 as [Aᵈ].
    exists θ. 
    exists nil.
    exists Aᵈ.
    repeat split; auto.
    + econstructor; auto.  
      * admit. (* OK, mono *)
    + intros. inversion H5. dependent destruction H6...
      contradiction.
      auto.
    + admit. (* OK, wf_ss *)
  - dependent destruction H3.
    apply IHaworklist_subst in H3 as IH.
    destruct IH as [θ'1 [θ'2 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds Hwfss]]]]]]].    
    exists θ'1. exists θ'2. exists Tᵈ. repeat split; auto.
    + econstructor. auto. 
      apply trans_typ_reorder with (θ':=(θ'2 ++ (X ~ dbind_typ Tᵈ) ++ θ'1 )) in H4; auto.
      * apply trans_typ_strengthen_etvar in H4; auto.
        eapply trans_typ_etvar_subst in H4; eauto.
        -- admit. (* OK, lc *)
        -- admit. (* OK, wf_ss *)
        -- admit. (* OK, notin *)
        -- admit. (* OK, mono *) 
        -- apply subst_tvar_in_typ_fresh_same...
      * admit. (* OK, wf_ss *)
      * intros. apply Hbinds... admit.
    + apply Hbinds; auto.
    + apply Hbinds; auto.
    + destruct_a_wf_wl; auto.
    + admit. (* OK, mono *)
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [θ'2 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds Hwfss]]]]]]].    
    exists θ'1. exists (Y ~ dbind_tvar_empty ++ θ'2). 
    exists Tᵈ. repeat split; auto.
    + econstructor; auto.
    + rewrite_env (nil ++ (Y ~ □) ++ θ'). apply trans_typ_weaken... 
      admit.
    + intros. inversion H7.
      * dependent destruction H8... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. inversion H7.
      * dependent destruction H8... 
      * simpl. apply binds_cons... apply Hbinds...
    + simpl. constructor; eauto. admit. (* OK, notin *)
    + destruct_a_wf_wl...
    + admit. (* OK, mono *)
    + auto.
  (* stvar_stay *)
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [θ'2 [Tᵈ [Htrans [Htranst [Htranst' [Hbindsx Hwfss]]]]]]].    
    exists θ'1. exists (Y ~ dbind_stvar_empty ++ θ'2). 
    exists Tᵈ. repeat split; auto.
    + econstructor; auto.
    + rewrite_env (nil ++ (Y ~ ■) ++ θ'). apply trans_typ_weaken... 
      admit. (* OK, wf_ss *)
    + intros. inversion H7.
      * dependent destruction H8... 
      * simpl. apply binds_cons... apply Hbindsx...
    + intros. inversion H7.
      * dependent destruction H8... 
      * simpl. apply binds_cons... apply Hbindsx...
    + simpl. constructor... admit. (* OK, notin *)
    + destruct_a_wf_wl...
    + admit. (* OK, mono *)
    + auto.
  (* work_stay *)
  - dependent destruction H3.
    apply IHaworklist_subst in H3 as IH.
    destruct IH as [θ'1 [θ'2 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds Hwfss]]]]]]].    
    exists θ'1. exists θ'2. exists Tᵈ. repeat split; auto.
    + constructor; auto.
      admit.
    + apply Hbinds...
    + apply Hbinds...
    + destruct_a_wf_wl...
    + simpl in H0...
    + auto.
  (* etvar_move *)
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [θ'2 [Tᵈ [Htrans [Htranst [Htranst' [Hbindsx Hwfss]]]]]]].    
    exists θ'1. 
    exists (Y ~ dbind_typ T ++ θ'2). exists Tᵈ. repeat split; auto.
    + econstructor; auto. admit.
    + admit.
    + intros. inversion H8.
      * dependent destruction H9... 
      * simpl. apply binds_cons... apply Hbindsx...
    + intros. admit.
    + admit.
    + destruct_a_wf_wl...
    + admit.
    + auto.
  - simpl in *.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [θ'2 [Tᵈ [Htrans [Htranst [Htranst' [Hbindsx Hwfss]]]]]]].    
    assert (exists T2ᵈ, exists θ'3, θ'1 = (Y ~ dbind_typ T2ᵈ) ++ θ'3) by admit.
    destruct H6 as [T2ᵈ [θ'3]].
    exists θ'3. exists ((Y, dbind_typ T2ᵈ) :: θ'2). exists Tᵈ. repeat split; auto.
    + simpl in *. rewrite_env (θ'2 ++ ((X, dbind_typ Tᵈ) :: θ'3)).
      econstructor. (* Ordinary, some inversion lemma about trans awl_app *)
      admit. admit.
    + admit. (* OK, wf *)
    + intros. simpl. apply binds_cons... 
      apply Hbindsx in H8. 
      admit. auto.
    + destruct (Y==Y0). 
      * intros. subst. inversion H8.
         dependent destruction H6. apply Hbindsx...
         admit.
      * admit.
    + admit.
    + admit.
    + admit.
    + auto.
Admitted.


(* Hint Resolve d_chk_inf_wft : Hdb_a_wl_red_soundness. *)

Hint Constructors trans_typ : Hdb_a_wl_red_soundness.
Hint Constructors trans_exp : Hdb_a_wl_red_soundness.
Hint Constructors trans_cont : Hdb_a_wl_red_soundness.
Hint Constructors trans_work : Hdb_a_wl_red_soundness.
Hint Constructors trans_worklist : Hdb_a_wl_red_soundness.
Hint Constructors aworklist_subst : Hdb_a_wl_red_soundness.


Hint Resolve trans_typ_lc_atyp : Hdb_a_wl_red_soundness.


Lemma worklist_subst_fresh_etvar_total : forall Γ1 Γ2 X X1 X2,
  ⊢ᵃʷ awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty) ->
  X1 `notin` dom (awl_to_aenv (awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty))) ->
  X2 `notin` add X1 (dom (awl_to_aenv (awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty)))) ->
  aworklist_subst (aworklist_constvar (aworklist_constvar (awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty)) X1 abind_etvar_empty) X2 abind_etvar_empty) 
    X (typ_arrow ` X1 `X2) (aworklist_constvar (aworklist_constvar Γ1 X2 abind_etvar_empty) X1 abind_etvar_empty) Γ2.
Proof.
  induction Γ2; intros; simpl in *; auto.
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (aworklist_constvar 
          (awl_app (aworklist_constvar aworklist_empty X1 abind_etvar_empty) (aworklist_constvar Γ1 X abind_etvar_empty))
          X2 abind_etvar_empty);
    constructor; simpl; auto.
    replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with 
      (aworklist_constvar 
          ((awl_app aworklist_empty (aworklist_constvar (aworklist_constvar Γ1 X2 abind_etvar_empty) X abind_etvar_empty)))
          X1 abind_etvar_empty);
    constructor; simpl; auto.
    constructor.
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) x ab)%aworklist with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar Γ2 x ab) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist;
    constructor; simpl; auto.
    replace (X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) x ab)%aworklist with
      ((X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar Γ2 x ab) ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1)%aworklist; 
    constructor; simpl; auto.
    + dependent destruction H; auto.
      simpl.
      constructor; auto.
      eapply IHΓ2 with (X1:=X1) (X2:=X2) in H1 as Hws; eauto.
      dependent destruction Hws; auto.
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
            destruct x; subst.
            auto. simpl.
            apply a_wf_wl_tvar_notin_remaining in H1; auto.
        -- simpl. apply a_wf_wl_tvar_notin_remaining in H1; auto.
           rewrite awl_to_aenv_app in H2. rewrite dom_aenv_app_comm in H2; simpl in *.
           auto.
    + rewrite awl_to_aenv_app in H0. rewrite dom_aenv_app_comm in H0; simpl in *.
      auto.
    + rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
      auto.
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
                rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
                auto.
        -- rewrite awl_to_aenv_app in H. rewrite dom_aenv_app_comm in H; simpl in *.
           auto.
      * rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
        auto.
      * rewrite awl_to_aenv_app in H2. rewrite dom_aenv_app_comm in H2; simpl in *.
        auto.
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
                rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
                auto.
        -- rewrite awl_to_aenv_app in H. rewrite dom_aenv_app_comm in H; simpl in *.
          auto.
      * rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
        auto.
      * rewrite awl_to_aenv_app in H2. rewrite dom_aenv_app_comm in H2; simpl in *.
        auto.
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
                rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
                auto.
        -- rewrite awl_to_aenv_app in H. rewrite dom_aenv_app_comm in H; simpl in *.
          auto.
      * rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
        auto.
      * rewrite awl_to_aenv_app in H2. rewrite dom_aenv_app_comm in H2; simpl in *.
        auto.
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
       -- rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
          apply a_wf_wl_tvar_notin_remaining in H0; auto.
   + rewrite awl_to_aenv_app in H1. rewrite dom_aenv_app_comm in H1; simpl in *.
     auto.
   + rewrite awl_to_aenv_app in H2. rewrite dom_aenv_app_comm in H2; simpl in *.
     auto.
Qed.

Ltac rewrite_close_open_subst :=
  match goal with
  | H : _ |- context [open_typ_wrt_typ (close_typ_wrt_typ ?X ?A) ?B] =>
      erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X A)) by apply close_typ_notin;
      rewrite open_typ_wrt_typ_close_typ_wrt_typ
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
  | H : ?θ ⫦ᵗ ?A1ᵃ ⇝ ?Aᵈ |- ?θ' ⫦ᵗ ?A2ᵃ ⇝ ({`?X' /ᵗ ?X} ?Aᵈ) => 
      eapply trans_typ_rename_tvar_cons in H; eauto with Hdb_a_wl_red_soundness
  end.


Ltac solve_trans_typ_open_close :=
  rewrite_close_open_subst;
  solve_trans_typ_open_close';
  simpl_open_subst_typ.

Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃʷ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto with Hdb_a_wl_red_soundness.
  intros * Hwfa Hared. dependent induction Hared; auto; unfold transfer in *;
    try _apply_IH_a_wl_red; try destruct_trans; try trans_all_typ; try rename_typ.
  - exists dworklist_empty. intuition...
  - exists (dworklist_consvar Ω x (dbind_typ Aᵈ))...
  - exists (dworklist_constvar Ω X dbind_tvar_empty)...
    split... exists ((X, dbind_tvar_empty) :: θ)...
  - exists (dworklist_constvar Ω X dbind_stvar_empty)...
    split... exists ((X, dbind_stvar_empty) :: θ)...
  - exists Ω.
    split... exists ((X, dbind_typ typ_unit) :: θ)...
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
    + admit.
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
    apply trans_typ_etvar_tvar_subst_cons in H12...
    destruct H12 as [B1xᵈ [Hsubst Htransa]].
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) A1ᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all. intros.
        solve_trans_typ_open_close.
      * admit. (* trans_typ_strengthen *)
    + econstructor. 
      eapply d_sub__alll with (T:=T) (L:=L)...
      * admit.
      * admit.
      * admit.
      * intros. inst_cofinites_with X0.
        rewrite_close_open_subst.
        admit. (* OK, s_in *)
      * admit.
      * rewrite_close_open_subst.
        rewrite Hsubst.
        dependent destruction Hdred...
      * dependent destruction Hdred...
    + admit.
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
        (* assert ((X0, ■) :: θ' ⫦ᵗ B1 ^ᵗ X0 ⇝ {` X0 /ᵗ X} B1xᵈ). *)
        (* solve_trans_typ_open_close. *)
        admit.
      * inst_cofinites_for trans_typ__all. intros.
        rewrite_close_open_subst.
        admit.
    + dependent destruction Hdred. 
      econstructor...
      inst_cofinites_for d_sub__all; intros.
      * rewrite_close_open_subst.
        admit.
      * rewrite_close_open_subst.
        admit.
      * repeat rewrite_close_open_subst.
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
  (* τ < ^X *)
  - assert (⊢ᵃʷ awl_app (subst_tvar_in_aworklist A X Γ2) (awl_app (etvar_list_to_awl E) Γ1)) by admit.
    _apply_IH_a_wl_red. 
    eapply a_worklist_subst_transfer_same_dworklist in Htrans; eauto.
    destruct Htrans as [θ'1 [θ'2 [Tᵈ [Htrans [Htransa [Htrans' [Hbinds [Hwfss]]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ Ω)%dworklist. split.
    + exists (θ'2 ++ X ~ dbind_typ Tᵈ ++ θ'1).
      constructor...
      constructor...
      eapply trans_typ_reorder in Htransa...
      * admit.
      * intros. apply Hbinds...
        admit.
    + econstructor...
      apply dsub_refl...
      admit.
  (* ^X < τ *)
  - assert ( ⊢ᵃʷ awl_app (subst_tvar_in_aworklist B X Γ2) (awl_app (etvar_list_to_awl E) Γ1)) by admit.
    _apply_IH_a_wl_red. 
    eapply a_worklist_subst_transfer_same_dworklist in Htrans as Hws; eauto.
    destruct Hws as [θ'1 [Htranswl [Hbinds Htransx]]].
    destruct Htransx as [Tᵈ [Htransa Htransx]].
    exists (work_sub Tᵈ Tᵈ ⫤ Ω)%dworklist. split.
    + exists θ'1.
      constructor...
      constructor...
      eapply trans_typ_reorder in Htransa...
      * admit.
    + admit.
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
      admit.
    + destruct_d_wl_del_red.
      dependent destruction Hdred...  
      econstructor; auto.
      econstructor.
      * admit. (* OK, wf *)
      * intros. admit. (* OK, rename *)
  (* \ x. e <= ^X *)
  - inst_cofinites_by L.
    inst_cofinites_by (L `union` singleton x `union` singleton X) using_name X1.
    inst_cofinites_by (L `union` singleton x `union` singleton X1 `union` singleton X) using_name X2.
    assert (exists Γ1 Γ2 E, aworklist_subst 
       (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
       (typ_arrow ` X1 ` X2) E Γ1 Γ2) by admit.
    destruct H2 as [Γ1 [Γ2 [E Hsubst]]].
    apply H1 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Htrans as Htransws; eauto...
      destruct Htransws as [θ'1 [Hdred1 [Hbinds Htransx]]].
      destruct Htransx as [Tᵈ [Htransa Htransx]].
      destruct_trans.
      exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) ( typ_arrow A1ᵈ1 A2ᵈ) ⫤ Ω)%dworklist.
      split.
      * exists θ'.
        econstructor...
        econstructor...
        admit.
        admit.
      * destruct_d_wl_del_red...
        econstructor.
        admit.
        admit.
      * admit.
    + admit.
  (* \ x. e <= ⊤ *)
  - destruct_a_wf_wl. inst_cofinites_by (L `union` L0).
    assert ( ⊢ᵃʷ (work_check (open_exp_wrt_exp e (exp_var_f x)) typ_top ⫤ (aworklist_consvar Γ x (abind_var_typ typ_bot)))) by admit.
    apply H3 in H4. 
    destruct H4 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) typ_top ⫤ Ω)%dworklist. split.
    + exists θ. 
      econstructor...
      econstructor...
      eapply trans_exp__abs with (L:=fvar_in_exp e). intros.
      admit.
    + destruct_d_wl_del_red.
      dependent destruction Hdred...  
      econstructor; auto.
      admit.
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
    assert (⊢ᵃʷ (work_apply c A0 ⫤ Γ)). econstructor... econstructor...
    admit.
    apply IHHared in H2. destruct H2 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans. rename_typ.
    exists (work_infer (exp_var_f x) cᵈ ⫤ Ω)%dworklist.
    split... exists θ. econstructor... econstructor...
    admit.
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
    exists (work_infer (exp_tabs (body_anno (close_exp_wrt_typ X eᵈ) A1ᵈ0)) cᵈ ⫤ Ω)%dworklist. split.
    + exists θ...
      econstructor...
      econstructor...
      inst_cofinites_for trans_exp__tabs.
      intros. simpl. unfold open_body_wrt_typ. simpl.
      constructor.
      -- admit.
      -- admit.
    + admit.
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
    + eapply d_wl_del_red__inf with (T1:=typ_arrow A1ᵈ0 A2ᵈ). 
      * assert ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ' ⫦ᵗ ` X1 ⇝ T1).
        { eapply trans_typ__etvar.
          - econstructor; eauto.
            econstructor; eauto.
            admit.
            admit.
            admit.
          - apply binds_cons. econstructor...
        }
        assert ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ' ⫦ᵗ ` X2 ⇝ T0).
        { eapply trans_typ__etvar.
          - econstructor; eauto.
            econstructor; eauto.
            admit.
            admit.
            admit.
          -  econstructor...
        }
        apply trans_typ_det with (A₁ᵈ:=A1ᵈ0) in H7; eauto; subst.
        apply trans_typ_det with (A₁ᵈ:=A2ᵈ) in H11; eauto; subst.
        destruct_d_wl_del_red... simpl in H7.
        econstructor; auto.
        admit. (* mono *)
        admit. (* rename *)
        admit. (* OK, uniq *)
        admit. (* OK, uniq *)
      * destruct_d_wl_del_red... dependent destruction Hdred. auto.
    + admit. (* OK, uniq *)
    + admit. (* OK, uniq *)
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
  - admit.
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
  - inst_cofinites_by L using_name X1.
    inst_cofinites_by (L `union` singleton X1) using_name X2.
    admit.
  - exists (work_infer (exp_tapp eᵈ Bᵈ) cᵈ ⫤ Ω)%dworklist.
    split...
    destruct_d_wl_del_red...
  (* ∀ a. A ∘ B =>=> _ *)
  - assert (⊢ᵃʷ (work_apply c (A ^^ᵗ B) ⫤ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    inst_cofinites_by (dom (awl_to_aenv Γ) `union` dom θ) using_name X.
    trans_all_typ.
    replace (A ^^ᵗ B) with ({B /ᵗ X} A ^ᵗ X) in H7 by admit.
    eapply trans_typ_rev_subst_cons in H7...
    destruct H7 as [Axᵈ [Hsubst Htransa]].
    exists (work_inftapp (typ_all (close_typ_wrt_typ X Axᵈ)) Bᵈ cᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ.
      econstructor...
      econstructor...
      admit.
    + eapply d_wl_del_red__inftapp with (T3:=open_typ_wrt_typ (close_typ_wrt_typ X Axᵈ) Bᵈ)...
      econstructor; auto.
      * admit. (* OK, wf *)
      * admit. (* OK, wf *)
      * admit. (* OK, wf *)
      * replace (close_typ_wrt_typ X Axᵈ ^^ᵗ Bᵈ) with ({Bᵈ /ᵗ X}(close_typ_wrt_typ X Axᵈ ^^ᵗ `X)) by admit.
        rewrite open_typ_wrt_typ_close_typ_wrt_typ. rewrite Hsubst...
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
    admit.
Admitted.
