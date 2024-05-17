Require Import Coq.Program.Equality.
Require Import Lia.

Require Import uni_counter.decl.def_extra.
Require Import uni_counter.decl.prop_basic.
Require Import uni_counter.decl.prop_typing.
Require Import uni_counter.def_ott.
Require Import uni_counter.notations.
Require Import uni_counter.decl_worklist.def.
Require Import uni_counter.ltac_utils.

Open Scope dworklist.


Ltac destruct_d_wf_wl' :=
  lazymatch goal with
    | H : d_wf_wl (dworklist_cons_work ?Ω ?w) |- _ => dependent destruction H
    | H : d_wf_wl (dworklist_cons_var ?Ω ?w ?b) |- _ => dependent destruction H
    | H : d_wf_twl (dworklist_cons_work ?Ω ?w) |- _ => dependent destruction H; solve_wf_twl_sub_false
    | H : d_wf_twl (dworklist_cons_var ?Ω ?w ?b) |- _ => dependent destruction H
    | H : d_wf_work ?Ω (?Cw _) |- _ => dependent destruction H
    | H : d_wf_work ?Ω (?Cw _ _) |- _ => dependent destruction H
    | H : d_wf_work ?Ω (?Cw _ _ _) |- _ => dependent destruction H
    | H : d_wf_typ ?E (open_typ_wrt_typ _ _) |- _ => fail
    | H : d_wf_typ ?E (?Ct ?A1 ?A2) |- _ => dependent destruction H
    | H : d_wf_exp ?E (open_exp_wrt_exp _ _) |- _ => fail
    | H : d_wf_exp ?E (open_exp_wrt_typ _ _) |- _ => fail
    | H : d_wf_exp ?E (?Ce ?b) |- _ => dependent destruction H
    | H : d_wf_exp ?E (?Ce ?e1 ?e2) |- _ => dependent destruction H
  end.

Ltac destruct_d_wf_wl :=
  repeat destruct_d_wf_wl'.

Lemma d_wf_twl_wf_tenv : forall Ω,
  ⊢ᵈʷₜ Ω -> ⊢ᵈₜ (dwl_to_denv Ω).
Proof.
  intros. induction H; simpl; auto.
  - econstructor; auto.
  - constructor; auto.
Qed.

Lemma d_wf_wl_wf_env : forall Ω,
  (⊢ᵈʷₛ Ω) -> ⊢ᵈ (dwl_to_denv Ω).
Proof.
  intros. induction H; simpl; auto.
  - econstructor; auto. 
    apply d_wf_twl_wf_tenv; auto.
  - apply d_wf_env__stvar; auto.
Qed.

Inductive d_all_work : dworklist -> Prop :=
  | d_all_work__empty : d_all_work dworklist_empty
  | d_all_work__cons_work : forall Ω w,
      d_all_work Ω -> d_all_work (dworklist_cons_work Ω w).

Lemma dwl_app_cons_work: forall Ω1 Ω2 w,
  w ⫤ᵈ Ω2 ⧺ Ω1 = (w ⫤ᵈ Ω2) ⧺ Ω1.
Proof.
  intros. auto.
Qed.

Lemma dwl_app_cons_var: forall Ω1 Ω2 X b,
  dworklist_cons_var (Ω2 ⧺ Ω1) X b = dworklist_cons_var Ω2 X b ⧺ Ω1.
Proof.
  intros. auto.
Qed.


Ltac rewrite_dwl_app :=
  repeat
    match goal with
    | _ : _ |- context [dworklist_cons_var  (dwl_app ?Ω2 ?Ω1) ?X ?b] => rewrite dwl_app_cons_var
    | _ : _ |- context [dworklist_cons_work (dwl_app ?Ω2 ?Ω1) ?w] => rewrite dwl_app_cons_work
    end.

Lemma d_wl_app_cons_work_same_env : forall Ω1 Ω2 w,
  dwl_to_denv (Ω2 ⧺ w ⫤ᵈ Ω1) = dwl_to_denv (Ω2 ⧺ Ω1).
Proof.
  intros. induction Ω2; simpl; auto.
  rewrite IHΩ2. auto.
Qed.

Ltac inv_all_work := 
  match goal with
  | H : d_all_work (dworklist_cons_var ?Ω ?x ?b) |- _ => inversion H
  | H : d_all_work (dworklist_cons_var ?Ω ?X ?b) |- _ => inversion H
  end.

Ltac destruct_all_work := 
  match goal with
  | H : d_all_work (dworklist_cons_work ?Ω ?w) |- _ => dependent destruction H
  end.

#[local] Hint Constructors d_all_work : core.

Lemma d_wl_app_all_work_same_env : forall Ω1 Ω2 Ω3,
  d_all_work Ω2 ->
  dwl_to_denv (Ω3 ⧺ Ω2 ⧺ Ω1) = dwl_to_denv (Ω3 ⧺ Ω1).
Proof. 
  intros. induction Ω3; simpl; auto. 
  - induction H; auto. 
  - rewrite IHΩ3. auto.
Qed.

Ltac solve_Ω1 IH :=
  match goal with 
  | H : ?Ω1 = ?Ω2 |- d_wl_del_red ?Ω => 
      dependent destruction H; replace Ω with (dwl_app dworklist_empty Ω) by auto; eapply IH;
      simpl; rewrite_dwl_app; eauto
  end.

Lemma d_wl_red_weaken_works : forall Ω1 Ω2 Ω3,
  (Ω3 ⧺ Ω2 ⧺ Ω1) ⟶ᵈ⁎⋅ -> d_all_work Ω2 -> (Ω3 ⧺ Ω1) ⟶ᵈ⁎⋅.
Proof with auto.
  intros * Hred Haw. dependent induction Hred;
    try destruct Ω3; simpl in x; try solve [inversion x]; dependent destruction x; simpl;
    destruct Ω2; simpl in *; 
      try solve [inversion x]; 
      try solve [dependent destruction x; eauto];
      try inv_all_work; (* Ω2 contains x or X *) 
      try solve [destruct_all_work; solve_Ω1 IHHred];
      try solve [econstructor; eauto];
      try solve [econstructor; eapply IHHred; rewrite_dwl_app; eauto].
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - econstructor; rewrite_dwl_app;
    eapply IHHred; simpl; eauto...
  - econstructor; rewrite_dwl_app;
    eapply IHHred; simpl; eauto...
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - econstructor; rewrite_dwl_app;
    eapply IHHred; simpl; eauto...
  - rewrite dwl_app_cons_work in H. rewrite d_wl_app_all_work_same_env in H...
    econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
  - econstructor; eauto.
    rewrite_dwl_app. eapply IHHred; eauto...
Qed.

Lemma d_wl_red_weaken_work1 : forall Ω1 w1 w2,
  (w2 ⫤ᵈ (w1 ⫤ᵈ Ω1)) ⟶ᵈ⁎⋅ ->  (w1 ⫤ᵈ Ω1) ⟶ᵈ⁎⋅.
Proof with auto.
  intros.  
  replace (w1 ⫤ᵈ Ω1) with ((dwl_app dworklist_empty (w1 ⫤ᵈ Ω1))) by auto.
  eapply d_wl_red_weaken_works with (Ω2:=(w2 ⫤ᵈ dworklist_empty)%dworklist)...
Qed.

Lemma d_wl_red_weaken_work2 : forall Ω1 w1 w2,
  (w2 ⫤ᵈ (w1 ⫤ᵈ Ω1)) ⟶ᵈ⁎⋅ ->  (w2 ⫤ᵈ Ω1) ⟶ᵈ⁎⋅.
Proof with auto.
  intros.  
  replace (w2 ⫤ᵈ Ω1)%dworklist with ((dwl_app (w2 ⫤ᵈ dworklist_empty) (Ω1))) by auto.
  eapply d_wl_red_weaken_works with (Ω2:=(w1 ⫤ᵈ dworklist_empty)%dworklist)...
Qed.


Theorem d_wf_work_apply_conts : forall Ω c A w,
  ⊢ᵈʷₜ Ω -> d_wf_conts (dwl_to_denv Ω) c -> dwl_to_denv Ω ᵗ⊢ᵈ A -> apply_conts c A w ->
  ⊢ᵈʷₛ dworklist_cons_work Ω w.
Proof.
  intros. induction H2; simpl; auto;
  dependent destruction H0; auto.
  - constructor; auto. constructor; auto. solve_false.
  - constructor; auto. constructor; auto. solve_false.
  - constructor; auto. constructor; auto. solve_false.
  - constructor; auto. constructor; auto. solve_false.
Qed.

Theorem d_wf_work_apply_contd : forall Ω cd A B w,
  ⊢ᵈʷₜ Ω -> 
  d_wf_contd (dwl_to_denv Ω) cd -> 
  dwl_to_denv Ω ᵗ⊢ᵈ A -> 
  dwl_to_denv Ω ᵗ⊢ᵈ B -> 
  apply_contd cd A B w ->
  ⊢ᵈʷₜ dworklist_cons_work Ω w.
Proof.
  intros. induction H3; simpl; auto;
  dependent destruction H0; auto.
  - constructor; auto. solve_false.
  - constructor; auto. solve_false.
  - constructor; auto. solve_false.
Qed.

(* Ltac destruct_d_wl_del_red' := 
  match goal with
  | H : d_wl_del_red (dworklist_cons_work ?Ω ?w) |- _ => 
    lazymatch w with 
    | work_apply (?c ?B) ?A => dependent destruction H
    | work_apply ?c ?A => fail
    | ?w1 _ _ => dependent destruction H
    | ?w1 _ _ _ => dependent destruction H
    end
  | H : d_wl_del_red (dworklist_cons_var ?Ω ?x ?A) |- _ => 
    dependent destruction H
  | H : d_wl_del_red (dworklist_cons_var ?Ω ?x ?b) |- _ => 
    dependent destruction Hƒ
  | H : apply_cont ?c ?A ?w |- _ => dependent destruction H
  (* | H : apply_cont2 ?cc ?A ?B ?w |- _ => dependent destruction H *)
  end. *)

Ltac destruct_d_wl_del_red' := 
  match goal with
  | H : d_wl_del_red (dworklist_cons_work ?Ω ?w) |- _ => 
    lazymatch w with 
    | work_applys (?c ?B) ?A => dependent destruction H
    | work_applys ?c ?A => fail
    | ?w1 _ _ => dependent destruction H
    | ?w1 _ _ _ => dependent destruction H
    end
  | H : d_wl_del_red (dworklist_cons_var ?Ω ?x ?A) |- _ => 
    dependent destruction H
  | H : d_wl_del_red (dworklist_cons_var ?Ω ?x ?b) |- _ => 
    dependent destruction H
  | H : apply_conts ?c ?A ?w |- _ => dependent destruction H
  | H : apply_contd (?cc _) ?A ?B ?w |- _ => dependent destruction H
  | H : apply_contd (?cc _ _) ?A ?B ?w |- _ => dependent destruction H
  end.

Ltac destruct_d_wl_del_red := repeat destruct_d_wl_del_red'.

Ltac _apply_IH_d_wl_red :=
  match goal with 
  | H : (⊢ᵈʷₛ ?Ω) -> (?Ω ⟶ᵈ⁎⋅) |- _ => try destruct_d_wf_wl; 
    let H1 := fresh "H" in
    assert (H1 : ⊢ᵈʷₛ Ω) by (eauto 6; repeat (constructor; eauto; try solve_false));
    apply H in H1
  end.

Lemma d_wf_twl_d_wf_wl : forall Ω,
  ⊢ᵈʷₜ Ω -> ⊢ᵈʷₛ Ω. 
Proof. 
  intros. dependent destruction H; auto.
Qed.

Lemma d_wf_twl_d_wf_tenv : forall Ω,
  ⊢ᵈʷₜ Ω -> ⊢ᵈₜ dwl_to_denv Ω. 
Proof. 
  intros. dependent induction H; simpl; auto.
  - constructor; auto. 
  - econstructor; auto.
Qed.

#[local] Hint Resolve d_wf_wl_wf_env d_wf_tenv_d_wf_env d_wf_twl_d_wf_tenv d_wf_twl_d_wf_wl : core.


#[local] Hint Immediate d_mono_typ_d_wf_typ : core.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

Theorem d_wl_red_sound: forall Ω, 
    ⊢ᵈʷₛ Ω -> Ω ⟶ᵈʷ⁎⋅ -> Ω ⟶ᵈ⁎⋅.
Proof with eauto.
  intros. induction H0; try solve [dependent destruction H; auto];
    try solve [destruct_d_wf_wl; _apply_IH_d_wl_red; destruct_d_wl_del_red; eauto].
  (* sub *)

  - destruct_d_wf_wl. 
    dependent destruction H. dependent destruction H1.
    constructor.
    eapply d_sub__all with (L:=L `union` L0 `union` L1 `union` dom (dwl_to_denv Ω)); intros; auto.
    inst_cofinites_with X.
    + assert ( ⊢ᵈʷₛ (work_sub (A ᵗ^ₜ X) (B ᵗ^ₜ X) ⫤ᵈ X ~ᵈ ■ ;ᵈ Ω) ) by eauto using d_wf_typ_tvar_stvar_cons.
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
    + pick fresh X. inst_cofinites_with X.
      assert ( ⊢ᵈʷₛ (work_sub (A ᵗ^ₜ X) (B ᵗ^ₜ X) ⫤ᵈ X ~ᵈ ■ ;ᵈ Ω) ) by  eauto using d_wf_typ_tvar_stvar_cons.
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - destruct_d_wf_wl. 
    dependent destruction H.
    assert (Hwf: ⊢ᵈʷₛ (work_sub (A ᵗ^^ₜ T) B ⫤ᵈ Ω)). {
      apply d_wf_wl__conswork_sub; auto.
      apply d_wf_typ_all_open; auto.
      inst_cofinites_for d_wf_typ__all...
    }
    _apply_IH_d_wl_red... destruct_d_wl_del_red...
  - destruct_d_wf_wl. constructor.
    + inst_cofinites_for d_chk_inf__chk_abs...
      intros. inst_cofinites_with x.
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^ₑ exp_var_f x) A2 ⫤ᵈ x ~ᵈ A1;ᵈ Ω)). {
        repeat (constructor; simpl; auto)...
        eapply d_wf_exp_var_binds_another_cons...
        apply d_wf_typ_weaken_cons...
      }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
    + pick fresh x. inst_cofinites_with x.
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^ₑ exp_var_f x) A2 ⫤ᵈ x ~ᵈ A1;ᵈ Ω)). {
        repeat (constructor; simpl; auto)...
        eapply d_wf_exp_var_binds_another_cons...
        apply d_wf_typ_weaken_cons... 
      }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
  - destruct_d_wf_wl. econstructor.
    + apply d_chk_inf__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
      intros. inst_cofinites_with x...
      assert (⊢ᵈʷₛ (work_check (e ᵉ^ₑ exp_var_f x) typ_top ⫤ᵈ x ~ᵈ typ_bot;ᵈ Ω)).
      { repeat constructor... simpl. eapply d_wf_exp_var_binds_another_cons...  }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
    + pick fresh x. inst_cofinites_with x.
      assert (⊢ᵈʷₛ (work_check (e ᵉ^ₑ exp_var_f x) typ_top ⫤ᵈ x ~ᵈ typ_bot;ᵈ Ω)).
      { repeat constructor... simpl. eapply d_wf_exp_var_binds_another_cons...  }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
  - destruct_d_wf_wl...
    eapply d_wl_del_red__inf with (A:=A)...
    assert (uniq (dwl_to_denv Ω))...
    unify_binds. 
    apply IHd_wl_red...
    repeat (constructor; simpl; auto)...
    eapply d_wf_env_binds_d_wf_typ; eauto...
  - destruct_d_wf_wl.
    apply d_wl_del_red__inf with (A:=typ_all A).
    + inst_cofinites_for d_chk_inf__inf_tabs...
      * inst_cofinites_for d_wf_typ__all...
        intros. inst_cofinites_with X. dependent destruction H...
        intros. inst_cofinites_with X.
        dependent destruction H0...
      * destruct_d_wf_wl. intros. inst_cofinites_with X.
        rewrite open_body_wrt_typ_anno in *.
        dependent destruction H0.  dependent destruction H... 
        assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵈ X ~ᵈ □ ;ᵈ work_applys cs (typ_all A) ⫤ᵈ Ω)). {
          repeat (constructor; simpl; auto)... 
          inst_cofinites_for d_wf_typ__all...
          - intros. eapply s_in_rename with (Y:=X0) in H0... 
            rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H0...
          - intros. apply d_wf_typ_rename_tvar_cons with (Y:=X0) in H1. 
            rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H1...
        }
        _apply_IH_d_wl_red. destruct_d_wl_del_red...
    + pick fresh X. inst_cofinites_with X.
      rewrite open_body_wrt_typ_anno in *.
      dependent destruction H0.  dependent destruction H... 
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵈ X ~ᵈ □ ;ᵈ work_applys cs (typ_all A) ⫤ᵈ Ω)). {
        repeat (constructor; simpl; auto)... solve_false.
        inst_cofinites_for d_wf_typ__all...
        - intros. eapply s_in_rename with (Y:=X0) in H0... 
          rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H0...
        - intros. apply d_wf_typ_rename_tvar_cons with (Y:=X0) in H1. 
          rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H1...
      }
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - destruct_d_wf_wl. 
    eapply d_wl_del_red__inf with (A:=(typ_arrow T1 T2))...
    + inst_cofinites_for d_chk_inf__inf_abs_mono...
      intros. inst_cofinites_with x...
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^ₑ exp_var_f x) T2 ⫤ᵈ x ~ᵈ T1;ᵈ work_applys cs (typ_arrow T1 T2) ⫤ᵈ Ω)). {
        dependent destruction H4.
        repeat (constructor; simpl; eauto)...
        - eapply d_wf_exp_var_binds_another_cons...
        - apply d_wf_typ_weaken_cons...
      }
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
    + pick fresh x. inst_cofinites_with x...
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^ₑ exp_var_f x) T2 ⫤ᵈ x ~ᵈ T1;ᵈ work_applys cs (typ_arrow T1 T2) ⫤ᵈ Ω)). {
        dependent destruction H4.
        repeat (constructor; simpl; eauto)...
        - eapply d_wf_exp_var_binds_another_cons...
        - apply d_wf_typ_weaken_cons...
      }
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - destruct_d_wf_wl. _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    eapply d_wl_del_red__inf with (A:=B).
    + econstructor; eauto. apply d_wl_red_weaken_work1 in H8. inversion H8... 
    + eapply d_wl_red_weaken_work2; eauto.
  - destruct_d_wf_wl. 
    assert (⊢ᵈʷₛ (work_applys cs (A ᵗ^^ₜ B) ⫤ᵈ Ω)).
    { repeat constructor... apply d_wf_typ_all_open... }
    _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - destruct_d_wf_wl. 
    assert (⊢ᵈʷₛ (work_infabs (A ᵗ^^ₜ T) cd ⫤ᵈ Ω)).
    { repeat constructor... apply d_wf_typ_all_open... }
    _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - econstructor; eauto.
    destruct_d_wf_wl.
    eapply d_wf_work_apply_conts in H0; eauto.
  - econstructor; eauto.
    destruct_d_wf_wl.
    eapply d_wf_work_apply_contd with (A:=A) in H0; eauto.
Qed.


Lemma d_wl_red_sub_complete: forall Ω A B,
  dwl_to_denv Ω ⊢ A <: B -> ⊢ᵈʷₛ (work_sub A B ⫤ᵈ Ω) -> 
  Ω ⟶ᵈʷ⁎⋅ -> (work_sub A B ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅.
Proof with auto.
  intros * Hsub Hwfwl Hred.
  dependent induction Hsub; 
  try solve [destruct_d_wf_wl; econstructor; auto].
  - destruct_d_wf_wl.
    eapply d_wl_red__sub_all with (L:=L `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with X.
    apply H2; eauto...
    apply d_sub_d_wf in H1; intuition.
  - destruct_d_wf_wl. 
    eapply d_wl_red__sub_alll with (T:=T); eauto. 
    apply IHHsub; eauto.
    apply d_wf_wl__conswork_sub; auto. 
    apply d_wf_typ_all_open; eauto; auto.
Qed.


Lemma d_wl_app_assoc : forall Ω1 Ω2 Ω3,
  Ω3 ⧺ Ω2 ⧺ Ω1 = (Ω3 ⧺ Ω2) ⧺ Ω1.
Proof.
  induction Ω3; auto.
  - simpl. rewrite <- IHΩ3. auto.
  - simpl. rewrite <- IHΩ3. auto.
Qed.

Lemma d_wl_red_weaken: forall Ω1 Ω2,
  (Ω2 ⧺ Ω1) ⟶ᵈʷ⁎⋅ -> Ω1 ⟶ᵈʷ⁎⋅ .
Proof.
  intros. dependent induction H; try destruct Ω2; simpl in x; 
    try solve [inversion x]; dependent destruction x; simpl; eauto;
    try solve [eapply IHd_wl_red; rewrite_dwl_app; eauto].
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H1.
    rewrite_dwl_app; eauto.
Qed.

Corollary d_wl_red_weaken_consw : forall Ω w,
  (w ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅ -> Ω ⟶ᵈʷ⁎⋅ .
Proof.
  intros.
  replace (w ⫤ᵈ Ω)%dworklist with (dwl_app (dworklist_cons_work dworklist_empty w) Ω) in H by auto.
  eapply d_wl_red_weaken. eauto.
Qed.

Lemma dwl_to_aenv_work : forall Ω2 Ω1 w,
  dwl_to_aenv (Ω2 ⧺ Ω1) = dwl_to_aenv (Ω2 ⧺ w ⫤ᵈ Ω1).
Proof.
  intros. induction Ω2; simpl; auto.
  rewrite IHΩ2. auto.
Qed.

Lemma d_wl_red_strengthen_work : forall Ω1 Ω2 w,
  (w ⫤ᵈ Ω1) ⟶ᵈʷ⁎⋅ -> (Ω2 ⧺ Ω1) ⟶ᵈʷ⁎⋅ -> (Ω2 ⧺ w ⫤ᵈ Ω1) ⟶ᵈʷ⁎⋅ .
Proof. 
  intros. dependent induction H0; 
      try destruct Ω2; simpl in x; try solve [inversion x]; dependent destruction x; simpl; eauto;
      try solve [econstructor; rewrite_dwl_app; eauto].
  - eapply d_wl_red__sub_all with (L:=L). 
    intros. inst_cofinites_with X. 
    rewrite_dwl_app. auto.
  - eapply d_wl_red__sub_alll with (T:=T); auto.
    rewrite d_wl_app_cons_work_same_env; auto.
    rewrite_dwl_app. auto.
  - eapply d_wl_red__chk_absarrow with (L:=L).
    intros. inst_cofinites_with x.
    rewrite_dwl_app. auto.
  - eapply d_wl_red__chk_abstop with (L:=L).
    intros. inst_cofinites_with x.
    rewrite_dwl_app. auto.
  - eapply d_wl_red__inf_var with (A:=A). 
    rewrite d_wl_app_cons_work_same_env. auto.
    rewrite_dwl_app. auto.
  - eapply d_wl_red__inf_tabs with (L:=L).
    intros. inst_cofinites_with X.
    rewrite_dwl_app. auto.
  - eapply d_wl_red__inf_abs_mono with (T1:=T1) (T2:=T2) (L:=L); auto.
    rewrite d_wl_app_cons_work_same_env. auto.
    intros. inst_cofinites_with x.
    rewrite_dwl_app. auto.
  - econstructor. rewrite <- dwl_to_aenv_work.
    eapply IHd_wl_red with (Ω2 := work_infer e1 (conts_infabs (contd_infapp (exp_split_size (dwl_to_aenv (Ω2 ⧺ Ω1)) e1) e2 cs)) ⫤ᵈ Ω2); eauto.
  - eapply d_wl_red__infabs_all with (T:=T).
    rewrite d_wl_app_cons_work_same_env. auto.
    rewrite_dwl_app. auto.
Qed.


Lemma d_wl_red_infabs_complete: forall Ω A B C cd,
   dwl_to_denv Ω ⊢ A ▹ B → C -> d_wf_twl (dworklist_cons_work Ω (work_infabs A cd)) -> 
   d_wl_red (dworklist_cons_work Ω (work_applyd cd B C)) -> d_wl_red (dworklist_cons_work Ω (work_infabs A cd)).
Proof with auto.
  intros. generalize dependent cd. dependent induction H; intros; eauto;
  try solve [destruct_d_wf_wl; econstructor; auto].
  - destruct_d_wf_wl.
    eapply d_wl_red__infabs_all with (T:=T); eauto.
  - destruct_d_wf_wl.
    apply d_infabs_d_wf in H.
    apply d_wl_red__infabs_union.
    apply IHd_infabs1; auto.
    eapply d_wl_red__applyd with 
      (w:=((work_infabsunion B1 C1 A2 cd)))...
    eapply apply_contd__infabsunion.
    eapply d_wl_red__infabsunion...
    apply IHd_infabs2; intuition...
    eapply d_wl_red__applyd with 
      (w:=(work_unioninfabs  B1 C1 B2 C2 cd))...
    econstructor.
Qed.


Lemma d_wl_red_inftapp_complete: forall Ω A B C cs,
  dwl_to_denv Ω ⊢ A ○ B ⇒⇒ C -> d_wf_wl (dworklist_cons_work Ω (work_inftapp A B cs)) ->
  d_wl_red (dworklist_cons_work Ω (work_applys cs C)) -> d_wl_red (dworklist_cons_work Ω (work_inftapp A B cs)).
Proof with auto.
  intros. generalize dependent cs. dependent induction H; intros; eauto;
  try solve [destruct_d_wf_wl; econstructor; eauto].
  - apply d_inftapp_d_wf in H.
    destruct_d_wf_wl.
    econstructor.
    eapply IHd_inftapp1...
    eapply d_wl_red__applys with (w:=work_inftappunion C1 A2 B cs).
    econstructor.
    simpl.
    econstructor. 
    eapply IHd_inftapp2... intuition.
    eapply d_wl_red__applys with (w:=work_unioninftapp C1 C2 cs).
    eapply apply_conts__unioninftapp...
    econstructor...
Qed.


Ltac destruct_binds_eq :=
  repeat
    lazymatch goal with
    | H1 : (?X1, ?b1) = (?X2, ?b2) |- _ =>
      dependent destruction H1
    end.

Ltac destruct_binds :=
  simpl in *;
  repeat
  match goal with
  | H1 : binds ?X ?b ((?X', ?b') :: ?θ) |- _ =>
    let H_1 := fresh "H" in
    let H_2 := fresh "H" in
    inversion H1 as [H_1 | H_2];
    clear H1;
    try destruct_binds_eq;
    try solve [solve_notin_eq X];
    try solve [solve_notin_eq X']
  end.


Ltac destruct_in :=
  simpl in *;
  match goal with
  | H1 : ((?X, ?b) = (?X', ?b')) \/  In ?b'' ?θ |- _ =>
    let H1_1 := fresh "H" in
    let H1_2 := fresh "H" in
    inversion H1 as [H1_1 | H1_2];
    clear H1;
    try destruct_binds_eq;
    try solve [solve_notin_eq X];
    try solve [solve_notin_eq X']
  end.


Lemma binds_lookup_tvar_bind : forall Σ X B,
  ⊢ᵃ Σ -> B = abind_tvar_empty \/ B = abind_stvar_empty \/ B = abind_etvar_empty ->
  binds X B Σ <-> lookup_tvar_bind Σ X = Some B.
Proof.
  intros. induction H; simpl.
  - split; intros; inversion H.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H2; auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H2; auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H2; auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        destruct H0 as [Hcontra | [Hcontra | Hcontra]]; inversion Hcontra.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H3.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
Qed.

Lemma binds_lookup_var_bind : forall Σ X A,
  ⊢ᵃ Σ -> binds X (abind_var_typ A) Σ <-> lookup_var_bind Σ X = Some A.
Proof.
  intros. induction H; simpl; split; intros; try solve [inversion H];
    try solve [destruct_binds; eapply IHa_wf_env; eauto];
    try solve [eapply binds_cons; eapply IHa_wf_env; eauto].
  - destruct_eq_atom; destruct_binds; eauto.
    + exfalso; eapply binds_dom_contradiction; eauto.
    + eapply IHa_wf_env; eauto.
  - destruct_eq_atom.
    + inversion H2; eauto.
    + eapply binds_cons; eauto. eapply IHa_wf_env; eauto.
Qed.

Lemma dbind_to_abind_inj : forall B1 B2,
  dbind_to_abind B1 = dbind_to_abind B2 -> B1 = B2.
Proof.
  intros. destruct B1; destruct B2; simpl in *; inversion H; auto.
Qed.

Lemma binds_dwl_aenv : forall Ω X B,
  binds X B (⌊ Ω ⌋ᵈ) <-> binds X (dbind_to_abind B) (dwl_to_aenv Ω).
Proof.
  intros Ω. induction Ω; intros *; simpl in *; split; intros; try solve [inversion H]; destruct_binds; auto;
    try solve [apply IHΩ; auto; dependent destruction Hwf; try solve [dependent destruction H; auto]; auto].
  - apply binds_cons. apply IHΩ; auto.
  - eapply dbind_to_abind_inj in x. subst. auto.
  - apply binds_cons. apply IHΩ; auto.
Qed.

Lemma dwl_to_aenv_wf_typ : forall Ω A,
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ A -> dwl_to_aenv Ω ᵗ⊢ᵃ A.
Proof.
  intros. dependent induction H; simpl; auto;
    try solve [apply binds_dwl_aenv in H; auto].
  econstructor; eauto. intros X Hnotin.
  replace (X ~ □%abind ++ dwl_to_aenv Ω) with (dwl_to_aenv (dworklist_cons_var Ω X □%dbind)); eauto.
Qed.

Lemma dwl_to_aenv_dom : forall Ω,
  dom (⌊ Ω ⌋ᵈ) = dom (dwl_to_aenv Ω).
Proof.
  intros Ω. induction Ω; simpl; auto.
  rewrite IHΩ. auto.
Qed.

Lemma d_wf_twl_wf_aenv : forall Ω,
   ⊢ᵈʷₜ Ω -> ⊢ᵃ (dwl_to_aenv Ω).
Proof.
  intros. induction H; simpl; try rewrite dwl_to_aenv_dom in H; auto;
    constructor; auto.
  apply dwl_to_aenv_wf_typ; auto.
Qed.

Lemma d_wf_wl_wf_aenv : forall Ω,
  ⊢ᵈʷₛ Ω -> ⊢ᵃ (dwl_to_aenv Ω).
Proof.
  intros. induction H; simpl; auto.
  - apply d_wf_twl_wf_aenv; auto.
  - constructor; auto.
    rewrite dwl_to_aenv_dom in H; auto.
Qed.

Lemma binds_lookup_tvar_bind_dwl : forall Ω X B,
  ⊢ᵈʷₛ Ω -> B = dbind_tvar_empty \/ B = dbind_stvar_empty ->
  binds X B (⌊ Ω ⌋ᵈ) <-> lookup_tvar_bind (dwl_to_aenv Ω) X = Some (dbind_to_abind B).
Proof.
  intros. split; intros.
  - apply binds_lookup_tvar_bind; auto.
    apply d_wf_wl_wf_aenv; auto.
    destruct H0; subst; auto.
    apply binds_dwl_aenv; auto.
  - apply binds_lookup_tvar_bind in H1; auto.
    apply binds_dwl_aenv; auto.
    apply d_wf_wl_wf_aenv; auto.
    destruct H0; subst; auto.
Qed.

Lemma binds_lookup_var_bind_dwl : forall Ω X A,
  ⊢ᵈʷₛ Ω -> binds X (dbind_typ A) (⌊ Ω ⌋ᵈ) <-> lookup_var_bind (dwl_to_aenv Ω) X = Some A.
Proof.
  intros. split; intros.
  - apply binds_lookup_var_bind; auto.
    apply d_wf_wl_wf_aenv; auto.
    apply binds_dwl_aenv with (B := dbind_typ A); auto.
  - apply binds_lookup_var_bind in H0; auto.
    apply binds_dwl_aenv; auto.
    apply d_wf_wl_wf_aenv; auto.
Qed.

Lemma iuv_size_d_mono : forall Γ A,
  d_mono_typ Γ A -> iuv_size A = 0.
Proof.
  intros Γ A Hmono.
  induction Hmono; simpl; eauto; try lia.
Qed.

Lemma iuv_size_open_d_mono_rec : forall Ψ A T n,
  d_mono_typ Ψ T ->
  iuv_size (open_typ_wrt_typ_rec n T A) <= iuv_size A.
Proof.
  intros Ψ A T n Hmono.
  generalize dependent n.
  induction A; intros; simpl; auto;
    try specialize (IHA1 n); try specialize (IHA2 n); try lia.
  destruct (lt_eq_lt_dec n n0); simpl; auto.
  destruct s; simpl; auto; subst.
  erewrite iuv_size_d_mono; eauto.
Qed.

Lemma iuv_size_open_d_mono : forall Ψ A T,
  d_mono_typ Ψ T ->
  iuv_size (open_typ_wrt_typ A T) <= iuv_size A.
Proof.
  intros Ψ A T Hmono.
  eapply iuv_size_open_d_mono_rec; eauto.
Qed.

Lemma infabs_iuv_size_B : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> iuv_size B <= iuv_size A.
Proof.
  intros. induction H; simpl; auto; try lia.
  assert (iuv_size (A ᵗ^^ₜ T) <= iuv_size A). { eapply iuv_size_open_d_mono; eauto. }
  lia.
Qed.

Lemma infabs_iuv_size_C : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> iuv_size C <= iuv_size A.
Proof.
  intros. induction H; simpl; auto; try lia.
  assert (iuv_size (A ᵗ^^ₜ T) <= iuv_size A). { eapply iuv_size_open_d_mono; eauto. }
  lia.
Qed.

Lemma iuv_size_open_typ_wrt_typ_rec : forall A B n,
  iuv_size (open_typ_wrt_typ_rec n B A) <= iuv_size A * (1 + iuv_size B).
Proof.
  intros A B.
  induction A; intros; simpl; eauto; try lia.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; simpl; eauto; lia.
    + simpl; eauto; lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
  - specialize (IHA1 n). specialize (IHA2 n). lia.
Qed.

Lemma iuv_size_open_typ_wrt_typ : forall A B,
  iuv_size (open_typ_wrt_typ A B) <= (1 + iuv_size A) * (2 + iuv_size B).
Proof.
  intros. unfold open_typ_wrt_typ.
  specialize (iuv_size_open_typ_wrt_typ_rec A B 0). lia.
Qed.

Lemma inftapp_iuv_size : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  iuv_size C <= (1 + iuv_size A) * (2 + iuv_size B).
Proof.
  intros. induction H; simpl; auto; try lia.
  eapply iuv_size_open_typ_wrt_typ.
Qed.

Lemma inf_iuv_size_exp_split_size : forall Ω A e,
  ⊢ᵈʷₛ Ω ->
  ⌊ Ω ⌋ᵈ ⊢ e ⇒ A ->
  iuv_size A <= exp_split_size (dwl_to_aenv Ω) e.
Proof.
  intros Ω A e Hwf Hinf. dependent induction Hinf; simpl; auto; try lia.
  - apply binds_lookup_var_bind_dwl in H0; auto. rewrite H0. simpl. auto.
  - assert (Hle: iuv_size C <= iuv_size A). { eapply infabs_iuv_size_C; eauto. }
    assert (Hle': iuv_size A <= exp_split_size (dwl_to_aenv Ω) e1) by auto. lia.
  - dependent destruction H.
    eapply iuv_size_d_mono in H. eapply iuv_size_d_mono in H0. subst. lia.
  - assert (Hle: iuv_size C <= (1 + iuv_size A) * (2 + iuv_size B)). { eapply inftapp_iuv_size; eauto. }
    assert (Hle': iuv_size A <= exp_split_size (dwl_to_aenv Ω) e1) by auto.
    eapply le_trans with (m := (1 + iuv_size A) * (2 + iuv_size B)); try lia.
    replace (S (S (iuv_size B + exp_split_size (dwl_to_aenv Ω) e1 * S (S (iuv_size B))))) with ((1 + exp_split_size (dwl_to_aenv Ω) e1) * (2 + iuv_size B)) by lia.
    eapply mult_le_compat_r. lia.
Qed.

Lemma iu_size_le_iuv_size : forall A,
  iu_size A <= iuv_size A.
Proof.
  induction A; simpl; auto; try lia.
Qed.

Lemma d_wl_red_chk_inf_complete: forall Ω e A mode,
  d_chk_inf (dwl_to_denv Ω) e mode A -> 
  match mode with 
  | typingmode__chk => ⊢ᵈʷₛ (work_check e A ⫤ᵈ Ω) -> Ω ⟶ᵈʷ⁎⋅ -> (work_check e A ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅
  | typingmode__inf => forall c, ⊢ᵈʷₛ (work_infer e c ⫤ᵈ Ω) -> (work_applys c A ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅ -> (work_infer e c ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅
  end.
Proof with auto.
  intros. dependent induction H; intros; eauto...
  (* - econstructor; eauto. *)
  - econstructor. 
    eapply IHd_chk_inf; eauto.
    destruct_d_wf_wl...
  - econstructor.
    destruct_d_wf_wl.
    eapply IHd_chk_inf1; eauto 7...
    apply d_wl_red__applys with (w:=work_infabs A (contd_infapp (exp_split_size (dwl_to_aenv Ω) e1) e2 c)); eauto.
    econstructor. simpl.
    apply d_infabs_d_wf in H0 as Hwft. intuition.
    eapply d_wl_red_infabs_complete; eauto.
    econstructor... econstructor...
    eapply inf_iuv_size_exp_split_size in H as Hle1; eauto.
    eapply infabs_iuv_size_B in H0 as Hle2.
    specialize (iu_size_le_iuv_size B) as Hle3. lia.
    econstructor.
    assert ((work_check e2 B ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅).
      apply IHd_chk_inf2; auto.
      apply d_wl_red_weaken_consw in H6; auto.
    replace (work_applys c C ⫤ᵈ work_check e2 B ⫤ᵈ Ω) with ((work_applys c C ⫤ᵈ dworklist_empty) ⧺ work_check e2 B ⫤ᵈ Ω) by auto.
    apply d_wl_red_strengthen_work; eauto.
  - destruct_d_wf_wl.
    eapply d_wl_red__inf_abs_mono with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)); eauto.
    intros. inst_cofinites_with x.
    apply H1...   
    apply d_mono_typ_d_wf_typ in H. dependent destruction H.
    repeat constructor; simpl...
    eapply d_wf_exp_var_binds_another_cons; eauto.
    apply d_wf_typ_weaken_cons...
  - destruct_d_wf_wl. 
    eapply d_wl_red__inf_tabs with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)); eauto. 
    intros. inst_cofinites_with X. dependent destruction H3.
    apply H1; auto 7.
  - destruct_d_wf_wl.
    apply d_chk_inf_wf_typ in H0.
    econstructor.
    apply IHd_chk_inf; auto...
    apply d_wl_red__applys with (w:=(work_inftapp A B c)); eauto.
    econstructor.
    simpl.
    eapply d_wl_red_inftapp_complete; eauto.
  - destruct_d_wf_wl.
    eapply d_wl_red__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H0... repeat (constructor; simpl; auto).
    rewrite_env ((x ~ dbind_typ typ_bot) ++ dwl_to_denv Ω).
    eapply d_wf_exp_var_binds_another_cons; eauto.
  - destruct_d_wf_wl.
    eapply d_wl_red__chk_absarrow with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H1...
    repeat (constructor; simpl; auto). 
    eapply d_wf_exp_var_binds_another_cons; eauto.
    simpl. apply d_wf_typ_weaken_cons...
  - destruct_d_wf_wl. econstructor. 
    apply IHd_chk_inf; auto...
    eapply d_wl_red__applys with (w:=(work_sub B A)); eauto.
    constructor; auto. simpl.
    apply d_wl_red_sub_complete; auto.
    apply d_chk_inf_wf_typ in H. auto.
  - destruct_d_wf_wl. eapply d_wl_red__chk_inter; eauto 11...
  - destruct_d_wf_wl. eauto 7. 
  - destruct_d_wf_wl. eauto 7. 
Qed.


Theorem d_wl_red_complete: forall Ω, 
    ⊢ᵈʷₛ Ω -> Ω ⟶ᵈ⁎⋅ -> Ω ⟶ᵈʷ⁎⋅.
Proof with auto.
  intros. induction H0; auto;
  try solve [destruct_d_wf_wl; econstructor; eauto 7].
  - destruct_d_wf_wl.
    refine (d_wl_red_chk_inf_complete _ _ _ _ H3 _ _); auto...
  - destruct_d_wf_wl.
    refine (d_wl_red_chk_inf_complete _ _ _ _ H3 _ _ _); auto...
    apply d_chk_inf_wf_typ in H3.
    apply IHd_wl_del_red. auto.
  - destruct_d_wf_wl. eapply d_wl_red_infabs_complete; eauto...
  - destruct_d_wf_wl. 
    apply d_wl_red__infabsunion.
    eapply d_wl_red_infabs_complete; eauto.
    eapply d_wl_red__applyd with (w:=(work_unioninfabs B1 C1 B2 C2 cd)).
    apply apply_contd__unioninfabs.
    simpl. econstructor.
    apply d_infabs_d_wf in H5. 
    apply IHd_wl_del_red. intuition.
  - destruct_d_wf_wl. eapply d_wl_red_inftapp_complete; eauto.
  - destruct_d_wf_wl. econstructor. 
    eapply d_wl_red_inftapp_complete; eauto...
    eapply d_wl_red__applys with (w:=(work_unioninftapp C1 C2 cs))...
    econstructor. simpl.
    apply d_inftapp_d_wf in H5.
    econstructor. intuition. eauto 6.
  - destruct_d_wf_wl. 
    apply d_wl_red_sub_complete; eauto.
  - destruct_d_wf_wl. econstructor; eauto.
    apply IHd_wl_del_red. eapply d_wf_work_apply_conts; eauto.
  - destruct_d_wf_wl. econstructor; eauto.
    apply IHd_wl_del_red. eapply d_wf_work_apply_contd in H4; eauto 7.
Qed.
