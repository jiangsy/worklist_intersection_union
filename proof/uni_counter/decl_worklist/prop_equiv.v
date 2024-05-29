Require Import Coq.Program.Equality.
Require Import Lia.

Require Import uni_counter.decl.def_extra.
Require Import uni_counter.decl.prop_basic.
Require Import uni_counter.decl.prop_rename.
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
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵈ x ~ᵈ A1;ᵈ Ω)). {
        repeat (constructor; simpl; auto)...
        eapply d_wf_exp_var_binds_another_cons...
        apply d_wf_typ_weaken_cons...
      }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
    + pick fresh x. inst_cofinites_with x.
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵈ x ~ᵈ A1;ᵈ Ω)). {
        repeat (constructor; simpl; auto)...
        eapply d_wf_exp_var_binds_another_cons...
        apply d_wf_typ_weaken_cons... 
      }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
  - destruct_d_wf_wl. econstructor.
    + apply d_chk_inf__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
      intros. inst_cofinites_with x...
      assert (⊢ᵈʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵈ x ~ᵈ typ_bot;ᵈ Ω)).
      { repeat constructor... simpl. eapply d_wf_exp_var_binds_another_cons...  }
      _apply_IH_d_wl_red... destruct_d_wl_del_red...
    + pick fresh x. inst_cofinites_with x.
      assert (⊢ᵈʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵈ x ~ᵈ typ_bot;ᵈ Ω)).
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
      * destruct_d_wf_wl. intros. inst_cofinites_with_keep X. 
        assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵈ X ~ᵈ □ ;ᵈ work_applys cs (typ_all A) ⫤ᵈ Ω)). {
          dependent destruction H4.
          repeat (constructor; simpl; auto)... 
          inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0...
          dependent destruction H9...
        }
        _apply_IH_d_wl_red. destruct_d_wl_del_red...
    + pick fresh X. inst_cofinites_with_keep X.
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵈ X ~ᵈ □ ;ᵈ work_applys cs (typ_all A) ⫤ᵈ Ω)). {
        dependent destruction H4...
        repeat (constructor; simpl; auto)...
        inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0...
        dependent destruction H8...
      }
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - destruct_d_wf_wl. 
    eapply d_wl_del_red__inf with (A:=(typ_arrow T1 T2))...
    + inst_cofinites_for d_chk_inf__inf_abs_mono...
      intros. inst_cofinites_with x...
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) T2 ⫤ᵈ x ~ᵈ T1;ᵈ work_applys cs (typ_arrow T1 T2) ⫤ᵈ Ω)). {
        dependent destruction H4.
        repeat (constructor; simpl; eauto)...
        - eapply d_wf_exp_var_binds_another_cons...
        - apply d_wf_typ_weaken_cons...
      }
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
    + pick fresh x. inst_cofinites_with x...
      assert (Hwf: ⊢ᵈʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) T2 ⫤ᵈ x ~ᵈ T1;ᵈ work_applys cs (typ_arrow T1 T2) ⫤ᵈ Ω)). {
        dependent destruction H4.
        repeat (constructor; simpl; eauto)...
        - eapply d_wf_exp_var_binds_another_cons...
        - apply d_wf_typ_weaken_cons...
      }
      _apply_IH_d_wl_red. destruct_d_wl_del_red...
  - destruct_d_wf_wl. _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    eapply d_wl_del_red__inf with (A:=B).
    + econstructor; eauto. apply d_wl_red_weaken_work1 in H9. inversion H9... 
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

Lemma dwl_to_denv_work : forall Ω2 Ω1 w,
  dwl_to_denv (Ω2 ⧺ Ω1) = dwl_to_denv (Ω2 ⧺ w ⫤ᵈ Ω1).
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
  - econstructor. rewrite <- dwl_to_denv_work. eauto.
    eapply IHd_wl_red with (Ω2 := work_infer e1 (conts_infabs (contd_infapp n e2 cs)) ⫤ᵈ Ω2); eauto.
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

Lemma num_occurs_in_typ_det : forall X A n1 n2,
  num_occurs_in_typ X A n1 -> num_occurs_in_typ X A n2 -> n1 = n2.
Proof.
  intros * Hocc1. generalize dependent n2.
  dependent induction Hocc1; intros * Hocc2; dependent destruction Hocc2; auto;
    try solve [exfalso; apply H; auto].
  pick fresh Y. inst_cofinites_with Y. eapply H0. eauto.
Qed.

Lemma num_occurs_in_typ_open_typ_wrt_typ_rename : forall X Y Z A n,
  (* Some additional conditions -> *)
  num_occurs_in_typ X (open_typ_wrt_typ A (typ_var_f Y)) n ->
  num_occurs_in_typ X (open_typ_wrt_typ A (typ_var_f Z)) n.
Admitted.

Lemma num_occurs_in_typ_total_a_wf_typ : forall Ψ X A,
  a_wf_typ Ψ A -> exists n, num_occurs_in_typ X A n.
Proof.
  intros * Hwf. induction Hwf; eauto using num_occurs_in_typ;
    try solve [destruct (X == X0); subst; eauto using num_occurs_in_typ].
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2].
    eauto using num_occurs_in_typ.
  - pick fresh Y. inst_cofinites_with Y.
    destruct H1 as [n H1]. exists n.
    eapply num_occurs_in_typ__all with (L := L). intros * Hnin.
    eapply num_occurs_in_typ_open_typ_wrt_typ_rename with (Z := Y0) in H1. auto.
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2].
    eauto using num_occurs_in_typ.
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2]. 
    eauto using num_occurs_in_typ.
Qed.

(* Please consider refactor *)
Lemma num_occurs_in_typ_total_d_wf_typ : forall Ψ X A,
  Ψ ᵗ⊢ᵈ A -> exists n, num_occurs_in_typ X A n.
Proof.
  intros * Hwf. induction Hwf; eauto using num_occurs_in_typ;
    try solve [destruct (X == X0); subst; eauto using num_occurs_in_typ].
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2].
    eauto using num_occurs_in_typ.
  - pick fresh Y. inst_cofinites_with Y.
    destruct H1 as [n H1]. exists n.
    eapply num_occurs_in_typ__all with (L := L). intros * Hnin.
    eapply num_occurs_in_typ_open_typ_wrt_typ_rename with (Z := Y0) in H1. auto.
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2].
    eauto using num_occurs_in_typ.
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2]. 
    eauto using num_occurs_in_typ.
Qed.

Lemma d_iuv_size_det : forall Ψ A n1 n2,
  d_iuv_size Ψ A n1 -> d_iuv_size Ψ A n2 -> n1 = n2.
Proof.
  intros * Hiuv1. generalize dependent n2.
  dependent induction Hiuv1; intros * Hiuv2; dependent destruction Hiuv2; auto.
  pick fresh X. inst_cofinites_with X.
  erewrite H0; eauto. erewrite num_occurs_in_typ_det with (n1 := m); eauto.
Qed.

Lemma d_iuv_size_d_mono : forall Γ A,
  d_mono_typ Γ A -> d_iuv_size Γ A 0.
Proof.
  intros Γ A Hmono.
  induction Hmono; simpl; eauto using d_iuv_size; try lia.
  replace 0 with (0 + 0) by auto. eauto using d_iuv_size.
Qed.

Lemma d_iuv_size_subst_mono_cons : forall Ψ A X B n,
  d_mono_typ Ψ B ->
  d_iuv_size (X ~ □ ++ Ψ) (A ᵗ^ₜ X) n ->
  d_iuv_size Ψ (A ᵗ^^ₜ B) n.
Admitted.

Lemma infabs_d_iuv_size_B : forall Ψ A B C n m,
  Ψ ⊢ A ▹ B → C -> d_iuv_size Ψ A n -> d_iuv_size Ψ B m -> m <= n.
Proof.
  intros * Hinf. generalize dependent m. generalize dependent n.
  dependent induction Hinf; intros * HiuvA HiuvB.
  - dependent destruction HiuvA. dependent destruction HiuvB. auto.
  - dependent destruction HiuvA.
    erewrite d_iuv_size_det with (n1 := n1); eauto. lia.
  - dependent destruction HiuvA.
    pick fresh X. inst_cofinites_with X.
    eapply d_iuv_size_subst_mono_cons with (B := T) in H2; eauto.
    eapply IHHinf in H2; eauto. lia.
  - dependent destruction HiuvA.
    eapply IHHinf in HiuvA1; eauto. lia.
  - dependent destruction HiuvA.
    eapply IHHinf in HiuvA2; eauto. lia.
  - dependent destruction HiuvA. dependent destruction HiuvB.
    eapply IHHinf1 in HiuvA1; eauto.
    eapply IHHinf2 in HiuvA2; eauto. lia.
Qed. 

Lemma infabs_d_iuv_size_C : forall Ψ A B C n m,
  Ψ ⊢ A ▹ B → C -> d_iuv_size Ψ A n -> d_iuv_size Ψ C m -> m <= n.
Proof.
  intros * Hinf. generalize dependent m. generalize dependent n.
  dependent induction Hinf; intros * HiuvA HiuvC.
  - dependent destruction HiuvA. dependent destruction HiuvC. auto.
  - dependent destruction HiuvA.
    erewrite d_iuv_size_det with (n1 := n2); eauto. lia.
  - dependent destruction HiuvA.
    pick fresh X. inst_cofinites_with X.
    eapply d_iuv_size_subst_mono_cons with (B := T) in H2; eauto.
    eapply IHHinf in H2; eauto. lia.
  - dependent destruction HiuvA.
    eapply IHHinf in HiuvA1; eauto. lia.
  - dependent destruction HiuvA.
    eapply IHHinf in HiuvA2; eauto. lia.
  - dependent destruction HiuvA. dependent destruction HiuvC.
    eapply IHHinf1 in HiuvA1; eauto.
    eapply IHHinf2 in HiuvA2; eauto. lia.
Qed.

(* Lemma iuv_size_open_typ_wrt_typ_rec : forall A B n,
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
Qed.  *)

Lemma d_exp_split_size_det : forall Ψ e n1 n2,
  ⊢ᵈₜ Ψ -> d_exp_split_size Ψ e n1 -> d_exp_split_size Ψ e n2 -> n1 = n2.
Proof.
  intros * Hwf H1. generalize dependent n2.
  dependent induction H1; intros * H2; dependent destruction H2; auto;
  try solve [pick fresh X; inst_cofinites_with X; eapply H0 in H1; try rewrite H1; try lia; auto; auto].
  eapply binds_unique in H; eauto. dependent destruction H. auto.
  - admit.
  - admit.
  - admit.
  - admit. 
Admitted.

Lemma d_exp_split_size_rename_var : forall m e Ψ1 Ψ2 A x y n1 n2,
  size_exp e < m ->
  d_wf_tenv (Ψ2 ++ (x, dbind_typ A) :: Ψ1) ->
  d_wf_exp (Ψ2 ++ (x, dbind_typ A) :: Ψ1) e ->
  y `notin` dom (Ψ2 ++ (x, dbind_typ A) :: Ψ1) `union` fvar_in_exp e ->
  d_exp_split_size (Ψ2 ++ (x, dbind_typ A) :: Ψ1) e n1 ->
  d_exp_split_size (Ψ2 ++ (y, dbind_typ A) :: Ψ1) ({exp_var_f y ᵉ/ₑ x} e) n2 ->
  n1 = n2.
Proof.
  intro m. induction m; try lia.
  intros * Hlt Hwf_env Hwf_exp Hnotin Hes1 Hes2.
  eapply d_wf_tenv_rename_var in Hwf_env as Hwf_env'; eauto.
  dependent destruction Hwf_exp; simpl in *.
  - dependent destruction Hes1. dependent destruction Hes2. auto.
  - dependent destruction Hes1. destruct_eq_atom; dependent destruction Hes2.
    + apply binds_mid_eq in H0; auto.
      apply binds_mid_eq in H2; auto.
      dependent destruction H0. dependent destruction H2.
      admit. (* d_iuv_det *)
    + eapply binds_remove_mid in H0; eauto.
      eapply binds_remove_mid in H2; eauto.
      eapply binds_unique in H0; eauto.
      dependent destruction H0.
      admit. (* d_iuv_det *)
      eapply uniq_remove_mid with (F := (y, dbind_typ A) :: nil). auto.
  - dependent destruction Hes1. dependent destruction Hes2.
    pick fresh x'. inst_cofinites_with x'.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var in H2; auto.
    eapply IHm with (Ψ1 := Ψ1) (Ψ2 := x' ~ dbind_typ typ_bot ++ Ψ2) (y := y) (n2 := n0) in H1; auto.
    + rewrite size_exp_open_exp_wrt_exp_var. lia.
    + constructor; auto.
    + eapply d_wf_exp_var_binds_another_cons with (A1 := T); eauto.
    + simpl in *. admit. (* notin *)
  - dependent destruction Hes1. dependent destruction Hes2.
    eapply IHm in Hes1_1; eauto; try lia.
    eapply IHm in Hes1_2; eauto; try lia.
  - dependent destruction Hes1. dependent destruction Hes2.
    pick fresh X. inst_cofinites_with X.
    rewrite <- subst_exp_in_exp_open_exp_wrt_typ in H3; auto.
    assert (m0 = m1) by admit. subst. (* d_iuv_det *)
    eapply IHm with (Ψ1 := Ψ1) (Ψ2 := X ~ □ ++ Ψ2) (y := y) (n2 := n0) in H1; auto.
    + simpl in Hlt. rewrite size_exp_open_exp_wrt_typ_var. lia.
    + constructor; auto.
    + dependent destruction H0. simpl in *. auto.
    + admit. (* notin *)
  - dependent destruction Hes1. dependent destruction Hes2.
    eapply IHm in Hes1; eauto; try lia.
    admit. (* d_iuv_det *)
  - dependent destruction Hes1. dependent destruction Hes2.
    eapply IHm in Hes1; eauto; try lia.
Admitted.

Lemma d_exp_split_size_rename_var_cons : forall e Ψ A x y n1 n2,
  d_wf_tenv ((x, dbind_typ A) :: Ψ) ->
  d_wf_exp ((x, dbind_typ A) :: Ψ) e ->
  y `notin` dom ((x, dbind_typ A) :: Ψ) `union` fvar_in_exp e ->
  d_exp_split_size ((x, dbind_typ A) :: Ψ) e n1 ->
  d_exp_split_size ((y, dbind_typ A) :: Ψ) ({exp_var_f y ᵉ/ₑ x} e) n2 ->
  n1 = n2.
Proof.
  intros. eapply d_exp_split_size_rename_var with (y := y) (e := e) (Ψ2 := nil); eauto.
Qed.

Lemma d_exp_split_size_total_ : forall m Ψ e,
  size_exp e < m ->
  d_wf_exp Ψ e ->
  exists n, d_exp_split_size Ψ e n.
Proof.
  intro m. induction m; try lia.
  intros * Hlt Hwf.
  dependent destruction Hwf; eauto using d_exp_split_size.
  (* - pick fresh x. inst_cofinites_with x.
    apply d_wf_exp_var_binds_another_cons with (A2 := typ_bot) in H0; auto.
    eapply IHm in H0 as [n Hn]; eauto.
    exists n. eapply d_exp_split_size__abs; eauto.
    intros.
    admit. admit. (* TODO: renaming *)
  - simpl in Hlt.
    eapply IHm in Hwf1 as [n1 H1]; try lia.
    eapply IHm in Hwf2 as [n2 H2]; try lia.
    eauto using d_exp_split_size.
  - destruct body5.
    pick fresh X. inst_cofinites_with X.
    dependent destruction H0.
    eapply IHm in H1 as [n Hn]; eauto.
    exists ((1 + n) * (2 + iuv_size A)).
    eapply d_exp_split_size__tabs; eauto.
    intros.
    admit. admit. TODO: renaming *)
Admitted.

#[local] Hint Constructors d_exp_split_size : core.

Lemma d_exp_split_size_total : forall Ψ e,
  d_wf_exp Ψ e ->
  exists n, d_exp_split_size Ψ e n.
Proof.
  intros. induction H; eauto.
  -  admit.
  - admit.
  - destruct_conj; eauto.
  - admit.
  - admit.
Admitted.

Lemma d_iuv_size_rename_cons : forall Ψ X X0 A n,
  (* some additional conditions *)
  d_iuv_size (X ~ □ ++ Ψ) (A ᵗ^ₜ X) n ->
  d_iuv_size (X0 ~ □ ++ Ψ) (A ᵗ^ₜ X0) n.
Admitted.

Lemma num_occurs_in_typ_rename_cons : forall X X0 A n,
  (* some additional conditions *)
  num_occurs_in_typ X (A ᵗ^ₜ X) n ->
  num_occurs_in_typ X0 (A ᵗ^ₜ X0) n.
Admitted.

Lemma d_iuv_size_total : forall Ψ A,
  Ψ ᵗ⊢ᵈ A -> exists n, d_iuv_size Ψ A n.
Proof.
  intros * Hwf. dependent induction Hwf; eauto using d_iuv_size.
  - destruct IHHwf1 as [n1 IHHwf1]. destruct IHHwf2 as [n2 IHHwf2].
    eauto using d_iuv_size.
  - pick fresh X. inst_cofinites_with X.
    destruct H1 as [n H1].
    edestruct num_occurs_in_typ_total_d_wf_typ with (X := X) as [m H2] in H0; eauto.
    exists (n + m).
    inst_cofinites_for d_iuv_size__all.
    + intros X0 Hnin. eapply d_iuv_size_rename_cons; eauto.
    + intros X0 Hnin. eapply num_occurs_in_typ_rename_cons; eauto.
  - destruct IHHwf1 as [n1 IHHwf1].
    destruct IHHwf2 as [n2 IHHwf2].
    eauto using d_iuv_size.
  - destruct IHHwf1 as [n1 IHHwf1].
    destruct IHHwf2 as [n2 IHHwf2].
    eauto using d_iuv_size.
Qed.

Lemma d_iuv_size_open_typ_wrt_typ_cons : forall X Ψ A B n m1 m2,
  d_iuv_size Ψ (A ᵗ^^ₜ B) n ->
  d_iuv_size (X ~ □ ++ Ψ) (A ᵗ^ₜ X) m1 -> d_iuv_size Ψ B m2 ->
  n <= (1 + m1) * (2 + m2).
Admitted.

Lemma inftapp_iuv_size : forall Ψ A B C na nb nc,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  d_iuv_size Ψ A na ->
  d_iuv_size Ψ B nb ->
  d_iuv_size Ψ C nc ->
  nc <= (1 + na) * (2 + nb).
Proof.
  intros.
  generalize dependent nc.
  generalize dependent nb.
  generalize dependent na. induction H; intros.
  - dependent destruction H3. lia.
  - dependent destruction H2.
    pick fresh X. inst_cofinites_with X.
    eapply d_iuv_size_open_typ_wrt_typ_cons with (n := nc) (m1 := n) (m2 := nb) in H5; eauto. lia.
  - dependent destruction H1.
    eapply IHd_inftapp in H1_; eauto. lia.
  - dependent destruction H1.
    eapply IHd_inftapp in H1_0; eauto. lia.
  - dependent destruction H1.
    dependent destruction H3.
    eapply IHd_inftapp1 in H1_; eauto.
    eapply IHd_inftapp2 in H1_0; eauto. lia.
Qed. 

Lemma inf_iuv_size_d_exp_split_size : forall Ω A e n m,
  ⊢ᵈʷₛ Ω ->
  ⌊ Ω ⌋ᵈ ⊢ e ⇒ A ->
  d_exp_split_size (dwl_to_denv Ω) e n ->
  d_iuv_size (dwl_to_denv Ω) A m ->
  m <= n.
Proof.
  intros * Hwf Hinf. generalize dependent n. generalize dependent m.
  dependent induction Hinf; intros * Hes Hiuv;
    dependent destruction Hes; simpl; auto; try lia.
  - eapply binds_unique in H0; eauto.
    dependent destruction H0.
    eapply d_iuv_size_det in H2; eauto. lia.
  - eapply d_iuv_size_det with (n2 := m) in H0; auto. lia.
  - dependent destruction Hiuv. auto.
  - eapply d_chk_inf_wf in Hinf1.
    destruct Hinf1 as [Hwf1 [Hwf2 Hwf3]].
    eapply d_iuv_size_total in Hwf2 as HiuvA.
    destruct HiuvA as [n HiuvA].
    apply infabs_d_iuv_size_C with (n := n) (m := m) in H; auto.
    apply IHHinf1 with (m := n) in Hes1; auto. lia.
  - dependent destruction H. dependent destruction Hiuv.
    eapply d_iuv_size_d_mono in H.
    eapply d_iuv_size_d_mono in H0.
    eapply d_iuv_size_det in H; eauto.
    eapply d_iuv_size_det in H0; eauto. lia.
  - eapply d_iuv_size_det in H3; eauto. lia.
  - eapply d_chk_inf_wf in Hinf.
    destruct Hinf as [Hwf1 [Hwf2 Hwf3]].
    eapply d_iuv_size_total in Hwf2 as HiuvA.
    destruct HiuvA as [na HiuvA].
    apply inftapp_iuv_size with (na := na) (nb := m0) (nc := m) in H0; auto.
    eapply IHHinf with (m := na) in Hes; auto.
    replace (S (S (m0 + n * S (S m0)))) with ((1 + n) * (2 + m0)) by lia.
    apply le_trans with (m := (1 + na) * (2 + m0)); auto.
    eapply mult_le_compat_r. lia.
Qed.

Lemma d_iuv_size_close : forall A Ψ X n,
  d_iuv_size (X ~ □ ++ Ψ) (A ᵗ^ₜ X) n -> d_iuv_size Ψ A n .
(* change the lemma and its name to whatever you like *)
Admitted.

Lemma iu_size_le_d_iuv_size : forall A Ψ n,
  d_iuv_size Ψ A n -> iu_size A <= n.
Proof.
  intro A. induction A; intros * Hiuv; simpl; try lia.
  - dependent destruction Hiuv.
    eapply IHA1 in Hiuv1. eapply IHA2 in Hiuv2. lia.
  - dependent destruction Hiuv.
    pick fresh X. inst_cofinites_with X.
    eapply d_iuv_size_close in H.
    eapply IHA in H. lia.
  - dependent destruction Hiuv.
    eapply IHA1 in Hiuv1. eapply IHA2 in Hiuv2. lia.
  - dependent destruction Hiuv.
    eapply IHA1 in Hiuv1. eapply IHA2 in Hiuv2. lia.
Qed.

Lemma d_wl_red_chk_inf_complete: forall Ω e A mode,
  d_chk_inf (dwl_to_denv Ω) e mode A -> 
  match mode with 
  | typingmode__chk => ⊢ᵈʷₛ (work_check e A ⫤ᵈ Ω) -> Ω ⟶ᵈʷ⁎⋅ -> (work_check e A ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅
  | typingmode__inf => forall c, ⊢ᵈʷₛ (work_infer e c ⫤ᵈ Ω) -> (work_applys c A ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅ -> (work_infer e c ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅
  end.
Proof with auto.
  intros. dependent induction H; intros; eauto...
  - econstructor. 
    eapply IHd_chk_inf; eauto.
    destruct_d_wf_wl...
  - destruct (d_exp_split_size_total (⌊ Ω ⌋ᵈ) e1) as [n Hn]. eapply d_chk_inf_wf; eauto.
    econstructor; eauto.
    destruct_d_wf_wl.
    eapply IHd_chk_inf1; eauto 7...
    apply d_wl_red__applys with (w:=work_infabs A (contd_infapp n e2 c)); eauto.
    econstructor. simpl.
    apply d_infabs_d_wf in H0 as Hwft. intuition.
    eapply d_wl_red_infabs_complete; eauto.
    econstructor... econstructor...
    eapply d_iuv_size_total in H8.
    eapply d_iuv_size_total in H7.
    destruct H8 as [na HiuvA].
    destruct H7 as [nb HiuvB].
    eapply inf_iuv_size_d_exp_split_size in HiuvA as Hle; eauto.
    eapply infabs_d_iuv_size_B with (n := na) (m := nb) in H0 as Hle2; eauto.
    eapply iu_size_le_d_iuv_size in HiuvB. lia.
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
    repeat constructor; simpl; auto.
    admit. (* wf *)
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
Admitted.


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
