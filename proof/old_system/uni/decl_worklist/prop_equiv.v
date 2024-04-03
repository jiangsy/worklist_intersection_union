Require Import Coq.Program.Equality.
Require Import Coq.Unicode.Utf8.

Require Import ln_utils.
Require Import uni.decl.def_extra.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_typing.
Require Import uni.def_ott.
Require Import uni.notations.
Require Import uni.decl_worklist.def.


(* Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dworklist.
Bind Scope dworklist_scope with dworklist.
 *)


Ltac destruct_wf :=
  repeat
    match goal with
    | H : d_wf_wl (dworklist_conswork ?Ω ?w) |- _ => dependent destruction H
    | H : d_wf_wl (dworklist_consvar ?Ω ?w ?b) |- _ => dependent destruction H
    | H : d_wf_wl (dworklist_constvar ?Ω ?w ?b) |- _ => dependent destruction H
    | H : d_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : d_wf_typ ?E (?Ct ?A1 ?A2) |- _ => dependent destruction H
    | H : d_wf_exp ?E (?Ce ?b) |- _ => dependent destruction H
    | H : d_wf_exp ?E (?Ce ?e1 ?e2) |- _ => dependent destruction H
    end.


Lemma d_wf_wl_wf_env : forall Ω,
  ⊢ᵈʷ Ω -> ⊢ (dwl_to_denv Ω).
Proof.
  intros. induction H; simpl; auto; econstructor; auto.
Qed.

Inductive d_all_work : dworklist -> Prop :=
  | d_all_work__empty : d_all_work dworklist_empty
  | d_all_work__conswork : forall Ω w,
      d_all_work Ω -> d_all_work (dworklist_conswork Ω w).

Lemma dwl_app_cons_work: forall Ω1 Ω2 w,
  dworklist_conswork (dwl_app Ω2 Ω1) w =(dwl_app (dworklist_conswork Ω2 w) Ω1).
Proof.
  intros. auto.
Qed.

Lemma dwl_app_cons_tvar: forall Ω1 Ω2 X b,
  dworklist_constvar (dwl_app Ω2 Ω1) X b =(dwl_app (dworklist_constvar Ω2 X b) Ω1).
Proof.
  intros. auto.
Qed.

Lemma dwl_app_cons_var: forall Ω1 Ω2 x b,
  dworklist_consvar (dwl_app Ω2 Ω1) x b =(dwl_app (dworklist_consvar Ω2 x b) Ω1).
Proof.
  intros. auto.
Qed.

Ltac rewrite_dwl_app :=
  repeat
    match goal with
    | _ : _ |- context [dworklist_consvar  (dwl_app ?Ω2 ?Ω1) ?X ?b] => rewrite dwl_app_cons_var
    | _ : _ |- context [dworklist_constvar (dwl_app ?Ω2 ?Ω1) ?X ?b] => rewrite dwl_app_cons_tvar
    | _ : _ |- context [dworklist_conswork (dwl_app ?Ω2 ?Ω1) ?w] => rewrite dwl_app_cons_work
    end.

Lemma d_wl_app_cons_work_same_env : forall Ω1 Ω2 w,
    dwl_to_denv (dwl_app Ω2 (w ⫤ᵈ Ω1)) = dwl_to_denv (dwl_app Ω2 Ω1).
  Proof.
    intros. induction Ω2; simpl; auto.
    rewrite IHΩ2. auto.
    rewrite IHΩ2. auto.
  Qed.

Ltac inv_all_work := 
  match goal with
  | H : d_all_work (dworklist_consvar ?Ω ?x ?b) |- _ => inversion H
  | H : d_all_work (dworklist_constvar ?Ω ?X ?b) |- _ => inversion H
  end.

Ltac destruct_all_work := 
  match goal with
  | H : d_all_work (dworklist_conswork ?Ω ?w) |- _ => dependent destruction H
  end.

#[local] Hint Constructors d_all_work : core.

Lemma d_wl_app_all_work_same_env : forall Ω1 Ω2 Ω3,
  d_all_work Ω2 ->
  dwl_to_denv (dwl_app Ω3 (dwl_app Ω2 Ω1)) = dwl_to_denv (dwl_app Ω3 Ω1).
Admitted.

Ltac solve_Ω1 IH :=
  match goal with 
  | H : ?Ω1 = ?Ω2 |- d_wl_del_red ?Ω => 
      dependent destruction H; replace Ω with (dwl_app dworklist_empty Ω) by auto; eapply IH;
      simpl; rewrite_dwl_app; eauto
  end.


Lemma d_wl_red_weaken_works : forall Ω1 Ω2 Ω3,
  (dwl_app Ω3 (dwl_app Ω2 Ω1)) ⟶ᵈ⁎⋅ -> d_all_work Ω2 -> (dwl_app Ω3 Ω1) ⟶ᵈ⁎⋅.
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
  replace (w1 ⫤ᵈ Ω1)%dworklist with ((dwl_app dworklist_empty (w1 ⫤ᵈ Ω1))) by auto.
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
  ⊢ᵈʷ Ω -> d_wf_conts (dwl_to_denv Ω) c -> dwl_to_denv Ω ⊢ A -> apply_conts c A w ->
  ⊢ᵈʷ dworklist_conswork Ω w.
Proof.
  intros. induction H2; simpl; auto;
    dependent destruction H0; auto.
Qed.

Theorem d_wf_work_apply_contd : forall Ω cc A B w,
  ⊢ᵈʷ Ω -> 
  d_wf_contd (dwl_to_denv Ω) cc -> 
  dwl_to_denv Ω ⊢ A -> 
  dwl_to_denv Ω ⊢ B -> 
  apply_contd cc A B w ->
  ⊢ᵈʷ dworklist_conswork Ω w.
Proof.
  intros. induction H3; simpl; auto;
    dependent destruction H0; auto.
Qed.

(* Ltac destruct_d_wl_del_red' := 
  match goal with
  | H : d_wl_del_red (dworklist_conswork ?Ω ?w) |- _ => 
    lazymatch w with 
    | work_apply (?c ?B) ?A => dependent destruction H
    | work_apply ?c ?A => fail
    | ?w1 _ _ => dependent destruction H
    | ?w1 _ _ _ => dependent destruction H
    end
  | H : d_wl_del_red (dworklist_consvar ?Ω ?x ?A) |- _ => 
    dependent destruction H
  | H : d_wl_del_red (dworklist_constvar ?Ω ?x ?b) |- _ => 
    dependent destruction H
  | H : apply_cont ?c ?A ?w |- _ => dependent destruction H
  (* | H : apply_cont2 ?cc ?A ?B ?w |- _ => dependent destruction H *)
  end. *)

Ltac destruct_d_wl_del_red' := 
  match goal with
  | H : d_wl_del_red (dworklist_conswork ?Ω ?w) |- _ => 
    lazymatch w with 
    | work_applys (?c ?B) ?A => dependent destruction H
    | work_applys ?c ?A => fail
    | ?w1 _ _ => dependent destruction H
    | ?w1 _ _ _ => dependent destruction H
    end
  | H : d_wl_del_red (dworklist_consvar ?Ω ?x ?A) |- _ => 
    dependent destruction H
  | H : d_wl_del_red (dworklist_constvar ?Ω ?x ?b) |- _ => 
    dependent destruction H
  | H : apply_conts ?c ?A ?w |- _ => dependent destruction H
  | H : apply_contd (?cc _) ?A ?B ?w |- _ => dependent destruction H
  | H : apply_contd (?cc _ _) ?A ?B ?w |- _ => dependent destruction H
  end.

Ltac destruct_d_wl_del_red := repeat destruct_d_wl_del_red'.

Ltac _apply_IH_d_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵈʷ ?Ω) -> (?Ω ⟶ᵈ⁎⋅) |- _ => destruct_wf; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵈʷ Ω) by auto;
      apply H in H1
    end.
(* 
(* remove later *)
Hint Constructors d_chk_inf : typing. *)

#[local] Hint Immediate d_wf_wl_wf_env : core.

(* This direction is not so important because soundness is proven against decl system directly *)
Theorem d_wl_red_sound: forall Ω, 
    ⊢ᵈʷ Ω -> Ω ⟶ᵈʷ⁎⋅ -> Ω ⟶ᵈ⁎⋅.
Proof with eauto with typing.
  intros. induction H0; try solve [dependent destruction H; auto];
    try solve [destruct_wf; _apply_IH_d_wl_red; destruct_d_wl_del_red; eauto].
  (* sub *)

  - destruct_wf. dependent destruction H. dependent destruction H1.
    constructor.
    eapply d_sub__all with (L:=L `union` L0 `union` L1 `union` dom (dwl_to_denv Ω)); intros; auto.
    inst_cofinites_with X.
    assert ( d_wf_wl  (dworklist_conswork (dworklist_consvar Ω X dbind_stvar_empty) (work_sub (A ^ᵗ X) (B ^ᵗ X)) ) ).
    admit.
    admit.
    admit.
  - admit.
  - admit.
  - destruct_wf. econstructor.
    apply d_chk_inf__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x...
    assert (⊢ᵈʷ (work_check (e ^ᵉₑ exp_var_f x) typ_top ⫤ᵈ x ~ᵈ typ_bot;ᵈ Ω)).
    { repeat constructor... admit. }
    apply H4 in H6. dependent destruction H6...
    inst_cofinites_by (L `union` L0 `union` dom (dwl_to_denv Ω)). 
    assert (⊢ᵈʷ (work_check (e ^ᵉₑ exp_var_f x) typ_top ⫤ᵈ x ~ᵈ typ_bot;ᵈ Ω)).
    { repeat constructor... admit. }
    apply H4 in H5. dependent destruction H5...  dependent destruction H6...
  - eapply d_wl_del_red__inf with (A:=A)...
    econstructor... destruct_wf...
    apply IHd_wl_red. admit.
  - admit.
  - admit.
  - destruct_wf. _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    eapply d_wl_del_red__inf with (A:=B).
    + econstructor; eauto. dependent destruction H7.
      apply d_wl_red_weaken_work1 in H7. inversion H7... 
    + eapply d_wl_red_weaken_work2; eauto.
  - admit.
  - destruct_wf. 
    assert (⊢ᵈʷ (work_infabs (A ^^ᵗ T) cd ⫤ᵈ Ω)).
    { repeat constructor... apply d_wft_all_open... apply d_mono_typ_d_wf_typ... }
    apply IHd_wl_red in H4. dependent destruction H4.
    eapply d_wl_del_red__infabs with (B:=B) (C:=C); eauto.
    eapply d_infabs__all with (T:=T)...
    apply d_mono_typ_d_wf_typ; eauto.
  - econstructor; eauto.
    destruct_wf.
    eapply d_wf_work_apply_conts in H0; eauto.
  - econstructor; eauto.
    destruct_wf.
    eapply d_wf_work_apply_contd with (A:=A) in H0; eauto.
Admitted.


Lemma d_wl_red_sub_complete: forall Ω A B,
  dwl_to_denv Ω ⊢ A <: B -> ⊢ᵈʷ (work_sub A B ⫤ᵈ Ω) -> 
  Ω ⟶ᵈʷ⁎⋅ -> (work_sub A B ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅.
Proof with auto.
  intros * Hsub Hwfwl Hred.
  dependent induction Hsub; 
  try solve [destruct_wf; econstructor; auto].
  - destruct_wf. 
    eapply d_wl_red__sub_all with (L:=L `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with SX.
    apply H2; eauto...
    inst_cofinites_with X.
    apply d_sub_dwft in H1; intuition.
  - destruct_wf. 
    eapply d_wl_red__sub_alll with (T:=T); eauto. 
    apply IHHsub; eauto. 
    econstructor; auto. econstructor; auto.
    apply d_wft_all_open; eauto; auto.
    eapply d_mono_typ_d_wf_typ; auto.
Qed.


Lemma d_wl_app_assoc : forall Ω1 Ω2 Ω3,
  dwl_app Ω3 (dwl_app Ω2 Ω1) = dwl_app (dwl_app Ω3 Ω2) Ω1.
Proof.
  induction Ω3; auto.
  - simpl. rewrite <- IHΩ3. auto.
  - simpl. rewrite <- IHΩ3. auto.
  - simpl. rewrite <- IHΩ3. auto.
Qed.

Lemma d_wl_red_weaken: forall Ω1 Ω2,
  (dwl_app Ω2 Ω1) ⟶ᵈʷ⁎⋅ -> Ω1 ⟶ᵈʷ⁎⋅ .
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
  replace (w ⫤ᵈ Ω)%dworklist with (dwl_app (dworklist_conswork dworklist_empty w) Ω) in H by auto.
  eapply d_wl_red_weaken. eauto.
Qed.


Lemma d_wl_red_strengthen_work : forall Ω1 Ω2 w,
  (w ⫤ᵈ Ω1) ⟶ᵈʷ⁎⋅ -> (dwl_app Ω2 Ω1) ⟶ᵈʷ⁎⋅ -> (dwl_app Ω2 (w ⫤ᵈ Ω1)) ⟶ᵈʷ⁎⋅ .
Proof. 
  intros. dependent induction H0; 
      try destruct Ω2; simpl in x; try solve [inversion x]; dependent destruction x; simpl; eauto;
      try solve [econstructor; rewrite_dwl_app; auto].
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
  - eapply d_wl_red__infabs_all with (T:=T).
    rewrite d_wl_app_cons_work_same_env. auto.
    rewrite_dwl_app. auto.
  - econstructor; eauto.
    rewrite_dwl_app. auto.
  - econstructor; eauto.
    rewrite_dwl_app. auto.
Qed.


Lemma d_wl_red_infabs_complete: forall Ω A B C cc,
   dwl_to_denv Ω ⊢ A ▹ B → C -> d_wf_wl (dworklist_conswork Ω (work_infabs A cc)) -> 
   d_wl_red (dworklist_conswork Ω (work_applyd cc B C)) -> d_wl_red (dworklist_conswork Ω (work_infabs A cc)).
Proof with auto.
  intros. generalize dependent cc. dependent induction H; intros; eauto;
  try solve [destruct_wf; econstructor; auto].
  - destruct_wf.
    eapply d_wl_red__infabs_all with (T:=T); eauto.
  - destruct_wf.
    apply d_infabs_wft in H.
    apply d_wl_red__infabs_union.
    apply IHd_infabs1; auto.
    eapply d_wl_red__applyd with 
      (w:=((work_infabsunion B1 C1 A2 cc))).
    eapply apply_contd__infabsunion.
    simpl.
    eapply d_wl_red__infabsunion.
    apply IHd_infabs2; intuition.
    eapply d_wl_red__applyd with 
      (w:=(work_unioninfabs  B1 C1 B2 C2 cc)).
    econstructor.
    simpl.
    econstructor.
    auto.  
Qed.


Lemma d_wl_red_inftapp_complete: forall Ω A B C c,
  dwl_to_denv Ω ⊢ A ○ B ⇒⇒ C -> d_wf_wl (dworklist_conswork Ω (work_inftapp A B c)) ->
  d_wl_red (dworklist_conswork Ω (work_applys c C)) -> d_wl_red (dworklist_conswork Ω (work_inftapp A B c)).
Proof with auto.
  intros. generalize dependent c. dependent induction H; intros; eauto;
  try solve [destruct_wf; econstructor; eauto].
  - apply d_inftapp_wft in H.
    destruct_wf.
    econstructor.
    eapply IHd_inftapp1...
    eapply d_wl_red__applys with (w:=work_inftappunion C1 A2 B c).
    econstructor.
    simpl.
    econstructor. 
    eapply IHd_inftapp2... intuition.
    eapply d_wl_red__applys with (w:=work_unioninftapp C1 C2 c).
    eapply apply_conts__unioninftapp...
    econstructor...
Qed.


Lemma d_wl_red_chk_inf_complete: forall Ω e A mode,
  d_chk_inf (dwl_to_denv Ω) e mode A -> 
  match mode with 
  | typingmode__chk => ⊢ᵈʷ (work_check e A ⫤ᵈ Ω) -> Ω ⟶ᵈʷ⁎⋅ -> (work_check e A ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅
  | typingmode__inf => forall c, ⊢ᵈʷ (work_infer e c ⫤ᵈ Ω) -> (work_applys c A ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅ -> (work_infer e c ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅
  end.
Proof with auto.
  intros. dependent induction H; intros; eauto...
  (* - econstructor; eauto. *)
  - econstructor. 
    eapply IHd_chk_inf; eauto.
    destruct_wf...
  - econstructor.
    destruct_wf.
    eapply IHd_chk_inf1; eauto.
    apply d_wl_red__applys with (w:=work_infabs A (contd_infapp e2 c)); eauto.
    econstructor. simpl.
    apply d_infabs_wft in H0 as Hwft. intuition.
    eapply d_wl_red_infabs_complete; eauto.
    econstructor... econstructor... econstructor.
    assert ((work_check e2 B ⫤ᵈ Ω) ⟶ᵈʷ⁎⋅).
      apply IHd_chk_inf2; auto.
      apply d_wl_red_weaken_consw in H5; auto.
    replace (work_applys c C ⫤ᵈ work_check e2 B ⫤ᵈ Ω)%dworklist with (dwl_app (work_applys c C ⫤ᵈ dworklist_empty) (work_check e2 B ⫤ᵈ Ω)%dworklist) by auto.
    apply d_wl_red_strengthen_work; eauto.
  - destruct_wf.
    eapply d_wl_red__inf_abs_mono with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)); eauto.
    intros. inst_cofinites_with x.
    apply H1...   
    apply d_mono_typ_d_wf_typ in H. dependent destruction H.
    repeat constructor; simpl...
    eapply d_wf_exp_var_binds_another_cons; eauto.
    apply d_wf_typ_weaken_cons...
  - destruct_wf. 
    eapply d_wl_red__inf_tabs with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)); eauto. 
    intros. inst_cofinites_with X. dependent destruction H2.
    apply H1; auto.
  - destruct_wf.
    apply d_chk_inf_wft in H0.
    econstructor.
    apply IHd_chk_inf; auto...
    apply d_wl_red__applys with (w:=(work_inftapp A B c)); eauto.
    econstructor.
    simpl.
    eapply d_wl_red_inftapp_complete; eauto.
  - destruct_wf.
    eapply d_wl_red__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H0... econstructor... econstructor... simpl. auto.
    simpl.
    rewrite_env ((x ~ dbind_typ typ_bot) ++ dwl_to_denv Ω).
    eapply d_wf_exp_var_binds_another_cons; eauto.
  - destruct_wf.
    eapply d_wl_red__chk_absarrow with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H1... 
    econstructor; econstructor; eauto.
    eapply d_wf_exp_var_binds_another_cons; eauto.
    simpl. apply d_wf_typ_weaken_cons...
  - destruct_wf. econstructor. 
    apply IHd_chk_inf; auto...
    eapply d_wl_red__applys with (w:=(work_sub B A)); eauto.
    constructor; auto. simpl.
    apply d_wl_red_sub_complete; auto.
    apply d_chk_inf_wft in H. auto.
  - destruct_wf. eapply d_wl_red__chk_inter...
  - destruct_wf. eauto...
  - destruct_wf. eauto... 
Qed.


Theorem d_wl_red_complete: forall Ω, 
    ⊢ᵈʷ Ω -> Ω ⟶ᵈ⁎⋅ -> Ω ⟶ᵈʷ⁎⋅.
Proof with auto.
  intros. induction H0; auto;
  try solve [destruct_wf; econstructor; eauto].
  - destruct_wf. refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _); auto...
  - destruct_wf.
    refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _ _); auto...
    apply d_chk_inf_wft in H2.
    apply IHd_wl_del_red. auto.
  - destruct_wf. eapply d_wl_red_infabs_complete; eauto...
  - destruct_wf. 
    apply d_wl_red__infabsunion.
    eapply d_wl_red_infabs_complete; eauto.
    eapply d_wl_red__applyd with (w:=(work_unioninfabs B1 C1 B2 C2 cd)).
    apply apply_contd__unioninfabs.
    simpl. econstructor.
    apply d_infabs_wft in H4. 
    apply IHd_wl_del_red. intuition.
  - destruct_wf.
    econstructor. apply IHd_wl_del_red...
  - destruct_wf.
    apply d_wl_red__infapp. 
    apply IHd_wl_del_red...
  - destruct_wf. eapply d_wl_red_inftapp_complete; eauto.
  - destruct_wf. econstructor. 
    eapply d_wl_red_inftapp_complete; eauto...
    eapply d_wl_red__applys with (w:=(work_unioninftapp C1 C2 cs))...
    econstructor. simpl.
    apply d_inftapp_wft in H4.
    econstructor. intuition.
  - destruct_wf. apply d_wl_red_sub_complete; eauto.
  - destruct_wf. econstructor; eauto.
    apply IHd_wl_del_red. eapply d_wf_work_apply_conts; eauto.
  - destruct_wf. econstructor; eauto.
    apply IHd_wl_del_red. eapply d_wf_work_apply_contd in H3; eauto.
Qed.


Print Assumptions  d_wl_red_complete.