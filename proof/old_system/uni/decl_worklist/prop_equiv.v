Require Import Coq.Program.Equality.
Require Import Coq.Unicode.Utf8.

Require Import ln_utils.
Require Import uni.decl.def_extra.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_typing.
Require Import uni.def_ott.
Require Import uni.notations.
Require Import uni.decl_worklist.def.


Hint Constructors d_wl_red : Hdb_dworklist_equiv.
Hint Constructors d_wf_wl : Hdb_dworklist_equiv.
Hint Constructors d_wl_del_red : Hdb_dworklist_equiv.


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
    dwl_to_denv (dwl_app Ω2 (w ⫤ Ω1)) = dwl_to_denv (dwl_app Ω2 Ω1).
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

Hint Constructors d_all_work : Hdb_dworklist_equiv.

Lemma d_wl_app_all_work_same_env : forall Ω1 Ω2 Ω3,
  d_all_work Ω2 ->
  dwl_to_denv (dwl_app Ω3 (dwl_app Ω2 Ω1)) = dwl_to_denv (dwl_app Ω3 Ω1).
Admitted.

Ltac solve_Ω1 IH :=
  match goal with 
  | H : ?Ω1 = ?Ω2 |- d_wl_del_red ?Ω => 
      dependent destruction H; replace Ω with (dwl_app dworklist_empty Ω) by auto; eapply IH;
      simpl; rewrite_dwl_app; eauto with Hdb_dworklist_equiv
  end.


Lemma d_wl_red_weaken_works : forall Ω1 Ω2 Ω3,
  (dwl_app Ω3 (dwl_app Ω2 Ω1)) ⟶ᵈ⁎⋅ -> d_all_work Ω2 -> (dwl_app Ω3 Ω1) ⟶ᵈ⁎⋅.
Proof with auto with Hdb_dworklist_equiv.
  intros * Hred Haw. dependent induction Hred;
    try destruct Ω3; simpl in x; try solve [inversion x]; dependent destruction x; simpl;
    destruct Ω2; simpl in *; 
      try solve [inversion x]; 
      try solve [dependent destruction x; eauto with Hdb_dworklist_equiv];
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
  (w2 ⫤ (w1 ⫤ Ω1)) ⟶ᵈ⁎⋅ ->  (w1 ⫤ Ω1) ⟶ᵈ⁎⋅.
Proof with auto with Hdb_dworklist_equiv.
  intros.  
  replace (w1 ⫤ Ω1)%dworklist with ((dwl_app dworklist_empty (w1 ⫤ Ω1))) by auto.
  eapply d_wl_red_weaken_works with (Ω2:=(w2 ⫤ dworklist_empty)%dworklist)...
Qed.

Lemma d_wl_red_weaken_work2 : forall Ω1 w1 w2,
  (w2 ⫤ (w1 ⫤ Ω1)) ⟶ᵈ⁎⋅ ->  (w2 ⫤ Ω1) ⟶ᵈ⁎⋅.
Proof with auto with Hdb_dworklist_equiv.
  intros.  
  replace (w2 ⫤ Ω1)%dworklist with ((dwl_app (w2 ⫤ dworklist_empty) (Ω1))) by auto.
  eapply d_wl_red_weaken_works with (Ω2:=(w1 ⫤ dworklist_empty)%dworklist)...
Qed.


Hint Resolve d_wf_wl_wf_env : Hdb_dworklist_equiv.


Theorem d_wf_work_apply_cont : forall Ω c A1 w,
  ⊢ᵈʷ Ω -> d_wf_cont (dwl_to_denv Ω) c -> dwl_to_denv Ω ⊢ A1 -> apply_cont c A1 w ->
  ⊢ᵈʷ dworklist_conswork Ω w.
Proof.
  intros. induction H2; simpl; auto;
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
  | H : apply_cont2 (?cc _) ?A ?B ?w |- _ => dependent destruction H
  | H : apply_cont2 (?cc _ _) ?A ?B ?w |- _ => dependent destruction H
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
Hint Constructors d_typing : typing. *)

(* This direction is not so important because soundness is proven against decl system directly *)
Theorem d_wl_red_sound: forall Ω, 
    ⊢ᵈʷ Ω -> Ω ⟶ᵈʷ⁎⋅ -> Ω ⟶ᵈ⁎⋅.
Proof with eauto with Hdb_dworklist_equiv typing.
  intros. induction H0; try solve [dependent destruction H; auto with Hdb_dworklist_equiv];
    try solve [destruct_wf; _apply_IH_d_wl_red; destruct_d_wl_del_red; eauto with Hdb_dworklist_equiv].
  (* sub *)

  - destruct_wf. econstructor.
    dependent destruction H. dependent destruction H1.
    eapply d_sub__all with (L:=L `union` L0 `union` L1 `union` dom (dwl_to_denv Ω)); intros; auto.
    inst_cofinites_with X.
    assert ( d_wf_wl  (dworklist_conswork (dworklist_consvar Ω X dbind_stvar_empty) (work_sub (A ^ᵗ X) (B ^ᵗ X)) ) ).
    admit.
    admit.
    admit.
  - admit.
  - admit.
  - econstructor.
    eapply d_typing__chk_abstop with (L:=L).
    intros. inst_cofinites_with x...
    admit. admit.
  - eapply d_wl_del_red__inf with (T1:=A)...
    econstructor... admit.
    apply IHd_wl_red. admit.
  - admit.
  - admit.
  - destruct_wf. _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    admit.
  - admit.
  - destruct_wf.
    econstructor...
    econstructor...
  - admit.
  - admit.
  - admit.
  - destruct_wf.
    econstructor...
  - destruct_wf.
    econstructor...
  - admit.
  - _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    eapply d_wl_del_red__infabs with (B:=B) (C:=C)...
  - destruct_wf. 
    _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    eapply d_wl_del_red__infabs with (B:=B) (C:=C)...
  - _apply_IH_d_wl_red.
    destruct_d_wl_del_red.
    eapply d_wl_del_red__infabs with (B:=typ_intersection B1 B2) (C:=typ_union C1 C2)...
  - assert (⊢ᵈʷ (work_infabs A (contd_unioninfabs B C cc) ⫤ Ω)) by admit.
    apply IHd_wl_red in H1.
    destruct_d_wl_del_red...  
  - econstructor; eauto.
    destruct_wf.
    eapply d_wf_work_apply_cont in H0; eauto.
  - admit.
Admitted.


Lemma d_wl_red_sub_complete: forall Ω A B,
  dwl_to_denv Ω ⊢ A <: B -> ⊢ᵈʷ (work_sub A B ⫤ Ω) -> 
  Ω ⟶ᵈʷ⁎⋅ -> (work_sub A B ⫤ Ω) ⟶ᵈʷ⁎⋅.
Proof with auto with Hdb_dworklist_equiv.
  intros * Hsub Hwfwl Hred.
  dependent induction Hsub; 
  try solve [destruct_wf; econstructor; auto with Hdb_dworklist_equiv].
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
    eapply d_sub_dwft; eauto.
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
    try solve [inversion x]; dependent destruction x; simpl; eauto with Hdb_dworklist_equiv;
    try solve [eapply IHd_wl_red; rewrite_dwl_app; eauto].
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
Qed.

Corollary d_wl_red_weaken_consw : forall Ω w,
  (w ⫤ Ω) ⟶ᵈʷ⁎⋅ -> Ω ⟶ᵈʷ⁎⋅ .
Proof.
  intros.
  replace (w ⫤ Ω)%dworklist with (dwl_app (dworklist_conswork dworklist_empty w) Ω) in H by auto.
  eapply d_wl_red_weaken. eauto.
Qed.


Lemma d_wl_red_strengthen_work : forall Ω1 Ω2 w,
  (w ⫤ Ω1) ⟶ᵈʷ⁎⋅ -> (dwl_app Ω2 Ω1) ⟶ᵈʷ⁎⋅ -> (dwl_app Ω2 (w ⫤ Ω1)) ⟶ᵈʷ⁎⋅ .
Proof. 
  intros. dependent induction H0; 
      try destruct Ω2; simpl in x; try solve [inversion x]; dependent destruction x; simpl; eauto with Hdb_dworklist_equiv;
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
  - eapply d_wl_red__inf_abs_mono with (T1:=T1) (T2:=T2); auto.
    rewrite d_wl_app_cons_work_same_env. auto.
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
   d_wl_red (dworklist_conswork Ω (work_apply2 cc B C)) -> d_wl_red (dworklist_conswork Ω (work_infabs A cc)).
Proof with auto with Hdb_dworklist_equiv.
  intros. generalize dependent cc. dependent induction H; intros; eauto;
  try solve [destruct_wf; econstructor; auto with Hdb_dworklist_equiv].
  - destruct_wf.
    eapply d_wl_red__infabs_all with (T:=T); eauto.
  - destruct_wf.
    apply d_infabs_wft in H.
    apply d_wl_red__infabs_union.
    apply IHd_infabs1; auto.
    eapply d_wl_red__apply_cont2 with 
      (w:=((work_infabsunion B1 C1 A2 cc))).
    eapply apply_cont2__infabsunion.
    simpl.
    eapply d_wl_red__infabsunion.
    apply IHd_infabs2; intuition.
    eapply d_wl_red__apply_cont2 with 
      (w:=(work_unioninfabs  B1 C1 B2 C2 cc)).
    econstructor.
    simpl.
    econstructor.
    auto.  
Qed.


Lemma d_wl_red_inftapp_complete: forall Ω A B C c,
  dwl_to_denv Ω ⊢ A ○ B ⇒⇒ C -> d_wf_wl (dworklist_conswork Ω (work_inftapp A B c)) ->
  d_wl_red (dworklist_conswork Ω (work_apply c C)) -> d_wl_red (dworklist_conswork Ω (work_inftapp A B c)).
Proof with auto with Hdb_dworklist_equiv.
  intros. generalize dependent c. dependent induction H; intros; eauto;
  try solve [destruct_wf; econstructor; eauto with Hdb_dworklist_equiv].
  - apply d_inftapp_wft in H.
    destruct_wf.
    econstructor.
    eapply IHd_inftapp1...
    eapply d_wl_red__applycont with (w:=work_inftappunion C1 A2 B c).
    econstructor.
    simpl.
    econstructor. 
    eapply IHd_inftapp2... intuition.
    eapply d_wl_red__applycont with (w:=work_unioninftapp C1 C2 c).
    eapply applycont__unioninftapp...
    econstructor...
Qed.


Lemma d_wl_red_chk_inf_complete: forall Ω e A mode,
  d_typing (dwl_to_denv Ω) e mode A -> 
  match mode with 
  | typingmode__chk => ⊢ᵈʷ (work_check e A ⫤ Ω) -> Ω ⟶ᵈʷ⁎⋅ -> (work_check e A ⫤ Ω) ⟶ᵈʷ⁎⋅
  | typingmode__inf => forall c, ⊢ᵈʷ (work_infer e c ⫤ Ω) -> (work_apply c A ⫤ Ω) ⟶ᵈʷ⁎⋅ -> (work_infer e c ⫤ Ω) ⟶ᵈʷ⁎⋅
  end.
Proof with auto with Hdb_dworklist_equiv.
  intros. dependent induction H; intros; eauto...
  - econstructor; eauto.
  - econstructor. 
    eapply IHd_typing; eauto.
    destruct_wf...
  - econstructor.
    destruct_wf.
    eapply IHd_typing1; eauto.
    apply d_wl_red__applycont with (w:=work_infabs A (cont_infapp e2 c)); eauto.
    econstructor. simpl.
    apply d_infabs_wft in H0 as Hwft. intuition.
    eapply d_wl_red_infabs_complete; eauto.
    econstructor... econstructor... econstructor.
    assert ((work_check e2 B ⫤ Ω) ⟶ᵈʷ⁎⋅).
      apply IHd_typing2; auto.
      apply d_wl_red_weaken_consw in H5; auto.
    replace (work_apply c C ⫤ work_check e2 B ⫤ Ω)%dworklist with (dwl_app (work_apply c C ⫤ dworklist_empty) (work_check e2 B ⫤ Ω)%dworklist) by auto.
    apply d_wl_red_strengthen_work; eauto.
  - destruct_wf.
    eapply d_wl_red__inf_abs_mono; eauto.
  - destruct_wf. 
    eapply d_wl_red__inf_tabs with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)); eauto. 
    intros. inst_cofinites_with X. dependent destruction H2.
    apply H1; auto. 
    eauto...
  - destruct_wf.
    apply d_chk_inf_wft in H0.
    econstructor.
    apply IHd_typing; auto...
    apply d_wl_red__applycont with (w:=(work_inftapp A B c)); eauto.
    econstructor.
    simpl.
    eapply d_wl_red_inftapp_complete; eauto.
  - destruct_wf.
    eapply d_wl_red__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H0... econstructor... econstructor... simpl. auto.
    simpl.
    rewrite_env ((x ~ dbind_typ typ_bot) ++ dwl_to_denv Ω).
    eapply d_wf_exp_bound_typ_head; eauto.
  - destruct_wf.
    eapply d_wl_red__chk_absarrow with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H1... 
    econstructor; econstructor; eauto.
    eapply d_wf_exp_bound_typ_head; eauto.
    simpl. apply d_wf_typ_weaken_cons...
  - destruct_wf. econstructor. 
    apply IHd_typing; auto... econstructor; auto.
    constructor; auto. simpl.
    apply d_wl_red_sub_complete; auto.
    apply d_chk_inf_wft in H. auto.
  - destruct_wf. eapply d_wl_red__chk_inter...
  - destruct_wf. eauto...
  - destruct_wf. eauto... 
Qed.


Theorem d_wl_red_complete: forall Ω, 
    ⊢ᵈʷ Ω -> Ω ⟶ᵈ⁎⋅ -> Ω ⟶ᵈʷ⁎⋅.
Proof with auto with Hdb_dworklist_equiv.
  intros. induction H0; auto;
  try solve [destruct_wf; econstructor; eauto with Hdb_dworklist_equiv].
  - destruct_wf. refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _); auto...
  - destruct_wf.
    refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _ _); auto...
    apply d_chk_inf_wft in H2.
    apply IHd_wl_del_red. auto.
  - destruct_wf. eapply d_wl_red_infabs_complete; eauto...
  - destruct_wf. 
    apply d_wl_red__infabsunion.
    eapply d_wl_red_infabs_complete; eauto.
    eapply d_wl_red__applycont with (w:=(work_unioninfabs (typ_arrow B1 C1)  (typ_arrow B2 C2) c)).
    apply applycont__unioninfabs.
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
    eapply d_wl_red__applycont with (w:=(work_unioninftapp C1 C2 c))...
    econstructor. simpl.
    apply d_inftapp_wft in H4.
    econstructor. intuition.
  - destruct_wf. apply d_wl_red_sub_complete; eauto.
  - destruct_wf. econstructor; eauto.
    apply IHd_wl_del_red. eapply d_wf_work_apply_cont; eauto.
Qed.


Print Assumptions  d_wl_red_complete.