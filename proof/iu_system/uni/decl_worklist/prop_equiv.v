Require Import Coq.Program.Equality.

Require Import ln_utils.
Require Import uni.decl.def_extra.
Require Import uni.prop_basic.
Require Import uni.def_ott.
Require Import uni.notations.
Require Import uni.decl_worklist.def.


Hint Constructors d_wl_red : dworklist.
Hint Constructors d_wf_wl : dworklist.
Hint Constructors d_wl_del_red : dworklist.


Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dworklist.
Bind Scope dworklist_scope with dworklist.


Notation " x ~ T ; Ω " :=
  (dworklist_consvar Ω x (dbind_typ T))
      (at level 58, T at next level, right associativity) : dworklist_scope.
    
Notation " X ~ ▫ ; Ω " :=
  (dworklist_constvar Ω X dbind_tvar_empty)
      (at level 58, right associativity) : dworklist_scope.

Notation " X ~ ▪ ; Ω " :=
  (dworklist_constvar Ω X dbind_stvar_empty)
      (at level 58, right associativity) : dworklist_scope.

Notation " W ⫤ Ω " :=
  (dworklist_conswork Ω W)
      (at level 58, right associativity) : dworklist_scope.

Notation " Ω ⟶ₐ⁎⋅ " :=
  (d_wl_red Ω)
      (at level 58, no associativity) : type_scope.

Notation " Ω ⟶⁎⋅ " :=
  (d_wl_del_red Ω)
      (at level 58, no associativity) : type_scope.

Notation " ⊢ᵈ Ω " :=
  (d_wf_wl Ω)
      (at level 58, no associativity) : type_scope.
    


Ltac destruct_wf :=
  repeat
    match goal with
    | H : d_wf_wl (dworklist_conswork ?Ω ?w) |- _ => dependent destruction H
    | H : d_wf_wl (dworklist_consvar ?Ω ?w ?b) |- _ => dependent destruction H
    | H : d_wf_wl (dworklist_constvar ?Ω ?w ?b) |- _ => dependent destruction H
    | H : d_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : d_wf_typ ?E (typ_intersection ?A1 ?A2) |- _ => dependent destruction H
    | H : d_wf_typ ?E (typ_union ?A1 ?A2) |- _ => dependent destruction H
    | H : d_wf_typ ?E (typ_arrow ?A1 ?A2) |- _ => dependent destruction H
    | H : d_wf_exp ?E (exp_app ?e1 ?e2) |- _ => dependent destruction H
    | H : d_wf_exp ?E (exp_anno ?e1 ?A1) |- _ => dependent destruction H
    | H : d_wf_exp ?E (exp_tapp ?e1 ?A1) |- _ => dependent destruction H
    end.


Lemma d_wf_wl_wf_env : forall Ω,
  ⊢ᵈ Ω -> ⊢ (dwl_to_denv Ω).
Proof.
  intros. induction H; simpl; auto; econstructor; auto.
Qed.

(* This direction is not so important because soundness is proven against decl system directly *)
Theorem d_wl_red_sound: forall Ω, 
    d_wf_wl Ω -> Ω ⟶ₐ⁎⋅ -> Ω ⟶⁎⋅.
Proof with auto with dworklist.
  intros. induction H0; try solve [dependent destruction H; auto with dworklist].
  (* sub *)

  (* A <: top *)
  - admit.
  (* bot <: A *)
  - admit.
  (* 1 <: 1 *)
  - destruct_wf. 
    econstructor...
    econstructor...
    now apply d_wf_wl_wf_env.
  (* X <: X *)
  - destruct_wf. 
    econstructor...
    econstructor; eauto.
    now apply d_wf_wl_wf_env.
  (* A1 -> A2 <: B1 -> B2 *)
  - destruct_wf. 
    assert (⊢ᵈ (work_sub A2 B2 ⫤ work_sub B1 A1 ⫤ Ω)) by auto.
    apply IHd_wl_red in H3. 
    dependent destruction H3.
    dependent destruction H4.
    auto...
  - econstructor. admit. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.


  (* check *)

  (* e <= A -> e => _ <: A *)
  - assert (d_wf_wl
    (dworklist_conswork Ω
      (work_infer e (cont_sub A1)))) by admit.
    apply IHd_wl_red in H1. dependent destruction H1.
    dependent destruction H2. dependent destruction H2.
    dependent destruction H3.
    econstructor. econstructor; eauto...
    auto.
  (* \x. e <= top *)
  - econstructor.
    eapply d_typing__chkabs with (L:=L `union` dom (dwl_to_denv Ω)).
    admit.
    intros. inst_cofinites_with x.
    assert (d_wf_wl
      (dworklist_conswork ((dworklist_consvar Ω x (dbind_typ A1)))
       (work_check (open_exp_wrt_exp e (exp_var_f x)) A2))) by admit.
    apply H1 in H3.
    dependent destruction H3.
    simpl in H3. auto.
    admit.
  (* \x. e <= Top *)
  - admit.
  - admit.
  - admit.
  - admit.

  (* infer *)

  (* x => _ *)
  - eapply d_wldelred__inf with (T1:=A1). econstructor; eauto.
    admit.
    apply IHd_wl_red. admit.
  - eapply d_wldelred__inf with (T1:=A1). econstructor; eauto.
    admit.
    admit.
    admit.
  - admit.
  - eapply d_wldelred__inf with (T1:=typ_unit).
    + econstructor. admit.
    + apply IHd_wl_red. admit.
  - destruct_wf.
    assert (⊢ᵈ (work_infer e1 (cont_infabs (cont_infapp e2 c)) ⫤ Ω)) by auto.
    apply IHd_wl_red in H4.
    dependent destruction H4.
    dependent destruction H5.
    dependent destruction H5.
    simpl in H6.
    dependent destruction H6.
    dependent destruction H6.
    dependent destruction H6.
    simpl in H7.
    dependent destruction H7.
    eapply d_wldelred__inf with (T1:=T3).
    econstructor; eauto.
    admit. 
    admit.
  - assert (d_wf_wl (dworklist_conswork Ω (work_infer e (cont_inftapp T c)))) by admit.
    apply IHd_wl_red in H1.
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    econstructor; eauto.
    econstructor; eauto.
    admit.
  
  (* type application inference *)

  (* forall a. A o B =>=> _ *)
  - eapply d_wldelred__inftapp with (T3:=T1 ^^ᵈ T2); eauto.
    econstructor; admit.
    apply IHd_wl_red. admit.
  (* bot o B =>=> _ *)
  - eapply d_wldelred__inftapp with (T3:=typ_bot); eauto.
    econstructor; admit.
    apply IHd_wl_red. admit.
  - assert (d_wf_wl (dworklist_conswork Ω (work_inftapp A1 B1 c))) by admit.
    apply IHd_wl_red in H1. 
    dependent destruction H1.
    eapply d_wldelred__inftapp with (T3:=T3); eauto.
    econstructor; eauto. admit.
  - admit.
  - assert (d_wf_wl
     (dworklist_conswork Ω
     (work_inftapp A1 B1 (cont_inftappunion A2 B1 c)))) by admit.
    apply IHd_wl_red in H1.
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    eapply d_wldelred__inftapp with (T3:=typ_union C1 C2); eauto.
    econstructor; eauto.
  - assert (d_wf_wl
  (dworklist_conswork Ω
     (work_inftapp A2 B2 (cont_unioninftapp C1 c)))) by admit.
    apply IHd_wl_red in H1.
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    econstructor; eauto.
  - econstructor. apply IHd_wl_red.
    admit.
  
  (* infabs *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.

  - econstructor. 
    apply IHd_wl_red. admit.

  - econstructor; eauto.
    apply IHd_wl_red. 
    admit.
Admitted.


Lemma d_wl_red_sub_complete: forall Ω A B,
  dwl_to_denv Ω ⊢ A <: B -> ⊢ᵈ (work_sub A B ⫤ Ω) -> 
  Ω ⟶ₐ⁎⋅ -> (work_sub A B ⫤ Ω) ⟶ₐ⁎⋅.
Proof with auto with dworklist.
  intros * Hsub Hwfwl Hred.
  dependent induction Hsub; 
  try solve [destruct_wf; econstructor; auto with dworklist].
  - destruct_wf. 
    eapply d_wlred__sub_all with (L:=L `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with SX.
    apply H2; eauto...
    inst_cofinites_with X.
    apply d_sub_dwft in H1; intuition.
  - destruct_wf. 
    eapply d_wlred__sub_alll with (T1:=T1); eauto. 
    apply IHHsub; eauto. 
    econstructor; auto. econstructor; auto.
    apply d_wft_all_open; eauto; auto.
    eapply d_sub_dwft; eauto.
    eapply d_mono_typ_d_wf_typ; auto.
Qed.


Lemma d_infabs_wft : forall E A1 B1 C1,
  E ⊢ A1 ▹ B1 → C1 ->
  ⊢ E /\ E ⊢ A1 /\ E ⊢ B1 /\ E ⊢ C1.
Proof.
  intros. induction H; intuition.
Qed.


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


Lemma d_wl_app_assoc : forall Ω1 Ω2 Ω3,
  dwl_app Ω3 (dwl_app Ω2 Ω1) = dwl_app (dwl_app Ω3 Ω2) Ω1.
Proof.
  induction Ω3; auto.
  - simpl. rewrite <- IHΩ3. auto.
  - simpl. rewrite <- IHΩ3. auto.
  - simpl. rewrite <- IHΩ3. auto.
Qed.

Lemma d_wl_red_weaken: forall Ω1 Ω2,
  (dwl_app Ω2 Ω1) ⟶ₐ⁎⋅ -> Ω1 ⟶ₐ⁎⋅ .
Proof.
  intros. dependent induction H; try destruct Ω2; simpl in x; try solve [inversion x]; dependent destruction x; simpl; eauto with dworklist;
    try solve [eapply IHd_wl_red; rewrite_dwl_app; eauto].
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - inst_cofinites_by L. eapply H0.
    rewrite_dwl_app; eauto.
  - eapply IHd_wl_red. rewrite d_wl_app_assoc. eauto.
Qed.

Corollary d_wl_red_weaken_consw : forall Ω w,
  dworklist_conswork Ω w ⟶ₐ⁎⋅ -> Ω ⟶ₐ⁎⋅ .
Proof.
  intros.
  replace (w ⫤ Ω)%dworklist with (dwl_app (dworklist_conswork dworklist_empty w) Ω) in H by auto.
  eapply d_wl_red_weaken. eauto.
Qed.

Lemma d_wl_app_cons_work_same_env : forall Ω1 Ω2 w,
  dwl_to_denv (dwl_app Ω2 (w ⫤ Ω1)) = dwl_to_denv (dwl_app Ω2 Ω1).
Proof.
  intros. induction Ω2; simpl; auto.
  rewrite IHΩ2. auto.
  rewrite IHΩ2. auto.
Qed.


Lemma d_wl_red_strengthen_work : forall Ω1 Ω2 w,
  (w ⫤ Ω1) ⟶ₐ⁎⋅ -> (dwl_app Ω2 Ω1) ⟶ₐ⁎⋅ -> (dwl_app Ω2 (w ⫤ Ω1)) ⟶ₐ⁎⋅ .
Proof. 
  intros. dependent induction H0; 
      try destruct Ω2; simpl in x; try solve [inversion x]; dependent destruction x; simpl; eauto with dworklist;
      try solve [econstructor; rewrite_dwl_app; auto].
  - eapply d_wlred__sub_all with (L:=L). 
    intros. inst_cofinites_with X. 
    rewrite_dwl_app. auto.
  - eapply d_wlred__sub_alll with (T1:=T1); auto.
    rewrite d_wl_app_cons_work_same_env; auto.
    rewrite_dwl_app. auto.
  - eapply d_wlred__chk_absarrow with (L:=L).
    intros. inst_cofinites_with x.
    rewrite_dwl_app. auto.
  - eapply d_wlred__chk_abstop with (L:=L).
    intros. inst_cofinites_with x.
    rewrite_dwl_app. auto.
  - eapply d_wlred__inf_var with (A1:=A1). 
    rewrite d_wl_app_cons_work_same_env. auto.
    rewrite_dwl_app. auto.
  - eapply d_wlred__inf_tabs with (L:=L).
    intros. inst_cofinites_with X.
    rewrite_dwl_app. auto.
  - eapply d_wlred__infabs_all with (T1:=T1).
    rewrite d_wl_app_cons_work_same_env. auto.
    rewrite_dwl_app. auto.
  - econstructor; eauto.
    rewrite d_wl_app_assoc.
    apply IHd_wl_red; auto.
    eapply d_wl_app_assoc.
Qed.


Lemma d_wl_red_infabs_complete: forall Ω A B C c,
   dwl_to_denv Ω ⊢ A ▹ B → C -> d_wf_wl (dworklist_conswork Ω (work_infabs A c)) -> 
   d_wl_red (dworklist_conswork Ω (work_apply c (typ_arrow B C))) -> d_wl_red (dworklist_conswork Ω (work_infabs A c)).
Proof with auto with dworklist.
  intros. generalize dependent c. dependent induction H; intros; eauto;
  try solve [destruct_wf; econstructor; auto with dworklist].
  - destruct_wf.
    eapply d_wlred__infabs_all with (T1:=T2); eauto.
    apply IHd_infabs; auto.
    econstructor; auto. econstructor; auto.
    apply d_wft_all_open; eauto.
    eapply d_infabs_wft; eauto.
  - destruct_wf.
    apply d_infabs_wft in H.
    apply d_wlred__infabs_union.
    apply IHd_infabs1; auto.
    eapply d_wlred__applycont with 
      (Ω':=(dworklist_conswork dworklist_empty (work_infabsunion (typ_arrow T3 T4) T2 c))).
    eapply d_applycont__infabsunion.
    simpl.
    eapply d_wlred__infabsunion.
    apply IHd_infabs2; intuition.
    eapply d_wlred__applycont with 
      (Ω':=(dworklist_conswork dworklist_empty (work_unioninfabs (typ_arrow T3 T4) (typ_arrow T5 T6) c))).
    econstructor.
    simpl.
    econstructor.
    auto.  
Qed.


(* remove later *)
Lemma d_inftapp_wft : forall E A B C,
  d_inftapp E A B C ->
  ⊢ E /\ E ⊢ A /\ E ⊢ B /\ E ⊢ C.
Proof.
  intros. induction H; intuition.
  - eapply d_wft_all_open; eauto.
Qed.

Lemma d_wl_red_inftapp_complete: forall Ω A B C c,
  dwl_to_denv Ω ⊢ A ○ B ⇒⇒ C -> d_wf_wl (dworklist_conswork Ω (work_inftapp A B c)) ->
  d_wl_red (dworklist_conswork Ω (work_apply c C)) -> d_wl_red (dworklist_conswork Ω (work_inftapp A B c)).
Proof with auto with dworklist.
  intros. generalize dependent c. dependent induction H; intros; eauto;
  try solve [destruct_wf; econstructor; eauto with dworklist].
  - apply d_inftapp_wft in H.
    destruct_wf.
    econstructor.
    eapply IHd_inftapp1...
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_inftappunion C1 A2 B c))).
    econstructor.
    simpl.
    econstructor. 
    eapply IHd_inftapp2... intuition.
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_unioninftapp C1 C2 c))).
    eapply d_applycont__unioninftapp...
    econstructor...
Qed.


(* remove later *)
Lemma d_chk_inf_wft: forall E e mode A1,
  d_typing E e mode A1 ->
  E ⊢ A1.
Proof.
  intros. induction H; auto.
  - admit. 
  - apply d_infabs_wft in H0; intuition.
  - apply d_inftapp_wft in H1; intuition.
  - admit.
Admitted.


Lemma d_wl_red_chk_inf_complete: forall Ω e A mode,
  d_typing (dwl_to_denv Ω) e mode A -> 
  match mode with 
  | typingmode__chk => ⊢ᵈ (work_check e A ⫤ Ω) -> Ω ⟶ₐ⁎⋅ -> (work_check e A ⫤ Ω) ⟶ₐ⁎⋅
  | typingmode__inf => forall c, ⊢ᵈ (work_infer e c ⫤ Ω) -> (work_apply c A ⫤ Ω) ⟶ₐ⁎⋅ -> (work_infer e c ⫤ Ω) ⟶ₐ⁎⋅
  end.
Proof with auto with dworklist.
  intros. dependent induction H; intros; eauto...
  - econstructor; eauto.
  - econstructor. 
    eapply IHd_typing; eauto.
    destruct_wf...
  - econstructor.
    destruct_wf.
    eapply IHd_typing1; eauto.
    apply d_wlred__applycont with (Ω':=dworklist_conswork dworklist_empty (work_infabs T1 (cont_infapp e2 c))); eauto.
    econstructor. simpl.
    apply d_infabs_wft in H0 as Hwft. intuition.
    eapply d_wl_red_infabs_complete; eauto.
    econstructor... econstructor... econstructor.
    assert ((work_check e2 T2 ⫤ Ω) ⟶ₐ⁎⋅).
      apply IHd_typing2; auto.
      apply d_wl_red_weaken_consw in H5; auto.
    replace (work_apply c T3 ⫤ work_check e2 T2 ⫤ Ω)%dworklist with (dwl_app (work_apply c T3 ⫤ dworklist_empty) (work_check e2 T2 ⫤ Ω)%dworklist) by auto.
    apply d_wl_red_strengthen_work; eauto.
  - destruct_wf. 
    dependent destruction H2.
    eapply d_wlred__inf_tabs with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)); eauto. 
    intros. inst_cofinites_with X. dependent destruction H2.
    apply H1; auto. 
    eauto...
  - destruct_wf.
    apply d_chk_inf_wft in H0.
    econstructor.
    apply IHd_typing; auto...
    apply d_wlred__applycont with (Ω':=dworklist_conswork dworklist_empty (work_inftapp T1 T2 c)); eauto.
    econstructor.
    simpl.
    eapply d_wl_red_inftapp_complete; eauto.
  - destruct_wf.
    dependent destruction H1.
    eapply d_wlred__chk_abstop with (L:=L `union` L0 `union` dom (dwl_to_denv Ω)).
    intros. inst_cofinites_with x.
    apply H0... econstructor... econstructor... simpl. auto. 
    admit.
  - destruct_wf.
    dependent destruction H2.
    eapply d_wlred__chk_absarrow with (L:=L `union` L0).
    intros. inst_cofinites_with x.
    apply H1... 
    admit.
  - destruct_wf. econstructor. 
    apply IHd_typing; auto... econstructor; auto.
    constructor; auto. simpl.
    apply d_wl_red_sub_complete; auto.
    apply d_chk_inf_wft in H. auto.
  - destruct_wf. eapply d_wlred__chk_inter...
  - destruct_wf. eauto...
  - destruct_wf. eauto... 
Admitted.


Theorem d_wf_work_apply_cont : forall Ω c A1 Ω',
  ⊢ᵈ Ω -> d_wf_cont (dwl_to_denv Ω) c -> dwl_to_denv Ω ⊢ A1 -> d_apply_cont c A1 Ω' ->
  ⊢ᵈ dwl_app Ω' Ω.
Proof.
  intros. induction H2; simpl; auto;
   try solve [dependent destruction H0; auto].
Qed.


Theorem d_wl_red_complete: forall Ω, 
    ⊢ᵈ Ω -> Ω ⟶⁎⋅ -> Ω ⟶ₐ⁎⋅.
Proof with auto with dworklist.
  intros. induction H0; auto;
  try solve [destruct_wf; econstructor; eauto with dworklist].
  - destruct_wf. refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _); auto...
  - destruct_wf.
    refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _ _); auto...
    apply d_chk_inf_wft in H2.
    apply IHd_wl_del_red. auto.
  - destruct_wf. eapply d_wl_red_infabs_complete; eauto...
    apply d_infabs_wft in H2. 
    intuition.
  - destruct_wf. 
    apply d_wlred__infabsunion.
    eapply d_wl_red_infabs_complete; eauto.
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_unioninfabs (typ_arrow B1 C1)  (typ_arrow B2 C2) c))).
    apply d_applycont__unioninfabs.
    simpl. econstructor.
    apply d_infabs_wft in H4. 
    apply IHd_wl_del_red. intuition.
  - destruct_wf.
    econstructor. apply IHd_wl_del_red...
  - destruct_wf.
    apply d_wlred__infapp. 
    apply IHd_wl_del_red...
  - destruct_wf.  eapply d_wl_red_inftapp_complete; eauto.
    apply d_inftapp_wft in H3. intuition.
  - destruct_wf. econstructor. 
    eapply d_wl_red_inftapp_complete; eauto...
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_unioninftapp C1 C2 c)))...
    econstructor. simpl.
    apply d_inftapp_wft in H4.
    econstructor. intuition.
  - destruct_wf. apply d_wl_red_sub_complete; eauto.
  - destruct_wf. econstructor; eauto.
    apply IHd_wl_del_red. eapply d_wf_work_apply_cont; eauto.
Qed.

