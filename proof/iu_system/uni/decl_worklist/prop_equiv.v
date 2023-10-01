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



Ltac destruct_wf :=
  repeat
    match goal with
    | H : d_wf_wl (dworklist_conswork ?Ω ?w) |- _ => dependent destruction H
    | H : d_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : d_wf_typ ?E (typ_intersection ?A ?B) |- _ => dependent destruction H
    | H : d_wf_typ ?E (typ_union ?A ?B) |- _ => dependent destruction H
    | H : d_wf_typ ?E (typ_arrow ?A ?B) |- _ => dependent destruction H
    end.


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
  - admit.
  (* X <: X *)
  - admit.
  (* SX <: SX *)
  - dependent destruction H. econstructor.
    assert (d_wf_wl
               (dworklist_conswork
                  (dworklist_conswork Ω
                     (work_sub B1 A1))
                  (work_sub A2 B2))) by admit.
    apply IHd_wl_red in H2. dependent destruction H2.
    dependent destruction H3.
    admit.
    admit.
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
    apply IHd_wl_red in H3. dependent destruction H3.
    dependent destruction H4. dependent destruction H4.
    dependent destruction H5.
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
  - assert (d_wf_wl
  (dworklist_conswork Ω
     (work_infer e1
        (cont_infabs
           (cont_infapp e2 c))))) by admit.
    apply IHd_wl_red in H1. 
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    eapply d_wldelred__inf with (T1:=T3).
    econstructor; eauto.
    admit.
    dependent destruction H3.
    dependent destruction H3.
    simpl in H4.
    dependent destruction H4. 
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
  dwl_to_denv Ω ⊢ A <: B -> d_wf_wl (dworklist_conswork Ω (work_sub A B)) -> 
  Ω ⟶ₐ⁎⋅ -> (dworklist_conswork Ω (work_sub A B)) ⟶ₐ⁎⋅.
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
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_infabsunion (typ_arrow T3 T4) T2 c))).
    eapply d__ac__infabsunion.
    simpl.
    eapply d_wlred__infabsunion.
    apply IHd_infabs2; intuition.
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_unioninfabs (typ_arrow T3 T4) (typ_arrow T5 T6) c))).
    econstructor.
    simpl.
    econstructor.
    auto.  
Qed.

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
    eapply d__ac__unioninftapp...
    econstructor...
Qed.


Lemma d_wl_red_chk_inf_complete: forall Ω e A mode,
  d_typing (dwl_to_denv Ω) e mode A -> 
  match mode with 
  | typingmode__chk => d_wf_wl (work_check e A ⫤ Ω) -> Ω ⟶ₐ⁎⋅ -> (work_check e A ⫤ Ω) ⟶ₐ⁎⋅
  | typingmode__inf => forall c, d_wf_wl (work_infer e c ⫤ Ω) -> (work_apply c A ⫤ Ω) ⟶ₐ⁎⋅ -> (work_infer e c ⫤ Ω) ⟶ₐ⁎⋅
  end.
Proof with auto with dworklist.
  intros. dependent induction H; intros; eauto...
  - econstructor; eauto.
  - econstructor. 
    eapply IHd_typing; eauto.
    admit.
  - econstructor.
    eapply IHd_typing1; eauto.
    admit.
    apply d_wlred__applycont with (Ω':=dworklist_conswork dworklist_empty (work_infabs T1 (cont_infapp e2 c))); eauto.
    econstructor.
    simpl.
    eapply d_wl_red_infabs_complete; eauto.
    admit.
    admit.
  - econstructor; eauto.
   admit.
  - econstructor.
    admit.
  - eapply d_wlred__chk_abstop.
    admit.
  - eapply d_wlred__chk_absarrow.
    admit.
  - econstructor. admit. admit.
    apply IHd_typing; auto. admit.
    admit.
  - eapply d_wlred__chk_inter.
    eapply IHd_typing2; auto. admit.
    eapply IHd_typing1; auto. admit.
  - eapply d_wlred__chk_union1.
    eapply IHd_typing; auto.
    admit.
  - eapply d_wlred__chk_union2.
    eapply IHd_typing; auto.
    admit.
Admitted.


Theorem d_wl_red_complete: forall Ω, 
    d_wf_wl Ω -> Ω ⟶⁎⋅ -> Ω ⟶ₐ⁎⋅.
Proof with auto with dworklist.
  intros. induction H0; auto...
  - constructor. apply IHd_wl_del_red.
    admit.
  - constructor. admit.
  - constructor. admit.
  - refine (d_wl_red_chk_inf_complete _ _ _ _ H0 _ _); auto.
    apply IHd_wl_del_red. 
    admit.
  - dependent destruction H.
    dependent destruction H.
    refine (d_wl_red_chk_inf_complete _ _ _ _ H2 _ _ _); auto.
    apply IHd_wl_del_red.
    admit.
  - eapply d_wl_red_infabs_complete; eauto.
    apply IHd_wl_del_red.
    admit.
  - apply d_wlred__infabsunion.
    eapply d_wl_red_infabs_complete; eauto.
    admit. 
    eapply d_wlred__applycont with (Ω':=(dworklist_conswork dworklist_empty (work_unioninfabs (typ_arrow B1 C1)  (typ_arrow B2 C2) c))).
    apply d__ac__unioninfabs.
    simpl. econstructor.
    apply IHd_wl_del_red.
    admit.  
  - econstructor. apply IHd_wl_del_red. 
    admit.
  - apply d_wlred__infapp. 
    apply IHd_wl_del_red.
    admit.
  - eapply d_wl_red_inftapp_complete; eauto.
    apply IHd_wl_del_red.
    admit.
  - econstructor. 
    eapply d_wl_red_inftapp_complete; eauto.
    admit.
    admit.
  - dependent destruction H. 
    dependent destruction H.
    constructor.
    apply IHd_wl_del_red. auto.
  - dependent destruction H. apply d_wl_red_sub_complete; eauto.
Admitted.


