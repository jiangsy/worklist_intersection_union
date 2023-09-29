Require Import Coq.Program.Equality.

Require Import ln_utils.
Require Import decl.def_ott.
Require Import decl.notations.
Require Import decl.worklist.def.


Hint Constructors d_wl_red : dworklist.
Hint Constructors d_wf_wl : dworklist.
Hint Constructors d_wl_del_red : dworklist.



(* This direction is not so important *)
Theorem d_wl_red_sound: forall Ω, 
    d_wf_wl Ω -> d_wl_red Ω -> d_wl_del_red Ω.
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
  - admit.
  - dependent destruction H. econstructor.
    assert (d_wf_wl
               (dworklist_conswork
                  (dworklist_conswork Γ
                     (dwork_sub B1 A1))
                  (dwork_sub A2 B2))) by admit.
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
    (dworklist_conswork Γ
      (dwork_infer e (dcont_sub A1)))) by admit.
    apply IHd_wl_red in H3. dependent destruction H3.
    dependent destruction H4. dependent destruction H4.
    dependent destruction H5.
    econstructor. econstructor; eauto...
    auto.
  (* \x. e <= top *)
  - econstructor.
    eapply d_typing_chkabs with (L:=L `union` dom (dwl_to_denv Γ)).
    admit.
    intros. inst_cofinites_with x.
    assert (d_wf_wl
      (dworklist_conswork ((dworklist_consvar Γ x (dbind_typ A1)))
       (dwork_check (open_dexp_wrt_dexp e (dexp_var_f x)) A2))) by admit.
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
  - eapply d__wldelred__inf with (T1:=A1). econstructor; eauto.
    admit.
    apply IHd_wl_red. admit.
  - eapply d__wldelred__inf with (T1:=A1). econstructor; eauto.
    admit.
    admit.
    admit.
  - admit.
  - eapply d__wldelred__inf with (T1:=dtyp_unit).
    + econstructor. admit.
    + apply IHd_wl_red. admit.
  - assert (d_wf_wl
  (dworklist_conswork Γ
     (dwork_infer e1
        (dcont_infabs
           (dcont_infapp e2 c))))) by admit.
    apply IHd_wl_red in H1. 
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    eapply d__wldelred__inf with (T1:=T3).
    econstructor; eauto.
    dependent destruction H3.
    dependent destruction H3.
    simpl in H4.
    dependent destruction H4. auto.
    dependent destruction H3.
    dependent destruction H3.
    simpl in H4.
    dependent destruction H4.
    dependent destruction H4.
    admit. (* weakening ? @chen *)
  - assert (d_wf_wl (dworklist_conswork Γ (dwork_infer e (dcont_inftapp T c)))) by admit.
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
  - eapply d__wldelred__inftapp with (T3:=T1 ^^ᵈ T2); eauto.
    econstructor; admit.
    apply IHd_wl_red. admit.
  (* bot o B =>=> _ *)
  - eapply d__wldelred__inftapp with (T3:=dtyp_bot); eauto.
    econstructor; admit.
    apply IHd_wl_red. admit.
  - assert (d_wf_wl (dworklist_conswork Γ (dwork_inftapp A1 B1 c))) by admit.
    apply IHd_wl_red in H1. 
    dependent destruction H1.
    eapply d__wldelred__inftapp with (T3:=T3); eauto.
    econstructor; eauto. admit.
  - admit.
  - assert (d_wf_wl
     (dworklist_conswork Γ
     (dwork_inftapp A1 B1 (dcont_inftappunion A2 B1 c)))) by admit.
    apply IHd_wl_red in H1.
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    eapply d__wldelred__inftapp with (T3:=dtyp_union C2 C0); eauto.
    econstructor; eauto.
  - assert (d_wf_wl
  (dworklist_conswork Γ
     (dwork_inftapp A2 B2 (dcont_unioninftapp C1 c)))) by admit.
    apply IHd_wl_red in H1.
    dependent destruction H1.
    dependent destruction H2.
    dependent destruction H2.
    simpl in H3.
    dependent destruction H3.
    econstructor; eauto.
  - econstructor. apply IHd_wl_red.
    admit.
  
  (* matching *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.

  - econstructor; eauto.
    apply IHd_wl_red. 
    admit.
Admitted.


Lemma d_wl_red_sub_complete: forall Ω A B,
   d_wf_wl (dworklist_conswork Ω (dwork_sub A B)) -> dwl_to_denv Ω ⊢ A <: B ->
   d_wl_red Ω -> d_wl_red (dworklist_conswork Ω (dwork_sub A B)).
Proof with auto with dworklist.
  intros * Hwfwl Hsub Hred.
  dependent induction Hsub; auto...
  - econstructor.
    dependent destruction Hwfwl. 
    dependent destruction H. auto...
    dependent destruction H. dependent destruction H1.
    auto.
  - dependent destruction Hwfwl. 
    eapply d__wlred__suball with (L:=L).
    intros. inst_cofinites_with SX.
    apply H2; eauto.
    econstructor. econstructor. simpl. admit.
    admit.
    econstructor. admit. auto. auto...
  - dependent destruction Hwfwl. 
    dependent destruction H5.
    eapply d__wlred__sub_alll with (B1:=T1); eauto. admit.
    apply IHHsub; eauto. admit.
  - dependent destruction Hwfwl. 
    dependent destruction H.
    dependent destruction H0.
    eapply d__wlred__sub_intersection1...
  - dependent destruction Hwfwl. 
    dependent destruction H0.
    dependent destruction H0.
    eapply d__wlred__sub_intersection2...
  - dependent destruction Hwfwl. 
    dependent destruction H0.
    dependent destruction H0.
    eapply d__wlred__sub_intersection3...
  - dependent destruction Hwfwl. 
    dependent destruction H0.
    dependent destruction H1.
    eapply d__wlred__sub_union1...
  - dependent destruction Hwfwl. 
    dependent destruction H0.
    dependent destruction H1.
    eapply d__wlred__sub_union2...
  - dependent destruction Hwfwl. 
    dependent destruction H.
    dependent destruction H. econstructor...
Admitted.


Theorem d_wl_red_complete: forall Ω, 
    d_wf_wl Ω -> d_wl_del_red Ω -> d_wl_red Ω.
Proof with auto with dworklist.
  intros. induction H0; auto...
  - constructor. apply IHd_wl_del_red.
    admit.
  - constructor. admit.
  - constructor. admit.
  - dependent destruction H0.
    + eapply d__wlred__chk_abstop. admit.
    + eapply d__wlred__chk_absarrow. admit.
    + eapply d__wlred__chk_sub; eauto.
      admit. admit. (* need to align the nonoverlapping condition *)
      admit.
    + admit.
    + admit.
    + admit.
  - admit.
  - admit.
  - apply d__wlred__infabsunion.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - apply d_wl_red_sub_complete; eauto.
    admit.
Admitted.


