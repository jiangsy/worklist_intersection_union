Require Import Coq.Program.Equality.

Require Import ln_utils.
Require Import decl.def_ott.
Require Import decl.notations.
Require Import decl.worklist.def.


Hint Constructors d_wl_red : dworklist.
Hint Constructors d_wl_del_red : dworklist.

Theorem d_wl_red_sound: forall W, 
    d_wf_wl W -> d_wl_red W -> d_wl_del_red W.
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

Theorem d_wl_red_complete: forall W, 
    d_wf_wl W -> d_wl_del_red W -> d_wl_red W.
Proof.
Admitted.


