
Require Import Coq.Program.Equality.

Require Import decl.def_extra.
Require Import decl.notations.
Require Import decl.prop_basic.
Require Import decl.prop_subtyping.
Require Import decl.explicit.def.
Require Import ln_utils.

Hint Constructors dexp_red : core.

Hint Resolve dwf_typ_lc_dtyp : core.

Inductive empty_var_dom : denv -> Prop :=
  | evd_empty : empty_var_dom nil
  | evd_empty_tvar : forall E X, empty_var_dom E -> empty_var_dom ((X , dbind_tvar_empty) :: E)
  | evd_empty_stvar : forall E SX, empty_var_dom E -> empty_var_dom  ((SX , dbind_stvar_empty) :: E)
.

Hint Constructors empty_var_dom : core.
 
Theorem bind_var_var_dom_not_empty : forall E x T,
  binds x (dbind_typ T) E -> empty_var_dom E -> False.
Proof.
  intros. induction E.
  - inversion H.
  - destruct a. destruct b.
    + inversion H.
      * inversion H1.
      * inversion H0. auto.
    + inversion H.
      * inversion H1.
      * inversion H0. auto.
    + inversion H0. 
Qed.
 
Theorem typing_all_inversion : forall E e T,
  d_typing_exptapp E e d_typingmode_inf (dtyp_all T) ->
  empty_var_dom E ->
  d_isval e ->
  (exists e1 T1, e = dexp_tabs (dbody_anno e1 T1)) \/ (exists e1 T1, e = dexp_anno (dexp_abs e1) (dtyp_all T1)).
Proof.
  intros.
  dependent induction H; try solve [inversion H2]; eauto.
  - dependent destruction H2; eauto.
Qed.

Hint Resolve dwf_typ_dlc_type : core.

 Theorem d_typing_exptapp_lc_dexp : forall E e m T1,
  d_typing_exptapp E e m T1 ->
  match m with 
  | d_typingmode_chk => lc_dexp e /\ lc_dtyp T1
  | d_typingmode_inf => lc_dexp e /\ lc_dtyp T1
  | d_typingmode_infapp T2 => lc_dexp e /\ lc_dtyp T1 /\ lc_dtyp T2
  end.
Proof with auto with typing.
  intros. induction H; try solve [intuition eauto 5].
  - split; auto.
    eapply dwf_typ_dlc_type; eapply dwf_env_binds_dwf_typ; eauto.
  - split.
    + inst_cofinites_by L. 
      inversion H1. inversion H2.
      eapply lc_dexp_tabs_exists with (X1:=x).
      econstructor; eauto.
    + eapply dwf_typ_dlc_type; eauto.
  - split. econstructor; intuition.
    + eapply dwf_typ_dlc_type; eauto.
    + apply lc_body_dtyp_wrt_dtyp.
      * apply lc_body_dtyp_all_1. intuition.
      * eauto.
  - split; auto.
    inst_cofinites_by L.
    eapply lc_dexp_abs_exists; intuition eauto.
  - split; inst_cofinites_by L.
    + eapply lc_dexp_abs_exists; intuition eauto.
    + eapply lc_dtyp_arrow; intuition eauto.
  - inst_cofinites_by L.
    split; intuition.
    apply lc_dtyp_all_exists with (X1:=x); auto.
  - split; intuition.
    + eapply dwf_typ_dlc_type. eapply dsub_dwft; eauto.
Qed.
  
 
Theorem progress' : forall E e m T,
   d_typing_exptapp E e m T ->
   empty_var_dom E ->
   d_isval e \/ exists e', dexp_red e e'.
Proof.
   intros. dependent induction H; intros; auto.
   - exfalso; eapply bind_var_var_dom_not_empty; eauto.
   - specialize (IHd_typing_exptapp H1).
     inversion IHd_typing_exptapp.
     + dependent destruction H2; eauto.
        * right. exists (dexp_tabs (dbody_anno e T)). eauto.
        * right. exists (dexp_anno (dexp_abs e) T). eauto.
     + right. destruct H2 as [e']. eauto.
   (* e1 e2 *)
   - specialize (IHd_typing_exptapp1 H1). 
     specialize (IHd_typing_exptapp2 H1). 
     inversion IHd_typing_exptapp1.
     + inversion IHd_typing_exptapp2.
       * dependent destruction H2.
         -- dependent destruction H. inversion H0.
         -- dependent destruction H.
         -- dependent destruction H.
         -- dependent destruction H.
            dependent destruction H1.
         -- dependent destruction H; eauto.
       * destruct H3 as [e2']. right. exists (dexp_app e1 e2'). 
         apply dexpred_app2; auto. 
     + right. destruct H2 as [e1'].
       exists (dexp_app e1' e2). 
       constructor; auto.
       specialize (d_typing_exptapp_lc_dexp _ _ _ _ H0). simpl. intuition.
   - left; eapply d_isval_tabs.
     inst_cofinites_by L.
     apply lc_dexp_tabs_exists with (X1:=x).
     specialize (d_typing_exptapp_lc_dexp _ _ _ _ H0).
     simpl. intros. inversion H3. dependent destruction H4.
     econstructor. fold open_dexp_wrt_dtyp_rec.
     intuition. intuition.
   (* e => BOT *)
   - specialize (IHd_typing_exptapp H1). inversion IHd_typing_exptapp.
     + destruct e; try solve [inversion H2; inversion H0].
       * dependent destruction H0. dependent destruction H3.
         right. exists (dexp_anno (dexp_abs e0) dtyp_bot).  
         apply dexpred_tappbot; auto.
         eapply dwf_typ_dlc_type; eauto.
     + right. destruct H2 as [e']. eauto.
   (* e @ T *)
   - specialize (IHd_typing_exptapp H1).
     inversion IHd_typing_exptapp.
     + specialize (typing_all_inversion _ _ _ H0 H1 H2).
       intros. inversion H3.
       * destruct H4 as [e3 [T3]]. rewrite H4.
         right. exists (dexp_anno (open_dexp_wrt_dtyp e3 T2) (open_dtyp_wrt_dtyp T3 T2)).
         eapply dexpred_tapptabs. subst.
         specialize (d_typing_exptapp_lc_dexp _ _ _ _ H0). simpl. intuition.
         eapply dwf_typ_dlc_type; eauto.
       * destruct H4 as [e3 [T3]]. rewrite H4.
         right. exists (dexp_anno (dexp_abs e3) (open_dtyp_wrt_dtyp T3 T2)).
         eapply dexpred_tappabs; subst.
         -- inversion H2; auto.
         -- inversion H2; auto.
         -- eapply dwf_typ_dlc_type; eauto.
     + destruct H2 as [e']. eauto.
   (* e => ∀ X . T *)
   - left. eapply d_isval_abs.
     inst_cofinites_by L.
     apply lc_dexp_abs_exists with (x1:=x).
     specialize (d_typing_exptapp_lc_dexp _ _ _ _ H). simpl. intuition.
   - left. eapply d_isval_abs.
    inst_cofinites_by L.
    apply lc_dexp_abs_exists with (x1:=x).
    specialize (d_typing_exptapp_lc_dexp _ _ _ _ H0). simpl. intuition.
   - inst_cofinites_by L. apply H1. constructor; auto.
Qed.

 
Theorem progress : forall e m T,
  d_typing_exptapp nil e m T ->
  d_isval e \/ exists e', dexp_red e e'.
Proof.
  intros. eapply progress'; eauto.
Qed.
 
 Hint Constructors d_typing_exptapp : type_safety.
 
Lemma check_top_sub : forall E T,
  d_typing_exptapp E dexp_top d_typingmode_chk T -> E ⊢ dtyp_top <: T.
Proof.
  intros; dependent induction H; eauto...
  - inversion H. inst_cofinites_by (L `union` L0). 
    exfalso. eapply dsub_top_fv_false; eauto.
  - dependent destruction H0; auto.
Qed.
 
Lemma check_unit_sub : forall E T,
  d_typing_exptapp E dexp_unit d_typingmode_chk T -> E ⊢ dtyp_unit <: T.
Proof.
  intros; dependent induction H; eauto...
  - inversion H. inst_cofinites_by (L `union` L0). 
    exfalso. eapply dsub_unit_fv_false; eauto.
  - dependent destruction H0; auto.
Qed.

Lemma sub_forall : forall L E F T1 T2,
  (forall X, X `notin` L -> F ++ (X ~ dbind_tvar_empty) ++ E ⊢ T1 <: T2 ^ᵈ X ) ->
  F ++ E ⊢ T1 <: dtyp_all T2.
Proof.
  (* intros. induction T1; auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - econstructor. *)
Admitted.

Lemma check_anno_sub : forall E e T1 T2,
  d_typing_exptapp E (dexp_anno e T1) d_typingmode_chk T2 -> E ⊢ T1 <: T2.
Proof.
  intros; dependent induction H; eauto...
  - replace E with (nil ++ E) by auto. eapply sub_forall with (L:=L). 
    intros. inst_cofinites_with X. simpl.
    eapply H1; eauto.
  - dependent destruction H0; auto.
Qed.

 (* E |- e <= T 
 [t2 / x] E |- [t2 / x] e <= [t2 / x] T *)
Theorem preservation : forall E e e' m T,
  d_typing_exptapp E e m T -> 
  dexp_red e e' -> 
  d_typing_exptapp E e' m T.
Proof with eauto with type_safety.
  intros. generalize dependent e'.
  induction H; intros e' Hred; try solve [inversion Hred]; eauto...
  - dependent destruction Hred; eauto...
    + dependent destruction H3.
      * admit. (* easy : proved in new lemma *)
      * admit. (* easy : proved in new lemma *)
      * inversion H2.
      * admit. 
      * admit.
  - dependent destruction Hred; eauto...
    inversion H.
    dependent destruction H. 
    
    admit.
  - dependent destruction Hred; eauto...
    + inversion H0.
    + inversion H0.
  - dependent destruction Hred.
    + eauto...
    + dependent destruction H0. 
      replace (open_dexp_wrt_dtyp (dexp_anno e T1) T2) with 
              (dexp_anno (open_dexp_wrt_dtyp e T2) (open_dtyp_wrt_dtyp T1 T2)) by auto.
      econstructor.
      * dependent destruction H0.
        inst_cofinites_by (L0 `union` ftv_in_dtyp T1).
        replace (T1 ^^ᵈ T2) with ({T2 /ᵈ x} T1 ^ᵈ x).
        assert (x ~ dbind_tvar_empty ++ E ⊢ {T2 /ᵈ x} T1 ^ᵈ x). {
          apply wft_all_open_wfdtyp_wft; eauto.
          apply dwf_typ_weakening_cons. auto.
        }
        admit.
        simpl. admit. 
      * inst_cofinites_by L. admit. (* medium : chk_subst *)
    + dependent destruction H0. eapply d_exptyping_infanno.
      * admit. (* easy : wft *)
      * dependent destruction H1; auto.
        -- admit.
        -- admit.
    + inversion H0.
Admitted.
 

Hint Resolve dsub_refl : core.

(* Theorem preservation_bot : forall E e e',
  d_typing_exptapp E e d_typingmode_inf dtyp_bot -> 
  dexp_red e e' -> 
  d_typing_exptapp E e' d_typingmode_inf dtyp_bot.
Proof.
  intros.
  dependent induction H.
  - inversion H1.
  - dependent destruction H1.
    + inversion H0.
  - admit.
  - inversion H0. *)

Theorem preservation' : forall E e e' m T1,
  d_typing_exptapp E e m T1 -> 
  dexp_red e e' -> 
  match m with 
  | d_typingmode_chk => d_typing_exptapp E e' m T1
  | d_typingmode_inf =>  exists T1', d_typing_exptapp E e' m T1' /\ d_sub E T1' T1
  | d_typingmode_infapp T2 => d_typing_exptapp E e' m T1
  end.
Proof with eauto with type_safety.
  intros. generalize dependent e'.
  induction H; intros e' Hred; try solve [inversion Hred]; eauto 1...
  - dependent destruction Hred; eauto 5...
    + exists T1; split; eauto.
      econstructor; eauto.
    + dependent destruction H3.
      * exists dtyp_unit.  
        specialize (check_unit_sub _ _ H0). intros; intuition eauto...
        econstructor. admit. (* easy *)
      * exists dtyp_top.
        specialize (check_top_sub _ _ H0). intros; intuition eauto...
        admit.
        (* medium : probelm of rules, top => ? *)
      * inversion H2.
      * admit. (* hard : problem of proof *)
      * admit. (* hard : problem of proof *)
  - dependent destruction Hred.
    + specialize (IHd_typing_exptapp1 _ Hred). 
      destruct IHd_typing_exptapp1 as [T1' [IHinf IHsub]].
      admit. (* medium : subsumption *)
    + specialize (IHd_typing_exptapp2 _ Hred). 
      exists T1. split; intuition eauto...
      eapply dsub_refl; admit.
    + inversion H.
    (* \ x . e <= T *)
    + dependent destruction H.
      clear IHd_typing_exptapp1. clear IHd_typing_exptapp2.
      admit. (* hard : probelm with proof *)
  - dependent destruction Hred; eauto...
    + specialize (IHd_typing_exptapp _ Hred).
      destruct IHd_typing_exptapp as [T1'].
      exists T1'. (* hard : problem of rules *) admit.
    + inversion H0.
    + inversion H0.
  - dependent destruction Hred; eauto...
    + specialize (IHd_typing_exptapp _ Hred).
      destruct IHd_typing_exptapp as [T1' [Hinf Hsub]].
      (* ((\ x : x) : ∀ a . a -> a /\ int -> int : ∀ a . a -> a) @ bool *)
      admit. (* hard : problems of rules *)
    + dependent destruction H0. admit. (* hard : stability of subtyping (poly) *)
    + dependent destruction H0. exists (T1 ^^ᵈ T2).
      * split. econstructor; eauto. 
        inversion H1. 
        admit. (* easy : wft *)
        admit. (* easy : wft *)
        admit. (* hard : ? *)
        admit. (* easy : wft *)
    + inversion H0. 
  - specialize (IHd_typing_exptapp _ Hred).
    destruct IHd_typing_exptapp as [S1'].
    eapply d_exptyping_chksub with (S1:=S1'); eauto.
    + admit. (* easy : transitivity *)
    + intuition.
Admitted.