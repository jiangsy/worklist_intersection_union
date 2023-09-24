Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.


Require Import decl.notations.
Require Import decl.prop_basic.
Require Import decl.prop_subtyping.
Require Import ln_utils.


Definition wf_dom : forall {E}, ⊢ E -> atoms.
Proof.
  intros.
  set (x := dom E). exact x.
Defined.


Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.
Hint Constructors d_typing : typing.



Inductive d_subenv : denv -> denv -> Prop := 
| d_subenv_empty: d_subenv nil nil  
| d_subenv_tvar : forall E1 E2 X, 
    d_subenv E1 E2 -> 
    d_subenv (X ~ dbind_tvar_empty  ++  E1) 
        (X ~ dbind_tvar_empty  ++  E2)
| d_subenv_stvar : forall E1 E2 SX, 
    d_subenv E1 E2 -> 
    d_subenv (SX ~ dbind_stvar_empty  ++  E1) 
        (SX ~ dbind_stvar_empty  ++  E2)
| d_subenv_var : forall E1 E2 x S1 T1,
    d_subenv E1 E2 ->
    d_sub E2 S1 T1 ->
    d_subenv (x ~ dbind_typ S1 ++ E1) 
        (x ~ dbind_typ T1 ++ E2)        
.

Hint Constructors d_subenv: typing.

Lemma d_subenv_refl: forall E,
  ⊢ E -> d_subenv E E.
Proof with auto with typing.
  intros. induction H; auto...
  econstructor; auto.
  apply dsub_refl; auto.
Qed.

Lemma d_subenv_same_dom : forall E E', 
  d_subenv E' E ->
  dom E = dom E'.
Proof.
  intros. induction H; simpl; auto; rewrite IHd_subenv; auto.
Qed.

Lemma d_subenv_same_tvar : forall E E' X, 
  d_subenv E' E ->
  binds X dbind_tvar_empty E ->
  binds X dbind_tvar_empty E'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.


Lemma d_subenv_same_var : forall E E' T1 x, 
  ⊢ E ->
  d_subenv E' E ->
  x ~ T1 ∈ E ->
  exists S1, x ~ S1 ∈ E' /\ E ⊢ S1 <: T1.
Proof.
  intros. induction H0; simpl; intros; auto.
  - inversion H1; auto.
  - inversion H1; auto.
    + inversion H2.
    + dependent destruction H. 
      specialize (IHd_subenv H H3).
      destruct IHd_subenv as [S1].
      exists S1; intuition.
      eapply d_sub_weakening_cons; eauto.
  - inversion H1; auto.
    + inversion H2.
    + dependent destruction H. specialize (IHd_subenv H H3).
      destruct IHd_subenv as [S1].
      exists S1; intuition.
      eapply d_sub_weakening_cons; eauto.
  - inversion H1; auto.
    + dependent destruction H3.
      exists S1; intuition.
      eapply d_sub_weakening_cons; eauto.
    + dependent destruction H. specialize (IHd_subenv H H5).
      destruct IHd_subenv as [S2].
      exists S2; intuition.
      eapply d_sub_weakening_cons; eauto.
Qed.


Lemma d_subenv_same_stvar : forall E E' SX, 
  d_subenv E' E ->
  binds SX dbind_stvar_empty E ->
  binds SX dbind_stvar_empty E'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.


Lemma d_subenv_wf_typ : forall E E' T, 
  E ⊢ T -> d_subenv E' E -> E' ⊢ T.
Proof.
  intros * H. generalize dependent E'. induction H; intros; auto.
  - econstructor. 
    eapply d_subenv_same_tvar; eauto.
  - econstructor.
    eapply d_subenv_same_stvar; eauto.
  - eapply dwftyp_all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed.


Lemma d_subenv_wf_env : forall E, 
  ⊢ E -> 
  forall E', 
    d_subenv E' E ->
    ⊢ E'.
Proof.
  intros E H. induction H; intros.
  - inversion H. auto.
  - dependent destruction H1.
    econstructor; auto. 
    erewrite <- d_subenv_same_dom; auto.
  - dependent destruction H1.
    econstructor; auto. 
    erewrite <- d_subenv_same_dom; auto.
  - dependent destruction H2.
    econstructor; auto.
    + apply d_sub_dwft in H3. destruct H3.
      eapply d_subenv_wf_typ; eauto. auto. intuition.
    + erewrite <- d_subenv_same_dom; auto.
Qed.


Lemma d_subenv_wf_env_inv : forall E', 
  ⊢ E' -> 
  forall E, 
    d_subenv E' E ->
    ⊢ E.
Proof.
Admitted.


Ltac solve_wf_subenv := match goal with 
  | H : d_subenv ?E' ?E |- ?E' ⊢ ?T => eapply d_subenv_wf_typ; eauto
  | H : d_subenv ?E' ?E |- ⊢ ?E' => eapply d_subenv_wf_env; eauto
end.

Lemma denvsub_sub: forall E S1 T1, 
  E ⊢ S1 <: T1 -> forall E', d_subenv E' E -> E' ⊢ S1 <: T1.
Proof.
  intros E S1 T1 Hsub.
  induction Hsub; try solve [econstructor; solve_wf_subenv].
  - econstructor; auto.
  - intros. econstructor; auto. intros. inst_cofinites_with SX. 
    specialize (H2 (SX ~ dbind_stvar_empty ++ E')).
    assert (d_subenv (SX ~ dbind_stvar_empty ++ E') (SX ~ dbind_stvar_empty ++ E)). {
      constructor. auto. }
    specialize (H2 H5).
    auto.
  - intros. eapply d_sub_alll with (T2:=T2); auto. solve_wf_subenv.
  - intros. 
    apply d_sub_intersection1; auto.
  - intros.
    apply d_sub_intersection2; auto.
    eapply d_subenv_wf_typ; eauto.
  - intros.
    apply d_sub_intersection3; auto.
    eapply d_subenv_wf_typ; eauto.
  - intros.
    apply d_sub_union1; auto.
    eapply d_subenv_wf_typ; eauto.
  - intros.
    apply d_sub_union2; auto.
    eapply d_subenv_wf_typ; eauto.
  - intros.
    apply d_sub_union3; auto.
Qed.

Hint Resolve d_subenv_wf_typ : typing.
Hint Resolve d_subenv_wf_env : typing.
Hint Resolve d_wft_typ_subst : typing.
Hint Resolve d_wf_env_subst_tvar_typ : typing.
Hint Resolve bind_typ_subst : typing. 
Hint Resolve dwf_typ_dlc_type : typing.


(* for the e <= forall a. A, not used now*)
Theorem d_chkinf_subst_mono: forall E F X e m T1 T2,
  d_typing (F ++ X ~ dbind_tvar_empty ++ E) e m T1 ->
  E ⊢ T2 ->
  dmono_typ T2 ->
  d_typing (map (d_subst_tv_in_binding T2 X) F  ++ E) (d_subst_tv_in_dexp T2 X e) m ({T2 /ᵈ X} T1).
Proof with auto with typing.
  (* intros.
  generalize dependent T2.
  dependent induction H; intros; try solve [simpl in *; eauto 5 with typing].
  - simpl in *. eapply d_typing_inftabs with (L:=L `union` singleton X).
    + replace (dtyp_all ({T2 /ᵈ X} T1)) with ({T2 /ᵈ X}  dtyp_all T1) by auto.
      auto... 
    + intros. specialize (notin_union_1 _ _ _ H4). intros.
      specialize (H1 _ H5 E (X0 ~ dbind_tvar_empty ++ F) X (JMeq_refl _) T2 H2 H3).
      assert (lc_dtyp T2) by eauto...
      specialize (d_subst_tv_in_dexp_open_dexp_wrt_dtyp e T2 (dtyp_var_f X0) X H6).
      intros. simpl in H7. unfold eq_dec in H7.
      destruct (EqDec_eq_of_X X0 X) in H7.
      * subst. apply notin_union_2 in H4. apply notin_singleton_1 in H4.
        contradiction.
      * rewrite <- H7. rewrite dtyp_subst_open_comm; auto.
  - simpl in *. rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
  - simpl in *. apply d_typing_chkabstop with (L:=L).
    intros x Hfr. inst_cofinites_with x.
    replace (dexp_var_f x) with (d_subst_tv_in_dexp T2 X (dexp_var_f x)) by auto.
    rewrite <-  d_subst_tv_in_dexp_open_dexp_wrt_dexp. 
    replace (x ~ dbind_typ dtyp_bot ++ map (d_subst_tv_in_binding T2 X) F ++ E) with 
    ((map (d_subst_tv_in_binding T2 X) (x ~ dbind_typ dtyp_bot ++ F)) ++ E) by auto. 
    auto...
  - simpl in *. eapply d_typing_chkabs with (L:=L); eauto...
    intros X1 Hfr.
    inst_cofinites_with X1.
    specialize (H1 E ((X1, dbind_typ T1) :: F ) X (JMeq_refl _) T0 H2 H3).
    replace (dexp_var_f X1) with (d_subst_tv_in_dexp T0 X (dexp_var_f X1)) by (simpl; auto).
    rewrite <- d_subst_tv_in_dexp_open_dexp_wrt_dexp; eauto...
  - simpl in *. eapply d_typing_chkall with (L:=L `union` singleton X); eauto...
    + replace (dtyp_all ({T2 /ᵈ X} T1)) with ({T2 /ᵈ X} dtyp_all T1) by auto. 
      auto...
    + intros. inst_cofinites_with X0.
      rewrite dtyp_subst_open_comm; eauto...
      replace (X0 ~ dbind_tvar_empty ++ map (d_subst_tv_in_binding T2 X) F ++ E) with 
      (map (d_subst_tv_in_binding T2 X) (X0 ~ dbind_tvar_empty ++ F) ++ E) by auto.
      auto.
  - simpl in *. 
    apply d_typing_chksub with (S1:=({T2 /ᵈ X} S1)); eauto.
    eapply d_sub_subst_mono; eauto.
  - simpl in *. eapply d_typing_infappall with (T3:={T0 /ᵈ X} T3); eauto...
    + apply d_mono_typ_subst_mono_mono; auto.
    + replace (dtyp_all ({T0 /ᵈ X} T1)) with ({T0 /ᵈ X} dtyp_all T1) by auto.
      auto...
    + rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto... *)
Admitted.


Definition dmode_size (mode : d_typing_mode) : nat := 
  match mode with 
  | d_typingmode_inf => 0
  | d_typingmode_chk => 1
  end.


Fixpoint 
  dexp_size (e:dexp) : nat :=
    match e with 
    | dexp_unit => 1
    | dexp_top => 1
    | dexp_var_f _ => 1
    | dexp_var_b _ => 1
    | dexp_abs e1 => 1 + dexp_size e1
    | dexp_app e1 e2 => 1 + dexp_size e1 + dexp_size e2 
    | dexp_anno e1 _ => 1 + dexp_size e1
    | dexp_tapp e1 _ => 1 + dexp_size e1
    | dexp_tabs b => 1 + d_body_size b  
    end with 
  d_body_size (b:dbody) :=
    match b with 
    | dbody_anno e T => 1 + dexp_size e
    end
  .


Fixpoint dtyp_size (T:dtyp) : nat :=
  match T with 
  | dtyp_intersection T1 T2 => dtyp_size T1 + dtyp_size T2 + 1
  | dtyp_union T1 T2 => dtyp_size T1 + dtyp_size T2 + 1
  | _ => 0
  end.
  

(* @shengyi:todo *** *)
(* Theorem d_infabs_subsumption : forall E T1 T2 S1, d_infabs E T1 T2 -> E ⊢ S1 <:T1 ->
  exists S2, d_infabs E.
Proof.
Admitted. *)

Hint Constructors d_inftapp : inftapp.
Hint Constructors d_inftapp_false : inftapp.


Lemma d_inftapp_wft : forall E A B C,
  d_inftapp E A B C ->
  ⊢ E /\ E ⊢ A /\ E ⊢ B /\ E ⊢ C.
Proof with auto with typing. 
  intros. induction H; intuition.
  - dependent destruction H0.
    pick fresh X. inst_cofinites_with X.
    replace (T1 ^^ᵈ T2) with ({T2 /ᵈ X} T1 ^ᵈ X).
    + rewrite_env ((map (d_subst_tv_in_binding T2 X) nil) ++ E).
      apply d_wft_typ_subst; eauto... 
      econstructor; eauto.
    + rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp...
      rewrite (d_subst_tv_in_dtyp_fresh_eq T1)...
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X X X); eauto. contradiction.
      eapply dwf_typ_dlc_type; eauto.
Qed.


Theorem d_inftapp_total: forall E A B,
  ⊢ E -> E ⊢ A -> E ⊢ B -> d_inftapp_false A \/ exists C, d_inftapp E A B C.
Proof with auto with inftapp.
  intros * Hwfenv Hwfta Hwftb. induction Hwfta; try solve intuition...
  - right. exists dtyp_bot. auto...
  - right. exists (T ^^ᵈ B). constructor; eauto...
  - specialize (IHHwfta1 Hwfenv Hwftb).
    specialize (IHHwfta2 Hwfenv Hwftb).
    inversion IHHwfta1; inversion IHHwfta2; auto...
    right.
    destruct H as [C1 Hc1]. destruct H0 as [C2 Hc2].
    exists (dtyp_union C1 C2); auto...
  - specialize (IHHwfta1 Hwfenv Hwftb).
    specialize (IHHwfta2 Hwfenv Hwftb).
    inversion IHHwfta1; inversion IHHwfta2.
    + auto...
    + right. destruct H0 as [C2 Hc2]. exists C2. auto...
    + right. destruct H as [C1 Hc1]. exists C1. auto...
    + destruct H as [C1 Hc1]. destruct H0 as [C2 Hc2].
      right. exists (dtyp_intersection C1 C2); auto...
Qed.


Hint Resolve d_inftapp_wft : typing.


Lemma d_inftapp_disjoint : forall E A1 B1 C1,
  d_inftapp E A1 B1 C1 ->
  d_inftapp_false A1 ->
  False.
Proof.
  intros. dependent induction H.
  - inversion H1.
  - inversion H2.
  - inversion H2. contradiction.
  - inversion H2. contradiction.
  - inversion H1. contradiction.
  - inversion H1; contradiction.
Qed.



Lemma d_inftapp_determinism: forall E A1 B1 C1 C2, 
  E ⊢ A1 ○ B1 ⇒⇒ C1 -> 
  E ⊢ A1 ○ B1 ⇒⇒ C2 ->
  C1 = C2.
Proof.
  intros. generalize dependent C2. induction H; intros.
  - dependent destruction H1; auto.
  - dependent destruction H2; auto.
  - dependent destruction H2; auto; exfalso; eapply d_inftapp_disjoint; eauto.
  - dependent destruction H2; auto. 
    + exfalso. eapply d_inftapp_disjoint; eauto.
    + exfalso. eapply d_inftapp_disjoint in H0; eauto.
  - dependent destruction H1; auto. 
    + exfalso. eapply d_inftapp_disjoint in H2; eauto.
    + exfalso. eapply d_inftapp_disjoint in H2; eauto.
    + specialize (IHd_inftapp1 _ H1_).
      specialize (IHd_inftapp2 _ H1_0).
      subst. auto.
  - dependent destruction H1; auto.
    specialize (IHd_inftapp1 _ H1_).
    specialize (IHd_inftapp2 _ H1_0).
    subst. auto.
Qed.

(* @shengyi:todo *** *)
Theorem d_inftapp_subsumption_same_env : forall E A1 B1 C1 A2, 
  E ⊢ A1 ○ B1 ⇒⇒ C1 -> 
  E ⊢ A2 <: A1 ->
  exists C2, E ⊢ C2 <: C1 /\ E ⊢ A2 ○ B1 ⇒⇒ C2.
Proof with auto with typing.
  intros. generalize dependent A2. dependent induction H.
  - intros. dependent induction H1.
    + exists dtyp_bot. split; auto... constructor; auto.
    + eapply d_sub_open_mono_bot_false in H6; eauto. contradiction.
    + specialize (d_inftapp_total _ _ _ H H2 H0). intros.
      specialize (IHd_sub H H0 (eq_refl _)). destruct IHd_sub as [C1 Hc1].
      inversion H3. 
      * exists C1; intuition...
      * destruct H4 as [C2 Hc2]. destruct Hc1.
        exists (dtyp_intersection C1 C2); split.
        -- constructor; auto.
           eapply d_inftapp_wft; eauto.
        -- apply d_inftapp_intersection3; auto.
    + specialize (d_inftapp_total _ _ _ H H2 H0). intros.
      specialize (IHd_sub H H0 (eq_refl _)). destruct IHd_sub as [C1 Hc1].
      inversion H3. 
      * exists C1; intuition...
      * destruct H4 as [C2 Hc2]. destruct Hc1.
        exists (dtyp_intersection C2 C1); split.
        -- apply d_sub_intersection3; auto.         
           eapply d_inftapp_wft. eauto.
        -- apply d_inftapp_intersection3; auto.
    + specialize (IHd_sub1 H H0 (eq_refl _)). destruct IHd_sub1 as [C1 Hc1].
      specialize (IHd_sub2 H H0 (eq_refl _)). destruct IHd_sub2 as [C2 Hc2].
      exists (dtyp_union C1 C2). split.
      intuition... intuition...
  - intros. dependent induction H2.
    + exists dtyp_bot. intuition... 
      econstructor... 
      dependent destruction H0. pick fresh X.
      inst_cofinites_with X.
      erewrite <- dtyp_subst_open_var; eauto...
      rewrite_env ((map (d_subst_tv_in_binding T2 X) nil) ++ E).
      eapply d_wft_typ_subst; eauto...
      econstructor; eauto.
    + exists (S1 ^^ᵈ T2). split; auto...
      pick fresh SX. inst_cofinites_with SX.
      erewrite <- dtyp_subst_open_stvar; eauto.
      rewrite <- (dtyp_subst_open_stvar SX T1 T2); eauto.
      rewrite_env ((map (d_subst_stv_in_binding T2 SX) nil) ++ E).
      apply d_sub_subst_stvar; auto...
      constructor; auto.
      inst_cofinites_for dwftyp_all; intros.
      * inst_cofinites_with X. 
        replace (S1 ^ᵈ X) with ({dtyp_var_f X /ₛᵈ X} (S1 ^^ᵈ (dtyp_svar X))).
        apply ftv_sins_dtyp_tvar_fstv_sin_dtyp; auto.
        erewrite dtyp_subst_open_stvar; auto.
      * inst_cofinites_with X.
        apply d_wf_typ_subst_tvar_stvar_cons; eauto...
        apply d_sub_dwft in H5; intuition.
    + inversion H6.
    + specialize (IHd_sub _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [C1 Hc1].
      specialize (d_inftapp_total _ _ _ H H3 H1). intros.
      inversion H4.
      -- exists C1; intuition...
      -- destruct H5 as [C2 Hc2]. 
         exists (dtyp_intersection C1 C2). split.
         constructor; intuition... 
         eapply d_inftapp_wft. eauto.
         eapply d_inftapp_wft. eauto.
         apply d_inftapp_intersection3; intuition...
    + specialize (IHd_sub _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [C1 Hc1].
      specialize (d_inftapp_total _ _ _ H H3 H1). intros.
      inversion H4.
      -- exists C1; intuition...
      -- destruct H5 as [C2 Hc2]. 
        exists (dtyp_intersection C2 C1). intuition. 
        apply d_sub_intersection3; intuition...
        eapply d_inftapp_wft. eauto.
        apply d_sub_intersection3; intuition...
        eapply d_inftapp_wft. eauto.
    + specialize (IHd_sub1 _ H H0 H1 (eq_refl _)).
      specialize (IHd_sub2 _ H H0 H1 (eq_refl _)).
      destruct IHd_sub1 as [C1].
      destruct IHd_sub2 as [C2].
      exists (dtyp_union C1 C2); intuition.
  - intros. apply dsub_intersection_inversion in H2. 
    intuition.
  - intros. apply dsub_intersection_inversion in H2. 
    intuition.
  - intros. dependent induction H1.
    + exists dtyp_bot. intuition...
      econstructor...
      apply d_inftapp_wft in H. 
      apply d_inftapp_wft in H0. intuition
      econstructor...
      apply d_inftapp_wft in H. intuition.
    + inversion H7.
    + specialize (IHd_inftapp1 _ H1_).
      specialize (IHd_inftapp2 _ H1_0).
      destruct IHd_inftapp1 as [C3].
      destruct IHd_inftapp2 as [C4].
      intuition.
      eapply d_inftapp_determinism in H4; eauto. subst.
      exists C3; intuition...
    + specialize (IHd_sub _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      apply d_inftapp_wft in H. intuition.
      eapply d_inftapp_total with (A:=S2) in H4...
      destruct H4.
      * destruct IHd_sub as [C3]. exists C3. intuition.
      * destruct IHd_sub as [C3]. destruct H4 as [C4].
        exists (dtyp_intersection C3 C4); intuition...
        eapply d_sub_intersection2... 
        apply d_inftapp_wft in H4. intuition.
    + specialize (IHd_sub _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      apply d_inftapp_wft in H. intuition.
      eapply d_inftapp_total with (A:=S1) in H4...
      destruct H4.
      * destruct IHd_sub as [C3]. exists C3. intuition.
      * destruct IHd_sub as [C3]. destruct H4 as [C4].
        exists (dtyp_intersection C4 C3); intuition...
        eapply d_sub_intersection3... 
        apply d_inftapp_wft in H4. intuition.
    + specialize (IHd_sub1 _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      destruct IHd_sub1 as [C3].
      destruct IHd_sub2 as [C4].
      exists (dtyp_union C3 C4). intuition...
  - intros. dependent induction H1.
    + exists dtyp_bot. 
      apply d_inftapp_wft in H.
      apply d_inftapp_wft in H0.
      intuition...
    + inversion H1.
    + specialize (IHd_sub _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      apply d_inftapp_wft in H. intuition.
      eapply d_inftapp_total with (A:=S2) in H4...
      destruct H4.
      * destruct IHd_sub as [C3]. exists C3. intuition.
      * destruct IHd_sub as [C3]. destruct H4 as [C4].
        exists (dtyp_intersection C3 C4); intuition...
        eapply d_sub_intersection2...
        apply d_inftapp_wft in H4. intuition.
    + specialize (IHd_sub _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      apply d_inftapp_wft in H. intuition.
      eapply d_inftapp_total with (A:=S1) in H4...
      destruct H4.
      * destruct IHd_sub as [C3]. exists C3. intuition.
      * destruct IHd_sub as [C3]. destruct H4 as [C4].
        exists (dtyp_intersection C4 C3); intuition...
        eapply d_sub_intersection3...
        apply d_inftapp_wft in H4. intuition.
    + specialize (IHd_inftapp1 _ H1). 
      destruct IHd_inftapp1 as [C3]. 
      exists C3. intuition...
      apply d_sub_union1; eauto...
      apply d_inftapp_wft in H0. intuition.
    + specialize (IHd_inftapp2 _ H1). 
      destruct IHd_inftapp2 as [C3]. 
      exists C3. intuition...
      apply d_sub_union2; eauto...
      apply d_inftapp_wft in H. intuition.
    + specialize (IHd_sub1 _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 IHd_inftapp1 IHd_inftapp2 (eq_refl _)).
      destruct IHd_sub1 as [C3].
      destruct IHd_sub2 as [C4].
      exists (dtyp_union C3 C4). intuition...
Qed.



Corollary d_inftapp_subsumption: forall E E' A1 A2 B1 C1,
  E ⊢ A1 ○ B1 ⇒⇒ C1 -> 
  E ⊢ A2 <: A1 ->
  d_subenv E' E -> 
  exists C2, E ⊢ C2 <: C1 /\ E' ⊢ A2 ○ B1 ⇒⇒ C2.
Admitted.

Hint Constructors d_infabs : typing.


Lemma d_infabs_wft : forall E A1 B1 C1,
  E ⊢ A1 ▹ B1 → C1 -> 
  ⊢ E /\ E ⊢ A1 /\ E ⊢ B1 /\ E ⊢ C1.
Proof.
  intros. induction H; intuition.
Qed.



(* @shengyi:todo *** *)
Theorem d_infabs_subsumption_same_env : forall E A1 B1 C1 A2, 
  E ⊢ A1 ▹ B1 → C1 -> 
  E ⊢ A2 <: A1 ->
  exists B2 C2, E ⊢ dtyp_arrow B2 C2 <: dtyp_arrow B1 C1 /\ E ⊢ A2 ▹ B2 → C2.
Proof with auto with typing.
  intros. generalize dependent A2. induction H; intros.
  - dependent induction H0...
    + exists dtyp_top dtyp_bot. auto...
    + exfalso. eapply d_sub_open_mono_bot_false; eauto.
    + specialize (IHd_sub H (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub H (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub1 H (eq_refl _)).
      specialize (IHd_sub2 H (eq_refl _)).
      destruct IHd_sub1 as [B1 [C1]].
      destruct IHd_sub2 as [B2 [C2]]. 
      exists (dtyp_intersection B1 B2) (dtyp_union C1 C2).
      destruct H0. destruct H1.
      split; intuition...
      dependent destruction H0. dependent destruction H1.
      eauto...
  - dependent induction H2...
    + exists dtyp_top dtyp_bot. dependent destruction H2.
      eauto...
    + exists S1 S2. intuition... 
      apply d_sub_dwft in H2_.   
      apply d_sub_dwft in H2_0.
      intuition...
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
      econstructor. eauto. eauto.
      econstructor; eauto...
      admit. auto.
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
    + specialize (IHd_sub1 _ _ H H0 H1 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub1 as [B2 [C2]].
      destruct IHd_sub2 as [B3 [C3]].
      exists (dtyp_intersection B2 B3) (dtyp_union C2 C3).
      split; intuition...
      dependent destruction H2. dependent destruction H4.
      eauto...
  - dependent induction H3.
    + exists dtyp_top dtyp_bot. 
      econstructor; eauto...
      admit.
    + assert (E ⊢ S1 ^^ᵈ T2 <: T1 ^^ᵈ T2). admit.
      specialize (IHd_infabs _ H7).
      destruct IHd_infabs as [B2 [C2]].
      exists B2 C2. intuition...
      econstructor; eauto... admit.
    + inversion H6.
    + specialize (IHd_sub T1 H H0 H1 H2 IHd_infabs (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2. intuition.
    + specialize (IHd_sub T1 H H0 H1 H2 IHd_infabs (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2. intuition.    
    + specialize (IHd_sub1 T1 H H0 H1 H2 IHd_infabs (eq_refl _)).
      specialize (IHd_sub2 T1 H H0 H1 H2 IHd_infabs (eq_refl _)).
      destruct IHd_sub1 as [B2 [C2]].
      destruct IHd_sub2 as [B3 [C3]].
      exists (dtyp_intersection B2 B3) (dtyp_union C2 C3).
      intuition...
      dependent destruction H5. dependent destruction H3.
      eauto...
  - apply dsub_intersection_inversion in H1. 
    intuition.
  - apply dsub_intersection_inversion in H1.
    intuition.
  - dependent induction H1.
    + exists dtyp_top dtyp_bot. intuition.
      econstructor; econstructor; eauto. 
      admit. admit.
    + inversion H1.
    + specialize (IHd_sub _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2. intuition.    
    + specialize (IHd_sub _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2. intuition.   
    + specialize (IHd_infabs1 _ H1). 
      destruct IHd_infabs1 as [B2 [C2]].
      exists B2 C2. intuition.
      dependent destruction H4. eauto...
      econstructor.
      eapply d_sub_intersection2; eauto. admit.
      eapply d_sub_union1; eauto. admit.
    + specialize (IHd_infabs2 _ H1).
      destruct IHd_infabs2 as [B2 [C2]].
      exists B2 C2. intuition.
      dependent destruction H4. eauto...
      econstructor. 
      eapply d_sub_intersection3; eauto. admit.
      eapply d_sub_union2; eauto. admit.
    + specialize (IHd_sub1 _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      specialize (IHd_sub2 _ _ H H0 IHd_infabs1 IHd_infabs2 (eq_refl _)).
      destruct IHd_sub1 as [B2 [C2]].
      destruct IHd_sub2 as [B3 [C3]].
      exists (dtyp_intersection B2 B3) (dtyp_union C2 C3).
      intuition...
      dependent destruction H1. dependent destruction H3.
      intuition...
Admitted.


Corollary d_inftabs_subsumption: forall E E' A1 A2 B1 C1,
  E ⊢ A1 ▹ B1 → C1 -> 
  E ⊢ A2 <: A1 ->
  d_subenv E' E -> 
  exists B2 C2, E ⊢ dtyp_arrow B2 C2 <: dtyp_arrow B1 C1 /\ E' ⊢ A2 ▹ B2 → C2.
Admitted.




Hint Extern 1 (_ < _) => lia : typing.
Hint Extern 1 (_ ⊢ _) => eapply d_subenv_wf_typ; eauto : typing.


Lemma d_exp_size_open_var_rec : forall e x n, 
  dexp_size e = dexp_size (open_dexp_wrt_dexp_rec n (dexp_var_f x) e)
with d_body_size_open_var_rec: forall b x n,
  d_body_size b = d_body_size (open_dbody_wrt_dexp_rec n (dexp_var_f x) b).
Proof.
  - intros. generalize dependent n. induction e; simpl; auto.
    + intros. destruct (lt_eq_lt_dec n n0).
      * destruct s; auto.
      * auto.
  - intros. generalize dependent n. induction b; simpl; auto.
Qed.


Lemma d_exp_size_open_var: forall e x,
  dexp_size e = dexp_size (open_dexp_wrt_dexp e (dexp_var_f x)).
Proof.
  intros. unfold open_dexp_wrt_dexp.
  apply d_exp_size_open_var_rec.
Qed.


Lemma d_exp_size_open_dtyp_rec : forall e T n, 
  dexp_size e = dexp_size (open_dexp_wrt_dtyp_rec n T e)
with d_body_size_open_dtyp_rec: forall b T n,
  d_body_size b = d_body_size (open_dbody_wrt_dtyp_rec n T b).
Proof.
  - intros. generalize dependent n. induction e; simpl; auto.
  - intros. generalize dependent n. induction b; simpl; auto.
Qed.


Lemma d_exp_size_open_dtyp: forall e T,
  dexp_size e = dexp_size (open_dexp_wrt_dtyp e T).
Proof.
  intros. unfold open_dexp_wrt_dexp.
  apply d_exp_size_open_dtyp_rec.
Qed.


Lemma d_chk_inf_wf_env: forall E e mode T,
  d_typing E e mode T ->
  ⊢ E.
Proof.
  intros. induction H; auto.
  - inst_cofinites_by L. inversion H1; auto.
  - inst_cofinites_by L. inversion H0; auto.
  - inst_cofinites_by L. inversion H1; auto.
Qed.



Theorem d_chk_inf_subsumption : forall n1 n2 n3 E E' e T1 mode,
  dexp_size e < n1 ->
  dmode_size mode < n2 ->
  dtyp_size T1 < n3 -> 
  d_typing E e mode T1 ->
  d_subenv E' E ->
    match mode with 
    | d_typingmode_chk => forall S1, E ⊢ T1 <: S1 -> E' ⊢ e ⇐ S1
    | d_typingmode_inf => exists S1, E ⊢ S1 <: T1 /\ E' ⊢ e ⇒ S1
    end.
Proof with auto with typing.
  intro n1; induction n1; intro n2; induction n2; intros n3; induction n3; intros * Hn1 Hn2 Hn3 Hty Hsubenv.
  - inversion Hn1.
  - inversion Hn1.
  - inversion Hn1. 
  - inversion Hn1.
  - inversion Hn2.
  - inversion Hn2.
  - inversion Hn3.
  - destruct mode.
    (* e => A *)
    + dependent destruction Hty; simpl in Hn1, Hn2, Hn3.
      * eapply d_subenv_same_var in Hsubenv as Hsubenvvar; eauto. 
        destruct Hsubenvvar as [S1 [Hbind Hsub]]. exists S1; intuition.
        constructor. auto...
        eapply d_subenv_wf_env with (E:=E); eauto.
        auto.         
      (* e : A => A *)
      * exists T1. split; auto. apply dsub_refl; auto.
        admit.
        econstructor. eapply d_subenv_wf_typ; eauto.
        refine (IHn1 _ _ _ _ _ _ _ _ _ _  Hty _ _ _); eauto... simpl in *.
        apply dsub_refl; auto.
        admit.
      (* () => 1 *)
      * exists dtyp_unit. split; auto.
        econstructor. eapply d_subenv_wf_env; eauto.
      (* e1 e2 => A *)
      * eapply IHn1 in Hty1; eauto...
        destruct Hty1 as [A2]. inversion H0.
        eapply d_inftabs_subsumption in H; eauto.
        destruct H as [B2 [C2]].
        exists C2; intuition.
        dependent destruction H0...
        dependent destruction H0...
        econstructor; eauto...
        refine (IHn1 _ _ _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
      (* d_infabs_subsumption @shengyi:todo *** *)
      (* /\ a. e : A => forall a. A *)
      * exists (dtyp_all T1); split.
        -- eapply dsub_refl; auto.
           admit.
        -- dependent destruction H. pick fresh X and apply d_typing_inftabs. auto...
           intros. inst_cofinites_with X.
           refine (IHn1 _ _ _ _ _ _ _ _ _ _ H1 _ _ _); eauto...
           simpl. rewrite <- d_exp_size_open_dtyp; lia.
           apply dsub_refl. admit. auto. 
      (* e @T *)
      * eapply IHn1 in Hty; eauto...
        destruct Hty as [A1 [Hsuba1 Hinfa1]].
        eapply d_inftapp_subsumption in H0; eauto.
        destruct H0 as [C2 Hc2].
        exists C2. intuition... 
        econstructor; eauto...
    (* e <= *)
    + dependent destruction Hty; simpl in Hn1, Hn2, Hn3.
      (* \x. e <= Top *)
      * intros. 
        dependent induction H0; eauto...
        -- eapply d_typing_chkabstop with (L:=L `union` dom E)... intros.
           inst_cofinites_with x.
           simpl in H.
           refine (IHn1 _ _ _ _ _ _ _ _ _ _ H _ _ _); eauto...
           rewrite <- d_exp_size_open_var. lia.
           econstructor; auto. 
           econstructor. econstructor; eauto.
           econstructor. 
      (* \x. e <= T1 -> T2 *)
      * intros. 
        assert (d_wft_ord S1) as Hwford. admit. (* trivial * *)
        induction Hwford.
        -- dependent destruction H1.
           ++ inst_cofinites_for d_typing_chkabstop. intros.
              inst_cofinites_with x.
              refine (IHn1 _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
              rewrite <- d_exp_size_open_var. lia.
              econstructor; eauto. admit.
           ++ inst_cofinites_for d_typing_chkabs.
              admit. intros. inst_cofinites_with x.
              refine (IHn1 _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
              rewrite <- d_exp_size_open_var. lia.
              admit. (* sub_weakening ★ *)
           ++ inversion H2.
           ++ inversion H3.
           ++ inversion H3.
        -- dependent destruction H1; auto... 
        -- dependent destruction H1; auto... 
      (* e <= forall a. A *) 
      (*  * admit. ignore for now *** *)
      (* e <= A *)
      * intros.
        eapply IHn2 in Hty; eauto.
        destruct Hty as [S2 [Hsub Hinf]].
        apply d_typing_chksub with (S1 := S2); auto.
        apply sub_transitivity with (S1 := T1); auto... 
        eapply denvsub_sub; eauto. apply sub_transitivity with (S1 := S1); auto...
        eapply denvsub_sub; eauto.
        simpl. lia.
      * intros. assert (d_wft_ord S0) as Hwford. 
        admit. (* trivial * *)
        induction Hwford.
        -- dependent destruction H.
           ++ dependent destruction H0. refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ inversion H1.
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
           ++ inversion H1.
           ++ inversion H1.
        -- dependent destruction H; auto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...
        -- dependent destruction H.
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty1 _ _ _); eauto...  
           ++ refine (IHn3 _ _ _ _ _ _ _ _ Hty2 _ _ _); eauto...  
           ++ eauto... 
           ++ eauto... 
      * intros.
        refine (IHn3 _ _ _ _ _ _ _ _ Hty _ _ _); eauto...
        apply dsub_union_inversion in H0. intuition.
      * intros. 
        refine (IHn3 _ _ _ _ _ _ _ _ Hty _ _ _); eauto...
        apply dsub_union_inversion in H0. intros. intuition.
Admitted.


Corollary d_chk_subsumption : forall E e T1 S1,  
  ⊢ E ->
  E ⊢ e ⇐ S1 -> 
  E ⊢ S1 <: T1 -> 
  E ⊢ e ⇐ T1.
Proof.
  intros.
  refine (d_chk_inf_subsumption _ _ _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto.
  now apply d_subenv_refl.
Qed.
