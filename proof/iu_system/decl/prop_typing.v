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


(* 

Theorem ld_sub_weakening: 
  forall G1 G2 G3 t1 t2, 
  G1 ,, G3 ⊢ t1 <: t2 -> ⊢ G1 ,, G2 ,, G3 -> 
  G1 ,, G2 ,, G3 ⊢ t1 <: t2.
Proof.
  intros.
  dependent induction H; auto.
  - constructor; auto. eapply ld_in_context_weakenning. auto.
  - constructor; auto. eapply ld_wf_type_weakening; eauto.
  - apply ld_sub_intersection_l2. auto. eapply ld_wf_type_weakening; eauto.
  - apply ld_sub_union_r1. auto. eapply ld_wf_type_weakening; eauto.
  - apply ld_sub_union_r2. auto. eapply ld_wf_type_weakening; eauto.
  - eapply ld_sub_foralll with (t:=t); auto.
    eapply ld_wf_mtype_weakening; auto.
  - pick fresh x and apply ld_sub_forallr for weakening.
    replace (G1,, G2,, G3, x) with (G1,, G2,, (G3, x)) by auto.
    eapply H0; auto. constructor; auto.
Qed.


Theorem ld_in_context_other : forall G1 G2 x x', 
  x <> x' -> ld_in_context x (G1, x',,G2) -> ld_in_context x (G1,,G2).
Proof.
  intros.
  induction G2.
  - simpl in *. dependent destruction H0.
    + contradiction.
    + auto.
  - simpl in *. dependent destruction H0.
    + econstructor.
    + constructor. auto. 
Qed.


Ltac rewrite_subst_open_var :=
  repeat
    match goal with 
      | _ : _ |-  context [ ([?e /ᵈ ?x] ?A) ^^ᵈ `ᵈ ?x' ] => 
        replace (`ᵈ x') with ([e /ᵈ x] `ᵈ x') by (apply subst_ld_type_fresh_eq; auto)
    end; repeat rewrite <- subst_ld_type_open_ld_type_wrt_ld_type by auto.

*)


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
  d_subenv E' E ->
  x ~ T1 ∈ E ->
  exists S1, x ~ S1 ∈ E' /\ E ⊢ S1 <: T1.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
  - inversion H0; auto.
    + inversion H1.
    + specialize (IHd_subenv H1).
      admit.
  - inversion H0; auto.
    + inversion H1.
    + specialize (IHd_subenv H1).
      admit.
Admitted.

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


(* Lemma d_subenv_wf_typ : forall E T, 
  E ⊢ T -> 
  forall E', 
    d_subenv E' E ->
    E' ⊢ T.
Proof.
  intros E T H. induction H; intros; auto.
  - econstructor. 
    eapply d_subenv_same_tvar; eauto.
  - econstructor.
    eapply d_subenv_same_stvar; eauto.
  - eapply dwftyp_all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed. *)

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
      eapply d_subenv_wf_typ; eauto. auto.
    + erewrite <- d_subenv_same_dom; auto.
Qed.

Lemma denvsub_sub: forall E S1 T1, 
  E ⊢ S1 <: T1 -> forall E', d_subenv E' E -> E' ⊢ S1 <: T1.
Proof.
  intros E S1 T1 Hsub.
  induction Hsub.
  - econstructor. eapply d_subenv_wf_typ; eauto.
  - econstructor. eapply d_subenv_wf_typ; eauto.
  - econstructor.
  - econstructor. eapply d_subenv_wf_typ; eauto.
  - econstructor. eapply d_subenv_wf_typ; eauto.
  - econstructor; auto.
  - intros. econstructor; auto.
    intros. inst_cofinites_with SX. 
    specialize (H2 (SX ~ dbind_stvar_empty ++ E')).
    assert (d_subenv (SX ~ dbind_stvar_empty ++ E') (SX ~ dbind_stvar_empty ++ E)). {
      constructor. auto. }
    specialize (H2 H5).
    auto.
  - intros. eapply d_sub_alll with (T2:=T2); auto.
    eapply d_subenv_wf_typ; eauto.
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


Hint Constructors d_subenv: typing.
Hint Constructors d_typing : typing.
Hint Resolve d_subenv_wf_typ : typing.
Hint Resolve d_subenv_wf_env : typing.
Hint Resolve d_wft_typ_subst : typing.
Hint Resolve d_wf_env_subst_tvar_typ : typing.
Hint Resolve bind_typ_subst : typing. 
Hint Resolve dwf_typ_dlc_type : typing.


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


Fixpoint dexp_size (e:dexp) : nat :=
  match e with 
  | dexp_unit => 1
  | dexp_top => 1
  | dexp_var_f _ => 1
  | dexp_var_b _ => 1
  | dexp_abs e1 => 1 + dexp_size e1
  | dexp_app e1 e2 => dexp_size e1 + dexp_size e2 
  | dexp_anno e1 _ => 1 + dexp_size e1
  | dexp_tapp e1 _ => 1 + dexp_size e1
  | dexp_tabs (dbody_anno e1 T) => 1 + dexp_size e1
  end.


Fixpoint dtyp_size (T:dtyp) : nat :=
  match T with 
  | dtyp_intersection T1 T2 => dtyp_size T1 + dtyp_size T2 + 1
  | dtyp_union T1 T2 => dtyp_size T1 + dtyp_size T2 + 1
  | _ => 0
  end.
  

Theorem d_infabs_subsumption : forall E T1 T2 S1, d_infabs E T1 T2 -> E ⊢ S1 <:T1 ->
  exists S2, d_inftapp E S1 T2 S2.
Proof.
Admitted.


Theorem d_inftapp_subsumption : forall E T1 T2 T3 S1, d_inftapp E T1 T2 T3 -> E ⊢ S1 <:T1 ->
  exists S2, d_inftapp E S1 T2 S2.
Proof.
Admitted.

Hint Extern 1 (_ < _) => lia : typing.
Hint Extern 1 (_ ⊢ _) => eapply d_subenv_wf_typ; eauto : typing.

Theorem dchk_dinf_subsumption : forall n1 n2 n3 E E' e T1 mode,
  dexp_size e < n1 ->
  dmode_size mode < n2 ->
  dtyp_size T1 < n3 -> 
  d_typing E e mode T1 ->
  d_subenv E' E ->
    match mode with 
    | d_typingmode_chk => forall S1, E ⊢ T1 <: S1 -> d_typing E' e d_typingmode_chk S1
    | d_typingmode_inf => exists S1, E ⊢ S1 <: T1 /\ d_typing E' e d_typingmode_inf S1
    end.
Proof with auto with typing.
  intro n1; induction n1; intro n2; induction n2; intros n3; induction n3; intros.
  - inversion H.
  - inversion H.
  - inversion H. 
  - inversion H.
  - inversion H0.
  - inversion H0.
  - inversion H1.
  - destruct mode.
    (* e => A *)
    + dependent destruction H2.
      * eapply d_subenv_same_var in H3; eauto. 
        destruct H3 as [S1 [Hbind Hsub]]. exists S1; intuition.
        constructor. auto...
        admit. (* trivial *)
        auto.         
      (* e : A => A *)
      * exists T1. split; auto. apply dsub_refl; auto.
        econstructor. eapply d_subenv_wf_typ; eauto.
        simpl in H.
        refine (IHn1 _ _ _ _ _ _ _ _ _ _ H3 _ _ _); eauto...
        apply dsub_refl; auto.
      (* () => 1 *)
      * exists dtyp_unit. split; auto.
        econstructor. eapply d_subenv_wf_env; eauto.
      (* e1 e2 => A *)
      * admit.
      (* /\ a. e : A => forall a. A *)
      * exists (dtyp_all T1); split.
        -- eapply dsub_refl; auto.
        -- eapply d_typing_inftabs with (L:=L); auto...
           intros. inst_cofinites_with X.
           refine (IHn1 _ _ _ _ _ _ _ _ _ _ H3 _ _ _); eauto...
           admit. (* maybe some minor problem with exp_size def ** *)
           admit. (* wft * *)
      (* e @T *)
      * admit.
    (* e <= *)
    + dependent destruction H2.
      (* \x. e <= Top *)
      * intros. 
        dependent induction H4; eauto...
        -- eapply d_typing_chkabstop with (L:=L). intros.
           inst_cofinites_with x.
           simpl in H.
           refine (IHn1 _ _ _ _ _ _ _ _ _ _ H2 _ _ _); eauto...
           admit. (* exp_size  ** *)
      (* \x. e <= T1 -> T2 *)
      * intros. 
        assert (d_wft_ord S1). admit. (* trivial * *)
        induction H6.
        -- dependent destruction H5.
           ++ admit.
           ++ inst_cofinites_for d_typing_chkabs.
              admit. intros. inst_cofinites_with x.
              refine (IHn1 _ _ _ _ _ _ _ _ _ _ H3 _ _ _); eauto...
              admit. (* exp_size ** *)
              admit. (* sub_weakening *)
           ++ inversion H6.
           ++ inversion H7.
        -- dependent destruction H5; auto... 
        -- dependent destruction H5; auto... 
      (* e <= forall a. A *) 
      * admit. (* ignore for now *** *)
      (* e <= A *)
      * intros.
        simpl in H0. assert (dmode_size d_typingmode_inf < n2) by (simpl; lia).
        assert (dtyp_size S1 < S (dtyp_size S1)) by lia.
        specialize (IHn2 _ _ _ _ _ _ H H6 H7 H2 H4).
        simpl in IHn2.
        destruct IHn2 as [S2 [Hsub Hinf]].
        apply d_typing_chksub with (S1 := S2); auto.
        apply sub_transitivity with (S1 := T1); auto... 
        admit. (* add |- E to the premise * *)
        eapply denvsub_sub; eauto. apply sub_transitivity with (S1 := S1); auto. 
        admit. (* add |- E to the premise * *)
        eapply denvsub_sub; eauto.
      * intros. assert (d_wft_ord S0). 
        admit. (* trivial * *)
        induction H4.
        -- dependent destruction H2; simpl in H1.
           ++ dependent destruction H2. refine (IHn3 _ _ _ _ _ _ _ _ H2_ _ _ _); eauto...
           ++ inversion H4.
           ++ refine (IHn3 _ _ _ _ _ _ _ _ H2_ _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ H2_0 _ _ _); eauto...
           ++ inversion H5.
           ++ inversion H5.
        -- simpl in H1. dependent destruction H2; auto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ H2_ _ _ _); eauto...
           ++ refine (IHn3 _ _ _ _ _ _ _ _ H2_0 _ _ _); eauto...
        -- simpl in H1. dependent destruction H2.
           ++ refine (IHn3 _ _ _ _ _ _ _ _ H2_ _ _ _); eauto...  
           ++ refine (IHn3 _ _ _ _ _ _ _ _ H2_0 _ _ _); eauto...  
           ++ eauto... 
           ++ eauto... 
      * intros. simpl in H1.
        refine (IHn3 _ _ _ _ _ _ _ _ H2 _ _ _); eauto...
        specialize (dsub_union_inversion _ _ _ _ H5). intros. intuition.
      * intros. simpl in H1.
        refine (IHn3 _ _ _ _ _ _ _ _ H2 _ _ _); eauto...
        specialize (dsub_union_inversion _ _ _ _ H5). intros. intuition.
Admitted.


Corollary dchk_subsumption : forall E e T1 S1,  
  d_typing E e d_typingmode_chk T1 ->
  E ⊢ T1 <: S1 -> 
  d_typing E e d_typingmode_chk S1.
Proof.
Admitted.
