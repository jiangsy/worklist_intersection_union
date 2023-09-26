Require Import ln_utils.
Require Import decl.def_ott.
Require Import decl.def_extra.
Require Import decl.notations.
Require Import decl.prop_basic.
Require Import decl.prop_subtyping.

Require Import systemf.def_ott.
Require Import systemf.prop_ln.

Notation "E ⊢ e : T" :=
    (typing E e T) 
      (at level 65, e at next level, no associativity) : type_scope.

Fixpoint trans_typ (T : dtyp) : ftyp :=
    match T with
    | dtyp_unit => ftyp_unit
    | dtyp_top => ftyp_unit
    | dtyp_bot => ftyp_all (ftyp_var_b 0)
    | dtyp_var_b n => ftyp_var_b n
    | dtyp_var_f X => ftyp_var_f X
    | dtyp_svar SX => ftyp_var_f SX
    | dtyp_arrow T1 T2 => ftyp_arrow (trans_typ T1) (trans_typ T2)
    | dtyp_all T => ftyp_all (trans_typ T)
    | dtyp_union T1 T2 => ftyp_sum (trans_typ T1) (trans_typ T2)
    | dtyp_intersection T1 T2 => ftyp_prod (trans_typ T1) (trans_typ T2) 
    end.

Notation "⟦  T  ⟧ₜ" := (trans_typ T) (at level 0, no associativity) : type_scope.

Fixpoint trans_env (E : denv) : fenv :=
    match E with
    | nil => nil
    | (X, dbind_tvar_empty) :: E' => (X, bind_tvar_empty) :: trans_env E'
    | (X, dbind_stvar_empty) :: E' => (X, bind_tvar_empty) :: trans_env E'
    | (X, (dbind_typ T)) :: E' => (X, (bind_typ (trans_typ T))) :: trans_env E'
    end.

Notation "⟦ E ⟧ₑ" := (trans_env E) (at level 0, no associativity) : type_scope.

Lemma trans_typ_open_dtyp_wrt_dtyp_rec : forall T1 T2 n,
    trans_typ (open_dtyp_wrt_dtyp_rec n T2 T1) = open_ftyp_wrt_ftyp_rec n (trans_typ T2)  (trans_typ T1).
Proof.
    intros T1. induction T1; auto; intros; simpl.
    - destruct (lt_eq_lt_dec n n0) as [[? | ?] | ?] eqn:E; auto.
    - rewrite IHT1_1. rewrite IHT1_2. auto.
    - rewrite IHT1. auto.
    - rewrite IHT1_1. rewrite IHT1_2. auto.
    - rewrite IHT1_1. rewrite IHT1_2. auto.
Qed.

Theorem trans_typ_open_dtyp_wrt_dtyp : forall T1 T2,
    trans_typ (T1 ^^ᵈ T2) = open_ftyp_wrt_ftyp (trans_typ T1) (trans_typ T2).
Proof.
    unfold open_dtyp_wrt_dtyp. unfold open_ftyp_wrt_ftyp.
    intros. apply trans_typ_open_dtyp_wrt_dtyp_rec.
Qed.

Theorem trans_typ_lc_ftyp : forall (T:dtyp),
    lc_dtyp T -> lc_ftyp (trans_typ T).
Proof.
    intros. induction H; simpl; eauto.
    - apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. eauto.
    - apply lc_ftyp_all. intros.
      rewrite <- trans_typ_open_dtyp_wrt_dtyp with (T2 := (dtyp_var_f X)).
      auto.
Qed.

Hint Resolve trans_typ_lc_ftyp : safety.

Theorem trans_env_notin_dom : forall E X,
    X `notin` dom E -> X `notin` dom (trans_env E).
Proof.
    intros E. induction E; auto.
    intros X H. destruct a. destruct b; simpl in *; auto.
Qed.

Hint Resolve trans_env_notin_dom : safety.

Theorem trans_env_tvar_in : forall (E:denv) X,
    X ~ ▫ ∈ E -> binds X bind_tvar_empty (trans_env E).
Proof.
    intros E. induction E; auto.
    intros X H. inversion H; subst.
    - simpl. auto.
    - destruct a. destruct b; simpl in *; auto.
Qed.

Theorem trans_env_svar_in : forall (E:denv) X,
    X ~ ▪ ∈ E -> binds X bind_tvar_empty (trans_env E).
Proof.
    intros E. induction E; auto.
    intros X H. inversion H; subst.
    - simpl. auto.
    - destruct a. destruct b; simpl in *; auto.
Qed.

Hint Constructors wf_env : safety.

Theorem trans_typ_wf : forall E T,
    E ⊢ T -> wf (trans_env E) (trans_typ T).
Proof.
    intros. induction H; simpl; eauto.
    - apply wf_typ_all with (L:=dom E).
      intros. apply trans_env_notin_dom in H.
      unfold open_ftyp_wrt_ftyp. simpl. auto.
    - apply wf_typ_var. apply trans_env_tvar_in. auto.
    - apply wf_typ_var. apply trans_env_svar_in. auto.
    - apply wf_typ_all with (L:= L `union` dom E). 
      intros. inst_cofinites_with X.
      rewrite trans_typ_open_dtyp_wrt_dtyp in H1. auto.
Qed.

Hint Resolve trans_typ_wf : safety.

Theorem trans_env_wf_env : forall E,
    ⊢ E -> wf_env (trans_env E).
Proof with eauto with safety.
    intros. induction H; simpl; eauto;
    try solve [apply trans_env_notin_dom in H0; apply wf_env_sub; auto].
    apply wf_env_typ; auto with safety.
Qed.

Hint Resolve trans_env_wf_env : safety.

Inductive sub_elab : denv -> dtyp -> dtyp -> fexp -> Prop :=
 | sub_elab_top : forall (E:denv) (S1:dtyp),
     dwf_env E ->
     dwf_typ E S1 ->
     sub_elab E S1 dtyp_top (fexp_abs (trans_typ S1) fexp_unit)
 | sub_elab_bot : forall (E:denv) (T1:dtyp),
     dwf_env E ->
     dwf_typ E T1 ->
     sub_elab E dtyp_bot T1 (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_tapp (fexp_var_b 0) (trans_typ T1)))
 | sub_elab_unit : forall (E:denv),
     dwf_env E ->
     sub_elab E dtyp_unit dtyp_unit (fexp_abs ftyp_unit (fexp_var_b 0))
 | sub_elab_tvar : forall (E:denv) (X:typvar),
     dwf_env E ->
     dwf_typ E (dtyp_var_f X) ->
     sub_elab E (dtyp_var_f X) (dtyp_var_f X) (fexp_abs (ftyp_var_f X) (fexp_var_b 0))
 | sub_elab_stvar : forall (E:denv) (SX:stypvar),
     dwf_env E ->
     dwf_typ E (dtyp_svar SX) ->
     sub_elab E (dtyp_svar SX) (dtyp_svar SX) (fexp_abs (ftyp_var_f SX) (fexp_var_b 0))
 | sub_elab_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp) (C1 C2:fexp),
     sub_elab E T1 S1 C1 ->
     sub_elab E S2 T2 C2 ->
     sub_elab E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
        (fexp_abs (ftyp_arrow (trans_typ S1) (trans_typ S2))
                  (fexp_abs (trans_typ T1)
                            (fexp_app C2
                                      (fexp_app (fexp_var_b 1)
                                                (fexp_app C1 (fexp_var_b 0))))))
 | sub_elab_all : forall (L:vars) (E:denv) (S1 T1:dtyp) (C:fexp),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> sub_elab  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) C ) ->
     sub_elab E (dtyp_all S1) (dtyp_all T1)
        (fexp_abs (trans_typ (dtyp_all S1)) (fexp_tabs (fexp_app C (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0)))))
 | sub_elab_alll : forall (L:vars) (E:denv) (S1 T1 T2:dtyp) (C:fexp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 -> 
     ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S1   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     sub_elab E  (open_dtyp_wrt_dtyp  S1   T2 )  T1 C ->
     sub_elab E (dtyp_all S1) T1
        (fexp_abs (trans_typ (dtyp_all S1)) (fexp_app C (fexp_tapp (fexp_var_b 0) (trans_typ T2))))
 | sub_elab_intersection1 : forall (E:denv) (S1 T1 T2:dtyp) (C1 C2:fexp),
     sub_elab E S1 T1 C1 ->
     sub_elab E S1 T2 C2 ->
     sub_elab E S1 (dtyp_intersection T1 T2)
        (fexp_abs (trans_typ S1)
                  (fexp_pair (fexp_app C1 (fexp_var_b 0))
                             (fexp_app C2 (fexp_var_b 0))))
 | sub_elab_intersection2 : forall (E:denv) (S1 S2 T1:dtyp) (C:fexp),
     sub_elab E S1 T1 C ->
     dwf_typ E S2 ->
     sub_elab E (dtyp_intersection S1 S2) T1
        (fexp_abs (trans_typ (dtyp_intersection S1 S2)) (fexp_app C (fexp_proj1 (fexp_var_b 0))))
 | sub_elab_intersection3 : forall (E:denv) (S1 S2 T1:dtyp) (C:fexp),
     sub_elab E S2 T1 C ->
     dwf_typ E S1 ->
     sub_elab E (dtyp_intersection S1 S2) T1
        (fexp_abs (trans_typ (dtyp_intersection S1 S2)) (fexp_app C (fexp_proj2 (fexp_var_b 0))))
 | sub_elab_union1 : forall (E:denv) (S1 T1 T2:dtyp) (C:fexp),
     sub_elab E S1 T1 C ->
     dwf_typ E T2 ->
     sub_elab E S1 (dtyp_union T1 T2)
        (fexp_abs (trans_typ S1) (fexp_inl (fexp_app C (fexp_var_b 0))))
 | sub_elab_union2 : forall (E:denv) (S1 T1 T2:dtyp) (C:fexp),
     sub_elab E S1 T2 C ->
     dwf_typ E T1 ->
     sub_elab E S1 (dtyp_union T1 T2)
        (fexp_abs (trans_typ S1) (fexp_inr (fexp_app C (fexp_var_b 0))))
 | sub_elab_union3 : forall (E:denv) (S1 S2 T1:dtyp) (C1 C2:fexp),
     sub_elab E S1 T1 C1 ->
     sub_elab E S2 T1 C2 ->
     sub_elab E (dtyp_union S1 S2) T1
     (fexp_abs (trans_typ (dtyp_union S1 S2)) (fexp_case (fexp_var_b 0) (fexp_app C1 (fexp_var_b 0)) (fexp_app C2 (fexp_var_b 0)))).

Notation "E ⊢ A <: B ↪ C" := (sub_elab E A B C) (at level 65, A at next level, no associativity) : type_scope.

Hint Constructors sub_elab : safety.
Hint Constructors typing : safety.

Theorem sub_elab_sound: forall E A B C,
    sub_elab E A B C -> d_sub E A B.
Proof.
    intros. induction H; eauto.
Qed.

Theorem sub_elab_complete: forall E A B,
    d_sub E A B -> exists C, sub_elab E A B C.
Proof.
    intros. induction H.
    - eauto with safety.
    - eauto with safety.
    - eauto with safety.
    - eauto with safety.
    - eauto with safety.
    - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
    - inst_cofinites_by L. inversion H2. eauto with safety.
      exists (fexp_abs (trans_typ (dtyp_all S1)) (fexp_tabs (fexp_app x0 (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0))))).
      apply sub_elab_all with (L := L).
      + intros. admit.
      + intros. admit.
      + intros. admit.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
Admitted.

Lemma open_fexp_wrt_fexp_rec_lc_fexp : forall e2 e1 n,
  lc_fexp e2 -> open_fexp_wrt_fexp_rec n e1 e2 = e2.
Proof.
    intros. apply open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp.
    apply degree_fexp_wrt_fexp_O.
    apply degree_fexp_wrt_fexp_of_lc_fexp. auto.
Qed.

Lemma open_fexp_wrt_ftyp_rec_lc_fexp : forall e T n,
  lc_fexp e -> open_fexp_wrt_ftyp_rec n T e = e.
Proof.
    intros. apply open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp.
    apply degree_fexp_wrt_ftyp_O.
    apply degree_fexp_wrt_ftyp_of_lc_fexp. auto.
Qed.

Theorem sub_elab_lc_fexp : forall E A B C,
    sub_elab E A B C -> lc_fexp C.
Proof.
    intros. induction H.
    - eauto with safety.
    - apply lc_fexp_abs.
    + apply lc_ftyp_all. intros.
        unfold open_ftyp_wrt_ftyp. simpl. auto.
    + intros.  unfold open_fexp_wrt_fexp. simpl.
        eauto with safety.
    - apply lc_fexp_abs; auto. 
      intros. unfold open_fexp_wrt_fexp. simpl. auto.
    - apply lc_fexp_abs; auto. 
      intros. unfold open_fexp_wrt_fexp. simpl. auto.
    - apply lc_fexp_abs; auto. 
      intros. unfold open_fexp_wrt_fexp. simpl. auto.
    - apply sub_elab_sound in H. apply sub_elab_sound in H0.
      apply d_sub_dwft in H. apply d_sub_dwft in H0.
      destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
      apply lc_fexp_abs.
      + apply lc_ftyp_arrow; eauto with safety.
      + intros. unfold open_fexp_wrt_fexp. simpl.
        rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply lc_fexp_abs; eauto with safety.
        intros. unfold open_fexp_wrt_fexp. simpl.
        rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    - admit.
    - admit.
    - apply sub_elab_sound in H. apply sub_elab_sound in H0.
      apply d_sub_dwft in H. apply d_sub_dwft in H0.
      destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
      apply lc_fexp_abs; eauto with safety.
      intros. unfold open_fexp_wrt_fexp. simpl.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    - apply sub_elab_sound in H.
      apply d_sub_dwft in H.
      destruct H as [_ [? ?]].
      apply lc_fexp_abs; eauto with safety.
      intros. unfold open_fexp_wrt_fexp. simpl.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    - apply sub_elab_sound in H.
      apply d_sub_dwft in H.
      destruct H as [_ [? ?]].
      apply lc_fexp_abs; eauto with safety.
      intros. unfold open_fexp_wrt_fexp. simpl.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    - apply sub_elab_sound in H.
      apply d_sub_dwft in H.
      destruct H as [_ [? ?]].
      apply lc_fexp_abs; eauto with safety.
      intros. unfold open_fexp_wrt_fexp. simpl.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    - apply sub_elab_sound in H.
      apply d_sub_dwft in H.
      destruct H as [_ [? ?]].
      apply lc_fexp_abs; eauto with safety.
      intros. unfold open_fexp_wrt_fexp. simpl.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    - apply sub_elab_sound in H. apply sub_elab_sound in H0.
      apply d_sub_dwft in H. apply d_sub_dwft in H0.
      destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
      apply lc_fexp_abs; eauto with safety.
      intros. unfold open_fexp_wrt_fexp. simpl.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply lc_fexp_case; eauto with safety; intros;
      unfold open_fexp_wrt_fexp; simpl;
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
Admitted.

Theorem sub_sound_f : forall E A B C,
    sub_elab E A B C -> typing (trans_env E) C (ftyp_arrow (trans_typ A) (trans_typ B)).
Proof with eauto with safety.
    intros. induction H; simpl; eauto.
    - apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_tapp with (T1:=ftyp_var_b 0); eauto with safety.
      apply typing_var; eauto.
      apply wf_env_typ; eauto with safety.
      apply trans_typ_wf with (E:=E) (T:=dtyp_all (dtyp_var_b 0)).
      apply dwftyp_all with (L:=dom E); unfold open_dtyp_wrt_dtyp; simpl; auto.
    - apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; eauto.
      apply wf_env_typ; eauto with safety.
    - apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; eauto.
      apply wf_env_typ; eauto with safety.
      apply trans_typ_wf with (T:=dtyp_var_f X); auto.
    - apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; eauto.
      apply wf_env_typ; eauto with safety.
      apply trans_typ_wf with (T:=dtyp_svar SX); auto.
    - apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_abs with (L:=dom E `union` singleton x).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc1: lc_fexp C1).
      { apply sub_elab_lc_fexp in H. auto. }
      assert (Hlc2: lc_fexp C2).
      { apply sub_elab_lc_fexp in H0. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (T1:=trans_typ S2).
      + admit. (* weaken *)
      + apply typing_app with (T1:=trans_typ S1).
        * apply typing_var; auto.
          admit. (* wf *)
        * apply typing_app with (T1:=trans_typ T1).
          -- admit. (* weaken *)
          -- apply typing_var; auto.
             admit. (* wf *)
    - apply typing_abs with (L:=L `union` dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_tabs with (L:=L `union` dom E `union` singleton x).
      unfold open_fexp_wrt_ftyp. simpl. intros.
      inst_cofinites_with X.
      assert (Hlc: lc_fexp C).
      { apply sub_elab_lc_fexp in H1. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      repeat rewrite open_fexp_wrt_ftyp_rec_lc_fexp;
      try rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
      replace (ftyp_var_f X) with (trans_typ (dtyp_svar X)); auto.
      apply typing_app with (T1:=trans_typ (S1 ^^ᵈ dtyp_svar X)).
      + rewrite <- trans_typ_open_dtyp_wrt_dtyp with (T1:=T1) (T2:=dtyp_svar X).
        admit. (* weaken *)
      + rewrite trans_typ_open_dtyp_wrt_dtyp.
        apply typing_tapp; eauto with safety.
        apply typing_var; auto.
        admit. (* wf *)
    - apply typing_abs with (L:=L `union` dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp C).
      { apply sub_elab_lc_fexp in H5. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (T1:=trans_typ (S1 ^^ᵈ T2)).
      + admit. (* weaken *)
      + rewrite trans_typ_open_dtyp_wrt_dtyp.
        apply typing_tapp; eauto with safety.
        apply typing_var; auto.
        admit. (* wf *)
    - apply typing_abs with (L:=dom E).
      intros. unfold open_fexp_wrt_fexp. simpl.
      assert (Hlc1: lc_fexp C1).
      { apply sub_elab_lc_fexp in H. auto. }
      assert (Hlc2: lc_fexp C2).
      { apply sub_elab_lc_fexp in H0. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_pair.
      + apply typing_app with (T1:=trans_typ S1).
        * admit. (* weaken *)
        * apply typing_var; auto.
          admit. (* wf *)
      + apply typing_app with (T1:=trans_typ S1).
        * admit. (* weaken *)
        * apply typing_var; auto.
          admit. (* wf *)
    - apply typing_abs with (L:=dom E).
      intros. unfold open_fexp_wrt_fexp. simpl.
      assert (Hlc: lc_fexp C).
      { apply sub_elab_lc_fexp in H. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (T1:=trans_typ S1).
      + admit. (* weaken *) 
      + apply typing_proj1 with (T2:=trans_typ S2).
        apply typing_var; auto.
        admit. (* wf *)
    - apply typing_abs with (L:=dom E).
      intros. unfold open_fexp_wrt_fexp. simpl.
      assert (Hlc: lc_fexp C).
      { apply sub_elab_lc_fexp in H. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (T1:=trans_typ S2).
      + admit. (* weaken *) 
      + apply typing_proj2 with (T1:=trans_typ S1).
        apply typing_var; auto.
        admit. (* wf *)
    - apply typing_abs with (L:=dom E).
      intros. unfold open_fexp_wrt_fexp. simpl.
      assert (Hlc: lc_fexp C).
      { apply sub_elab_lc_fexp in H. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_inl.
      + eapply typing_app with (T1:=trans_typ S1).
        * admit. (* weaken *)
        * apply typing_var; auto.
          admit. (* wf *)
      + admit. (* wf *)
    - apply typing_abs with (L:=dom E).
      intros. unfold open_fexp_wrt_fexp. simpl.
      assert (Hlc: lc_fexp C).
      { apply sub_elab_lc_fexp in H. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_inr.
      + eapply typing_app with (T1:=trans_typ S1).
        * admit. (* weaken *)
        * apply typing_var; auto.
          admit. (* wf *)
      + admit. (* wf *)
    - apply typing_abs with (L:=dom E).
      intros. unfold open_fexp_wrt_fexp. simpl.
      assert (Hlc1: lc_fexp C1).
      { apply sub_elab_lc_fexp in H. auto. }
      assert (Hlc2: lc_fexp C2).
      { apply sub_elab_lc_fexp in H0. auto. }
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
      try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_case with (T1:=trans_typ S1) (T2:=trans_typ S2)
                             (L:=dom E `union` singleton x).
      + apply typing_var; auto. admit. (* wf *) 
      + intros. unfold open_fexp_wrt_fexp. simpl.
        rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_app with (T1:=trans_typ S1).
        * admit. (* weaken *) 
        * apply typing_var; auto.
          admit. (* wf *) 
      + intros. unfold open_fexp_wrt_fexp. simpl.
        rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_app with (T1:=trans_typ S2).
        * admit. (* weaken *) 
        * apply typing_var; auto.
          admit. (* wf *) 
Admitted. 
