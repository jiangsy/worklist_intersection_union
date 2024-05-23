Require Import uni.def_ott.
Require Import uni.decl.def_extra.
Require Import uni.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import uni.ltac_utils.
Require Import uni.notations.


Require Import systemf.def_ott.
Require Import systemf.prop_ln.


Notation "E ⊢ e : A" :=
  (f_typing E e A) 
    (at level 65, e at next level, no associativity) : type_scope.

Fixpoint trans_typ (A : typ) : ftyp :=
  match A with
  | typ_unit => ftyp_unit
  | typ_top => ftyp_unit
  | typ_bot => ftyp_all (ftyp_var_b 0)
  | typ_var_b n => ftyp_var_b n
  | typ_var_f X => ftyp_var_f X
  | typ_arrow A1 A2 => ftyp_arrow (trans_typ A1) (trans_typ A2)
  | typ_all A => ftyp_all (trans_typ A)
  | typ_union A1 A2 => ftyp_sum (trans_typ A1) (trans_typ A2)
  | typ_intersection A1 A2 => ftyp_prod (trans_typ A1) (trans_typ A2) 
  end.

Notation "ᵗ⟦  A  ⟧" := (trans_typ A) (at level 0, no associativity) : type_scope.

Fixpoint trans_env (Ψ : denv) : fenv :=
  match Ψ with
  | nil => nil
  | (X, dbind_tvar_empty) :: Ψ' => (X, fbind_tvar_empty) :: trans_env Ψ'
  | (X, dbind_stvar_empty) :: Ψ' => (X, fbind_tvar_empty) :: trans_env Ψ'
  | (X, (dbind_typ T)) :: Ψ' => (X, (fbind_typ (trans_typ T))) :: trans_env Ψ'
  end.

Notation "ᵉ⟦ Ψ ⟧" := (trans_env Ψ) (at level 0, no associativity) : type_scope.


Lemma trans_typ_open_typ_wrt_typ_rec : forall A1 A2 n,
  trans_typ (open_typ_wrt_typ_rec n A2 A1) = open_ftyp_wrt_ftyp_rec n ᵗ⟦ A2 ⟧ ᵗ⟦ A1 ⟧.
Proof.
  intros A1. induction A1; auto; intros; simpl.
  - destruct (lt_eq_lt_dec n n0) as [[? | ?] | ?] eqn:E; auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
  - rewrite IHA1. auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
Qed.

Theorem trans_typ_open_typ_wrt_typ : forall A1 A2,
  trans_typ (A1 ᵗ^^ₜ A2) = open_ftyp_wrt_ftyp (trans_typ A1) (trans_typ A2).
Proof.
  unfold open_typ_wrt_typ. unfold open_ftyp_wrt_ftyp.
  intros. apply trans_typ_open_typ_wrt_typ_rec.
Qed.

Theorem trans_typ_lc_ftyp : forall (A:typ),
  lc_typ A -> lc_ftyp (trans_typ A).
Proof.
  intros. induction H; simpl; eauto.
  - apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. eauto.
  - apply lc_ftyp_all. intros.
    rewrite <- trans_typ_open_typ_wrt_typ with (A2 := (typ_var_f X)).
    auto.
Qed.

#[local] Hint Resolve trans_typ_lc_ftyp : core.

Theorem trans_env_notin_dom : forall E X,
  X `notin` dom E -> X `notin` dom (trans_env E).
Proof.
  intros Ψ. induction Ψ; auto.
  intros X H. destruct a. destruct d; simpl in *; auto.
Qed.

#[local] Hint Resolve trans_env_notin_dom : core.

Theorem trans_env_tvar_in : forall (Ψ:denv) X,
  X ~ □ ∈ᵈ Ψ -> binds X fbind_tvar_empty (trans_env Ψ).
Proof.
  intros. induction Ψ; auto.
  destruct a; destruct d; destruct_binds; auto.
Qed.


Theorem trans_env_stvar_in : forall (Ψ:denv) X,
  X ~ ■ ∈ᵈ Ψ -> binds X fbind_tvar_empty (trans_env Ψ).
Proof.
  intros. induction Ψ; auto.
  destruct a; destruct d; destruct_binds; auto.
Qed.


Theorem trans_typ_wf : forall Ψ A,
  Ψ ᵗ⊢ᵈ A -> f_wf_typ (trans_env Ψ) (trans_typ A).
Proof.
  intros. induction H; simpl; eauto...
  - apply f_wf_typ__all with (L:=dom Ψ).
    intros. apply trans_env_notin_dom in H.
    unfold open_ftyp_wrt_ftyp. simpl. auto.
  - apply f_wf_typ__tvar. apply trans_env_tvar_in. auto.
  - apply f_wf_typ__tvar. apply trans_env_stvar_in. auto.
  - apply f_wf_typ__all with (L:= L `union` dom Ψ). 
    intros. inst_cofinites_with X.
    rewrite trans_typ_open_typ_wrt_typ in H1. auto.
Qed.

Theorem trans_env_wf_tenv_wf_fenv : forall Ψ,
  ⊢ᵈₜ Ψ -> f_wf_env ᵉ⟦ Ψ ⟧.
Proof with eauto using trans_typ_wf.
  intros. induction H; simpl; eauto...
  constructor...
  constructor... 
Qed.

Theorem trans_env_wf_env_wf_fenv : forall Ψ,
  ⊢ᵈ Ψ -> f_wf_env ᵉ⟦ Ψ ⟧.
Proof with eauto using trans_env_wf_tenv_wf_fenv.
  intros. induction H; simpl; eauto;
  try solve [apply trans_env_notin_dom in H0; apply wf_env_sub; auto]...
  constructor...
Qed.


Inductive d_sub_elab : denv -> typ -> typ -> fexp -> Prop :=
  | sub_elab_top : forall (Ψ:denv) (A:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ A ->
      d_sub_elab Ψ A typ_top (fexp_abs (trans_typ A) fexp_unit)
  | sub_elab_bot : forall (Ψ:denv) (B:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ B ->
      d_sub_elab Ψ typ_bot B (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_tapp (fexp_var_b 0) (trans_typ B)))
  | sub_elab_unit : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_sub_elab Ψ typ_unit typ_unit (fexp_abs ftyp_unit (fexp_var_b 0))
  | sub_elab_tvar : forall (Ψ:denv) (X:typvar),
      d_wf_env Ψ ->
      d_wf_typ Ψ (typ_var_f X) ->
      d_sub_elab Ψ (typ_var_f X) (typ_var_f X) (fexp_abs (ftyp_var_f X) (fexp_var_b 0))
  | sub_elab_arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ) (co1 co2:fexp),
      d_sub_elab Ψ B1 A1 co1 ->
      d_sub_elab Ψ A2 B2 co2 ->
      d_sub_elab Ψ (typ_arrow A1 A2) (typ_arrow B1 B2)
        (fexp_abs (ftyp_arrow (trans_typ A1) (trans_typ A2))
                  (fexp_abs (trans_typ B1)
                            (fexp_app co2
                                      (fexp_app (fexp_var_b 1)
                                                (fexp_app co1 (fexp_var_b 0))))))
  | sub_elab_all : forall (L:vars) (Ψ:denv) (A1 B1:typ) (co:fexp),
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  A1   (typ_var_f X) ) ) ->
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  B1   (typ_var_f X) ) ) ->
      ( forall X , X \notin L -> d_sub_elab  ( X ~ dbind_stvar_empty  ++  Ψ )   (open_typ_wrt_typ  A1   (typ_var_f X) )   (open_typ_wrt_typ  B1   (typ_var_f X) ) co ) ->
      d_sub_elab Ψ (typ_all A1) (typ_all B1)
        (fexp_abs (trans_typ (typ_all A1)) (fexp_tabs (fexp_app co (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0)))))
  | sub_elab_alll : forall (L:vars) (Ψ:denv) (A B T:typ) (co:fexp),
      neq_all B ->
      neq_intersection B ->
      neq_union B -> 
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
      d_wf_typ Ψ T ->
      d_mono_typ Ψ T ->
      d_sub_elab Ψ  (open_typ_wrt_typ  A   T )  B co ->
      d_sub_elab Ψ (typ_all A) B
        (fexp_abs (trans_typ (typ_all A)) (fexp_app co (fexp_tapp (fexp_var_b 0) (trans_typ T))))
  | sub_elab_intersection1 : forall (Ψ:denv) (A B1 B2:typ) (co1 co2:fexp),
      d_sub_elab Ψ A B1 co1 ->
      d_sub_elab Ψ A B2 co2 ->
      d_sub_elab Ψ A (typ_intersection B1 B2)
        (fexp_abs (trans_typ A)
                  (fexp_pair (fexp_app co1 (fexp_var_b 0))
                          (fexp_app co2 (fexp_var_b 0))))
  | sub_elab_intersection2 : forall (Ψ:denv) (A1 A2 B:typ) (co:fexp),
      d_sub_elab Ψ A1 B co ->
      d_wf_typ Ψ A2 ->
      d_sub_elab Ψ (typ_intersection A1 A2) B
        (fexp_abs (trans_typ (typ_intersection A1 A2)) (fexp_app co (fexp_proj1 (fexp_var_b 0))))
  | sub_elab_intersection3 : forall (Ψ:denv) (A1 A2 B:typ) (co:fexp),
      d_sub_elab Ψ A2 B co ->
      d_wf_typ Ψ A1 ->
      d_sub_elab Ψ (typ_intersection A1 A2) B
        (fexp_abs (trans_typ (typ_intersection A1 A2)) (fexp_app co (fexp_proj2 (fexp_var_b 0))))
  | sub_elab_union1 : forall (Ψ:denv) (A B1 B2:typ) (co:fexp),
      d_sub_elab Ψ A B1 co ->
      d_wf_typ Ψ B2 ->
      d_sub_elab Ψ A (typ_union B1 B2)
        (fexp_abs (trans_typ A) (fexp_inl (fexp_app co (fexp_var_b 0))))
  | sub_elab_union2 : forall (Ψ:denv) (A B1 B2:typ) (co:fexp),
      d_sub_elab Ψ A B2 co ->
      d_wf_typ Ψ B1 ->
      d_sub_elab Ψ A (typ_union B1 B2)
        (fexp_abs (trans_typ A) (fexp_inr (fexp_app co (fexp_var_b 0))))
  | sub_elab_union3 : forall (Ψ:denv) (A1 A2 B:typ) (co1 co2:fexp),
      d_sub_elab Ψ A1 B co1 ->
      d_sub_elab Ψ A2 B co2 ->
      d_sub_elab Ψ (typ_union A1 A2) B
        (fexp_abs (trans_typ (typ_union A1 A2)) (fexp_case (fexp_var_b 0) (fexp_app co1 (fexp_var_b 0)) (fexp_app co2 (fexp_var_b 0)))).


(* 



Notation "E ⊢ A <: B ↪ C" := (d_sub_elab E A B C) (at level 65, A at next level, no associativity) : type_scope.

Hint Constructors d_sub_elab : safety.
Hint Constructors typing : safety.

Theorem sub_elab_sound: forall E A B C,
  d_sub_elab E A B C -> d_sub E A B.
Proof.
  intros. induction H; eauto.
Qed.

Theorem sub_elab_complete: forall E A B,
  d_sub E A B -> exists C, d_sub_elab E A B C.
Proof.
  intros. induction H.
  - eauto with safety.
  - eauto with safety.
  - eauto with safety.
  - eauto with safety.
  - eauto with safety.
  - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
  - inst_cofinites_by L. inversion H2. eauto with safety.
    exists (fexp_abs (trans_typ (typ_all A1)) (fexp_tabs (fexp_app x0 (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0))))).
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
  d_sub_elab E A B C -> lc_fexp C.
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
    apply d_sub_d_wf in H. apply d_sub_d_wf in H0.
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
    apply d_sub_d_wf in H. apply d_sub_d_wf in H0.
    destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H. apply sub_elab_sound in H0.
    apply d_sub_d_wf in H. apply d_sub_d_wf in H0.
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
  d_sub_elab E A B C -> typing (trans_env E) C (ftyp_arrow (trans_typ A) (trans_typ B)).
Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_tapp with (B1:=ftyp_var_b 0); eauto with safety.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
    apply trans_typ_wf with (E:=E) (T:=typ_all (typ_var_b 0)).
    apply dwftyp_all with (L:=dom E); unfold open_typ_wrt_typ; simpl; auto.
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
    apply trans_typ_wf with (T:=typ_var_f X); auto.
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
    apply trans_typ_wf with (T:=typ_var_f SX); auto.
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
    apply typing_app with (B1:=trans_typ A2).
    + admit. (* weaken *)
    + apply typing_app with (B1:=trans_typ A1).
    * apply typing_var; auto.
      admit. (* wf *)
    * apply typing_app with (B1:=trans_typ B1).
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
    replace (ftyp_var_f X) with (trans_typ (typ_var_f X)); auto.
    apply typing_app with (B1:=trans_typ (A1 ᵗ^^ₜ typ_var_f X)).
    + rewrite <- trans_typ_open_typ_wrt_typ with (B1:=B1) (B2:=typ_var_f X).
    admit. (* weaken *)
    + rewrite trans_typ_open_typ_wrt_typ.
    apply typing_tapp; eauto with safety.
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=L `union` dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H5. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ (A1 ᵗ^^ₜ B2)).
    + admit. (* weaken *)
    + rewrite trans_typ_open_typ_wrt_typ.
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
    + apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_var; auto.
        admit. (* wf *)
    + apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_var; auto.
        admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A1).
    + admit. (* weaken *) 
    + apply typing_proj1 with (B2:=trans_typ A2).
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A2).
    + admit. (* weaken *) 
    + apply typing_proj2 with (B1:=trans_typ A1).
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_inl.
    + eapply typing_app with (B1:=trans_typ A1).
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
    + eapply typing_app with (B1:=trans_typ A1).
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
    apply typing_case with (B1:=trans_typ A1) (B2:=trans_typ A2)
               (L:=dom E `union` singleton x).
    + apply typing_var; auto. admit. (* wf *) 
    + intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *) 
      * apply typing_var; auto.
        admit. (* wf *) 
    + intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A2).
      * admit. (* weaken *) 
      * apply typing_var; auto.
        admit. (* wf *) 
Admitted.

Inductive infabs_elab : denv -> typ -> typ -> typ -> fexp -> Prop := 
| infabs_elab_bot : forall (E:denv),
  d_wf_env E ->
  infabs_elab E typ_bot typ_top typ_bot
    (fexp_abs (ftyp_all (ftyp_var_b 0))
          (fexp_tapp (fexp_var_b 0) (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0)))))
| infabs_elab_arr : forall (E:denv) (B1 B2:typ),
  d_wf_env E ->
  d_wf_typ E B1 ->
  d_wf_typ E B2 ->
  infabs_elab E (typ_arrow B1 B2) B1 B2
    (fexp_abs (trans_typ (typ_arrow B1 B2)) (fexp_var_b 0))
| infabs_elab_all : forall (E:denv) (B1 B2 T3 T4:typ) (Co:fexp),
  d_mono_typ B2 -> 
  d_wf_typ E B2 ->
  d_wf_typ E (typ_all B1) ->
  infabs_elab E  (open_typ_wrt_typ  B1   B2 ) T3 T4 Co ->
  infabs_elab E (typ_all B1) T3 T4
    (fexp_abs (trans_typ (typ_all B1))
              (fexp_app Co (fexp_tapp (fexp_var_b 0) (trans_typ B2))))
| infabs_elab_intersection1 : forall (E:denv) (B1 B2 T3 T4:typ) (Co:fexp),
  d_wf_typ E B2 ->
  infabs_elab E B1 T3 T4 Co ->
  infabs_elab E (typ_intersection B1 B2) T3 T4
    (fexp_abs (trans_typ (typ_intersection B1 B2))
              (fexp_app Co (fexp_proj1 (fexp_var_b 0))))
| infabs_elab_intersection2 : forall (E:denv) (B1 B2 T3 T4:typ) (Co:fexp),
  d_wf_typ E B1 ->
  infabs_elab E B2 T3 T4 Co ->
  infabs_elab E (typ_intersection B1 B2) T3 T4
    (fexp_abs (trans_typ (typ_intersection B1 B2))
              (fexp_app Co (fexp_proj2 (fexp_var_b 0))))
| infabs_elab_union : forall (E:denv) (B1 B2 T3 T4 T5 T6:typ) (Co1 Co2:fexp),
  infabs_elab E B1 T3 T4 Co1 ->
  infabs_elab E B2 T5 T6 Co2 ->
  infabs_elab E (typ_union B1 B2) (typ_intersection T3 T5) (typ_union T4 T6)
    (fexp_abs (trans_typ (typ_union B1 B2))
              (fexp_abs (trans_typ (typ_intersection T3 T5))
                        (fexp_case (fexp_var_b 1)
                                   (fexp_inl (fexp_app Co1 (fexp_proj1 (fexp_var_b 1))))
                                   (fexp_inr (fexp_app Co2 (fexp_proj2 (fexp_var_b 1)))))))
.

Notation "E ⊢ B1 ▹ B2 → T3 ↪ C" :=   (infabs_elab E B1 B2 T3 C) 
  (at level 65, B1 at next level, B2 at next level, no associativity) : type_scope.

Lemma lc_ftyp_all_id : lc_ftyp (ftyp_all (ftyp_var_b 0)).
Proof.
  apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. auto.
Qed.

Hint Resolve lc_ftyp_all_id : safety.

Theorem infabs_elab_lc_fexp : forall E A B C Co,
  infabs_elab E A B C Co -> lc_fexp Co.
Proof.
  intros. induction H; eauto with safety;
  apply lc_fexp_abs; eauto with safety; simpl.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_tapp; eauto with safety.
  - unfold open_fexp_wrt_fexp. simpl. auto.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_app; eauto with safety.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply lc_ftyp_prod.
    + admit.
    + apply trans_typ_lc_ftyp. apply d_wf_typ_lc_typ with (E:=E); auto.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_app; eauto with safety.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply lc_ftyp_prod.
    + apply trans_typ_lc_ftyp. apply d_wf_typ_lc_typ with (E:=E); auto.
    + admit.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_app; eauto with safety.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
Admitted.

Theorem infabs_sound_f : forall E A B C Co,
  infabs_elab E A B C Co ->
  typing (trans_env E) Co (ftyp_arrow (trans_typ A) (ftyp_arrow (trans_typ B) (trans_typ C))).
Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    replace (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0))) with
        (open_ftyp_wrt_ftyp (ftyp_var_b 0)
                  (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0)))) at 2; auto.
    apply typing_tapp.
    + apply lc_ftyp_arrow; auto.
    apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. auto.
    + apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp Co).
    { apply infabs_elab_lc_fexp in H2. auto. }
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ (open_typ_wrt_typ B1 B2)).
    + admit. (* weaken *)
    + rewrite trans_typ_open_typ_wrt_typ. apply typing_tapp.
      * apply trans_typ_lc_ftyp; auto.
      * apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp Co).
    { apply infabs_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ B1); auto.
    + admit. (* weaken *)
    + apply typing_proj1 with (B2:=trans_typ B2).
      apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp Co).
    { apply infabs_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ B2); auto.
    + admit. (* weaken *)
    + apply typing_proj2 with (B1:=trans_typ B1).
      apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom E).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc1: lc_fexp Co1).
    { apply infabs_elab_lc_fexp in H. auto. }
    assert (Hlc2: lc_fexp Co2).
    { apply infabs_elab_lc_fexp in H0. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_abs with (L:=dom E `union` singleton x).
    intros. unfold open_fexp_wrt_fexp. simpl.
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_case with
      (L:=dom E `union` singleton x `union` singleton x0)
      (B1:=trans_typ B1) (B2:=trans_typ B2).
    + apply typing_var; auto. admit. (* wf *)
    + unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_inl.
      * apply typing_app with (B1:=trans_typ T3).
        -- admit. (* weaken *)
        -- apply typing_proj1 with (B2:=trans_typ T5).
           apply typing_var; auto. admit. (* wf *)
      * admit. (* wf *)
    + unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_inr.
      * apply typing_app with (B1:=trans_typ T5).
        -- admit. (* weaken *)
        -- apply typing_proj2 with (B1:=trans_typ T3).
           apply typing_var; auto. admit. (* wf *)
      * admit. (* wf *)
Admitted.

Inductive inftapp_elab : denv -> typ -> typ -> typ -> fexp -> fexp -> Prop := 
| inftapp_elab_bot : forall (E:denv) (B1:typ),
  d_wf_env E -> 
  d_wf_typ E B1 ->
  inftapp_elab E typ_bot B1 typ_bot
    (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_var_b 0))
    (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_var_b 0))
| inftapp_elab_all : forall (E:denv) (B1 B2:typ),
  d_wf_env E -> 
  d_wf_typ E (typ_all B1) ->
  d_wf_typ E B2 ->
  inftapp_elab E (typ_all B1) B2 (open_typ_wrt_typ  B1   B2 )  
    (fexp_abs (trans_typ (typ_all B1)) (fexp_var_b 0))
    (fexp_abs (trans_typ (typ_all B1)) (fexp_tapp (fexp_var_b 0) (trans_typ B2)))
| inftapp_elab_intersection1 : forall (E:denv) (A1 A2 B C1:typ) (Co1 Co2:fexp),
  d_wf_typ E A2 ->
  d_inftapp_false A2 ->
  inftapp_elab E A1 B C1 Co1 Co2 ->
  inftapp_elab E (typ_intersection A1 A2) B C1
    (fexp_abs (trans_typ (typ_intersection A1 A2))
              (fexp_app Co1 (fexp_proj1 (fexp_var_b 0))))
    Co2
| inftapp_elab_intersection2 : forall (E:denv) (A1 A2 B C2:typ) (Co1 Co2:fexp),
  d_wf_typ E A1 ->
  d_inftapp_false A1 ->
  inftapp_elab E A2 B C2 Co1 Co2 ->
  inftapp_elab E (typ_intersection A1 A2) B C2
    (fexp_abs (trans_typ (typ_intersection A1 A2))
              (fexp_app Co1 (fexp_proj2 (fexp_var_b 0))))
    Co2
| inftapp_elab_intersection3 : forall (E:denv) (A1 A2 B C1 C2:typ) (Co1 Co2 Co3 Co4:fexp),
  inftapp_elab E A1 B C1 Co1 Co2 ->
  inftapp_elab E A2 B C2 Co3 Co4 ->
  inftapp_elab E (typ_intersection A1 A2) B (typ_intersection C1 C2)
    (fexp_abs (trans_typ (typ_intersection A1 A2))
              (fexp_pair (fexp_app Co2 (fexp_app Co1 (fexp_proj1 (fexp_var_b 0))))
                         (fexp_app Co4 (fexp_app Co3 (fexp_proj2 (fexp_var_b 0))))))
    (fexp_abs (trans_typ ((typ_intersection C1 C2))) (fexp_var_b 0))
| inftapp_elab_union : forall (E:denv) (A1 A2 B C1 C2:typ) (Co1 Co2 Co3 Co4:fexp),
  inftapp_elab E A1 B C1 Co1 Co2 ->
  inftapp_elab E A2 B C2 Co3 Co4 ->
  inftapp_elab E (typ_union A1 A2) B (typ_union C1 C2)
    (fexp_abs (trans_typ (typ_union A1 A2))
              (fexp_case (fexp_var_b 0)
                         (fexp_inl (fexp_app Co2 (fexp_app Co1 (fexp_var_b 0))))
                         (fexp_inr (fexp_app Co4 (fexp_app Co3 (fexp_var_b 0))))))
    (fexp_abs (trans_typ (typ_union C1 C2)) (fexp_var_b 0))
.

Notation "E ⊢ B1 ○ B2 ⇒⇒ T3 ↪ C1 | C2" :=
    (inftapp_elab E B1 B2 T3 C1 C2) 
      (at level 65, B1 at next level, B2 at next level, no associativity) : type_scope. 

Theorem inftapp_elab_lc_fexp : forall E A B C Co1 Co2,
  inftapp_elab E A B C Co1 Co2 -> lc_fexp Co1 /\ lc_fexp Co2.
Proof.
  intros. induction H; eauto with safety; simpl.
  - split; apply lc_fexp_abs; eauto with safety;
    unfold open_fexp_wrt_fexp; simpl; auto.
  - split; apply lc_fexp_abs; eauto with safety.
    + replace (ftyp_all (trans_typ B1)) with (trans_typ (typ_all B1)); eauto.
      apply trans_typ_lc_ftyp. eauto.
    + unfold open_fexp_wrt_fexp. simpl. auto.
    + replace (ftyp_all (trans_typ B1)) with (trans_typ (typ_all B1)); eauto.
      apply trans_typ_lc_ftyp. eauto.
    + unfold open_fexp_wrt_fexp. simpl. intros.
      apply lc_fexp_tapp; eauto. apply trans_typ_lc_ftyp. eauto. 
Admitted.

Theorem inftapp_sound_f : forall E A B C Co1 Co2,
  inftapp_elab E A B C Co1 Co2 -> exists D,
  typing (trans_env E) Co1 (ftyp_arrow (trans_typ A) D) /\
    typing (trans_env E) Co2 (ftyp_arrow D (trans_typ C)).
Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - exists (ftyp_all (ftyp_var_b 0)). split.
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
  - exists (ftyp_all (trans_typ B1)). split.
    + apply typing_abs with (L:=dom E).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom E).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite trans_typ_open_typ_wrt_typ.
      apply typing_tapp.
      * apply trans_typ_lc_ftyp. eauto.
      * apply typing_var; auto. admit. (* wf *)
  - inversion IHinftapp_elab. destruct H2.
    exists x. split.
    + apply typing_abs with (L:=dom E).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp Co1 /\ lc_fexp Co2).
      { apply inftapp_elab_lc_fexp in H1. auto. }
      destruct Hlc as [Hlc1 Hlc2].
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_proj1 with (B2:=trans_typ A2).
        apply typing_var; auto. admit. (* wf *)
    + auto.
  - inversion IHinftapp_elab. destruct H2.
    exists x. split.
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp Co1 /\ lc_fexp Co2).
      { apply inftapp_elab_lc_fexp in H1. auto. }
      destruct Hlc as [Hlc1 Hlc2].
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (B1:=trans_typ A2).
      * admit. (* weaken *)
      * apply typing_proj2 with (B1:=trans_typ A1).
        apply typing_var; auto.  admit. (* wf *)
    + auto.
  - inversion IHinftapp_elab1. inversion IHinftapp_elab2.
    destruct H1. destruct H2.
    exists (trans_typ (typ_intersection C1 C2)). split.
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc12: lc_fexp Co1 /\ lc_fexp Co2).
      { apply inftapp_elab_lc_fexp in H. auto. }
      destruct Hlc12 as [Hlc1 Hlc2].
      assert (Hlc34: lc_fexp Co3 /\ lc_fexp Co4).
      { apply inftapp_elab_lc_fexp in H0. auto. }
      destruct Hlc34 as [Hlc3 Hlc4].
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_pair.
      * apply typing_app with (B1:=x).
        -- admit. (* weaken *) 
        -- apply typing_app with (B1:=trans_typ A1).
           ++ admit. (* weaken *)
           ++ apply typing_proj1 with (B2:=trans_typ A2).
              apply typing_var; auto. admit. (* wf *)
      * apply typing_app with (B1:=x0).
        -- admit. (* weaken *) 
        -- apply typing_app with (B1:=trans_typ A2).
           ++ admit. (* weaken *)
           ++ apply typing_proj2 with (B1:=trans_typ A1).
              apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
  - inversion IHinftapp_elab1. inversion IHinftapp_elab2.
    destruct H1. destruct H2.
    exists (trans_typ (typ_union C1 C2)). split.
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc12: lc_fexp Co1 /\ lc_fexp Co2).
      { apply inftapp_elab_lc_fexp in H. auto. }
      destruct Hlc12 as [Hlc1 Hlc2].
      assert (Hlc34: lc_fexp Co3 /\ lc_fexp Co4).
      { apply inftapp_elab_lc_fexp in H0. auto. }
      destruct Hlc34 as [Hlc3 Hlc4].
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_case with (L:=dom E `union` singleton x1)
        (B1:=trans_typ A1) (B2:=trans_typ A2).
      * apply typing_var; auto. admit. (* wf *)
      * unfold open_fexp_wrt_fexp. simpl. intros.
        repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_inl.
        -- apply typing_app with (B1:=x).
           ++ admit. (* weaken *) 
           ++ apply typing_app with (B1:=trans_typ A1).
              ** admit. (* weaken *)
              ** apply typing_var; auto. admit. (* wf *)
        -- admit. (* wf *)
      * unfold open_fexp_wrt_fexp. simpl. intros.
        repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_inr.
        -- apply typing_app with (B1:=x0).
           ++ admit. (* weaken *) 
           ++ apply typing_app with (B1:=trans_typ A2).
              ** admit. (* weaken *)
              ** apply typing_var; auto. admit. (* wf *)
        -- admit. (* wf *)
    + apply typing_abs with (L:=dom E).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)  
Admitted.


Inductive typing_elab : denv -> dexp -> d_typing_mode -> typ -> fexp -> Prop :=
| typing_elab_infvar : forall (E:denv) (x:expvar) (B1:typ),
  d_wf_env E ->
  binds ( x )  ( (dbind_typ B1) ) ( E )  ->
  typing_elab E (dexp_var_f x) d_typingmode_inf B1
    (fexp_var_f x)
| typing_elab_infanno : forall (E:denv) (e:dexp) (B1:typ) (C:fexp),
  d_wf_typ E B1 ->
  typing_elab E e d_typingmode_chk B1 C ->
  typing_elab E  ( (dexp_anno e B1) )  d_typingmode_inf B1
    C
| typing_elabinf_unit : forall (E:denv),
  d_wf_env E ->
  typing_elab E dexp_unit d_typingmode_inf typ_unit
    fexp_unit
| typing_elab_infapp : forall (E:denv) (e1 e2:dexp) (B1 B2 T3:typ) (C1 C2 C3:fexp),
  typing_elab E e1 d_typingmode_inf B1 C1 ->
  infabs_elab E B1 B2 T3 C2 ->
  typing_elab E e2 d_typingmode_chk B2 C3 ->
  typing_elab E  ( (dexp_app e1 e2) ) d_typingmode_inf T3
    (fexp_app (fexp_app C2 C1) C3)
| typing_elab_inftabs : forall (L:vars) (E:denv) (e:dexp) (B1:typ) (C:fexp),
  d_wf_typ E (typ_all B1) ->
  ( forall X , X \notin  L  -> typing_elab  ( X ~ dbind_tvar_empty  ++  E ) (dexp_anno  ( open_dexp_wrt_typ e (typ_var_f X) )  ( open_typ_wrt_typ B1 (typ_var_f X) ) ) d_typingmode_chk ( open_typ_wrt_typ B1 (typ_var_f X) ) C)  ->
  typing_elab E (dexp_tabs (dbody_anno e B1)) d_typingmode_inf (typ_all B1)
    (fexp_tabs C)
| typing_elab_inftapp : forall (E:denv) (e1:dexp) (B1 B2 T3:typ) (C1 C2 C3:fexp),
  d_wf_typ E B2 ->
  typing_elab E e1 d_typingmode_inf B1 C1 ->
  inftapp_elab E B1 B2 T3 C2 C3 ->
  typing_elab E (dexp_tapp e1 B2) d_typingmode_inf T3
    (fexp_app C3 (fexp_app C2 C1))
| typing_elab_chkabstop : forall (L:vars) (E:denv) (e:dexp) (C:fexp),
  ( forall x , x \notin  L  -> typing_elab  ( x ~ (dbind_typ typ_bot)  ++  E )   ( open_dexp_wrt_dexp e (dexp_var_f x) ) d_typingmode_chk typ_top C)  ->
  typing_elab E (dexp_abs e) d_typingmode_chk typ_top
    fexp_unit
| typing_elab_chkabs : forall (L:vars) (E:denv) (e:dexp) (B1 B2:typ) (C:fexp),
  d_wf_typ E B1 ->
  ( forall x , x \notin  L  -> typing_elab  ( x ~ (dbind_typ B1)  ++  E )  ( open_dexp_wrt_dexp e (dexp_var_f x) ) d_typingmode_chk B2 C)  ->
  typing_elab E (dexp_abs e) d_typingmode_chk (typ_arrow B1 B2)
    (fexp_abs (trans_typ B1) C)
| typing_elab_chkall : forall (L:vars) (E:denv) (e:dexp) (B1:typ) (C:fexp),
  d_wf_typ E (typ_all B1) ->
  ( forall X , X \notin  L  -> typing_elab  ( X ~ dbind_tvar_empty  ++  E )  e  d_typingmode_chk ( open_typ_wrt_typ B1 (typ_var_f X) ) C)  ->
  typing_elab E e d_typingmode_chk (typ_all B1)
    (fexp_tabs C)
| typing_elab_chksub : forall (E:denv) (e:dexp) (B1 A1:typ) (C1 C2:fexp),
  typing_elab E e d_typingmode_inf A1 C1 ->
  d_sub_elab E A1 B1 C2 ->
  typing_elab E e d_typingmode_chk B1
    (fexp_app C2 C1)
| typing_elab_chkintersection : forall (E:denv) (e:dexp) (A1 B1:typ) (C1 C2:fexp),
  typing_elab E e d_typingmode_chk A1 C1 ->
  typing_elab E e d_typingmode_chk B1 C2 ->
  typing_elab E e d_typingmode_chk (typ_intersection A1 B1)
    (fexp_pair C1 C2)
| typing_elab_chkunion1 : forall (E:denv) (e:dexp) (A1 B1:typ) (C:fexp),
  typing_elab E e d_typingmode_chk A1 C ->
  d_wf_typ E B1 ->
  typing_elab E e d_typingmode_chk (typ_union A1 B1)
    (fexp_inl C)
| typing_elab_chkunion2 : forall (E:denv) (e:dexp) (A1 B1:typ) (C:fexp),
  typing_elab E e d_typingmode_chk B1 C ->
  d_wf_typ E A1 ->
  typing_elab E e d_typingmode_chk (typ_union A1 B1)
    (fexp_inr C)
.

Theorem trans_binds : forall E x T,
  binds x (dbind_typ T) E -> binds x (bind_typ (trans_typ T)) (trans_env E).
Proof.
  intros. induction E; auto.
  inversion H.
  - subst. simpl. auto.
  - apply IHE in H0. destruct a.
    destruct b; simpl; auto.
Qed.

Theorem typing_elab_lc_fexp : forall E e T C mode,
  typing_elab E e mode T C -> lc_fexp C.
Proof.
  intros. induction H; eauto with safety; simpl.
Admitted.

Theorem typing_sound_f : forall E e T C mode,
  typing_elab E e mode T C -> typing (trans_env E) C (trans_typ T).
Proof.
  intros. induction H; simpl; eauto.
  - apply typing_var; auto. admit. (* wf *)
    apply trans_binds. auto.
  - apply typing_app with (B1:=trans_typ B2); auto.
    apply typing_app with (B1:=trans_typ B1); auto.
    apply infabs_sound_f; auto.
  - apply typing_tabs with (L:=L `union` dom E).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X. assert (Hlc: lc_fexp C).
    { apply typing_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    rewrite <- trans_typ_open_typ_wrt_typ with (B2:=typ_var_f X). auto.
  - apply inftapp_sound_f in H1. destruct H1. destruct H1.
    apply typing_app with (B1:=x); auto.
    apply typing_app with (B1:=trans_typ B1); auto.
  - apply typing_abs with (L:=L `union` dom E).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with x. assert (Hlc: lc_fexp C).
    { apply typing_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_lc_fexp; auto.
  - apply typing_tabs with (L:=L `union` dom E).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X. assert (Hlc: lc_fexp C).
    { apply typing_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    rewrite <- trans_typ_open_typ_wrt_typ with (B2:=typ_var_f X). auto.
  - eapply typing_app with (B1:=trans_typ A1); auto.
    apply sub_sound_f. auto.
Admitted. *)
