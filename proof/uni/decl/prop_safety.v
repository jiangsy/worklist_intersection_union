Require Import Coq.Program.Equality.
Require Export Metalib.Metatheory.

Require Import systemf.def_ott.
Require Import systemf.prop_ln.
Require Import systemf.prop_basic.

Require Import uni.prop_basic.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_rename.
Require Import uni.ltac_utils.

Open Scope dbind.

Notation "Ψ ⊢ e : A" :=
  (f_typing Ψ e A) 
    (at level 65, e at next level, no associativity) : type_scope.

Notation "⊢ᶠ Ψ" :=
  (f_wf_env Ψ)
    (at level 65, no associativity) : type_scope.

Notation "Ψ ᵗ⊢ᶠ A" :=
  (f_wf_typ Ψ A)
    (at level 65, no associativity) : type_scope.

Fixpoint trans_ftyp (A : typ) : ftyp :=
  match A with
  | typ_unit => ftyp_unit
  | typ_top => ftyp_unit
  | typ_bot => ftyp_all (ftyp_var_b 0)
  | typ_var_b n => ftyp_var_b n
  | typ_var_f X => ftyp_var_f X
  | typ_arrow A1 A2 => ftyp_arrow (trans_ftyp A1) (trans_ftyp A2)
  | typ_all A => ftyp_all (trans_ftyp A)
  | typ_union A1 A2 => ftyp_sum (trans_ftyp A1) (trans_ftyp A2)
  | typ_intersection A1 A2 => ftyp_prod (trans_ftyp A1) (trans_ftyp A2) 
  end.

Notation "ᵗ⟦  A  ⟧" := (trans_ftyp A) (at level 0, no associativity) : type_scope.

Fixpoint trans_env (Ψ : denv) : fenv :=
  match Ψ with
  | nil => nil
  | (X, dbind_tvar_empty) :: Ψ' => (X, fbind_tvar_empty) :: trans_env Ψ'
  | (X, dbind_stvar_empty) :: Ψ' => (X, fbind_tvar_empty) :: trans_env Ψ'
  | (X, (dbind_typ T)) :: Ψ' => (X, (fbind_typ (trans_ftyp T))) :: trans_env Ψ'
  end.

Notation "⟦ Ψ ⟧" := (trans_env Ψ) (at level 0, no associativity) : type_scope.

Lemma trans_ftyp_open_typ_wrt_typ_rec : forall A1 A2 n,
  trans_ftyp (open_typ_wrt_typ_rec n A2 A1) = open_ftyp_wrt_ftyp_rec n ᵗ⟦ A2 ⟧ ᵗ⟦ A1 ⟧.
Proof.
  intros A1. induction A1; auto; intros; simpl.
  - destruct (lt_eq_lt_dec n n0) as [[? | ?] | ?] eqn:Ψ; auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
  - rewrite IHA1. auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
Qed.

Theorem trans_ftyp_open_typ_wrt_typ : forall A1 A2,
  ᵗ⟦ A1 ᵗ^^ₜ A2 ⟧ = open_ftyp_wrt_ftyp ᵗ⟦ A1 ⟧ ᵗ⟦ A2 ⟧.
Proof.
  unfold open_typ_wrt_typ. unfold open_ftyp_wrt_ftyp.
  intros. apply trans_ftyp_open_typ_wrt_typ_rec.
Qed.

Theorem trans_ftyp_lc_ftyp : forall (A:typ),
  lc_typ A -> lc_ftyp (trans_ftyp A).
Proof.
  intros. induction H; simpl; eauto.
  - apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. eauto.
  - apply lc_ftyp_all. intros.
    rewrite <- trans_ftyp_open_typ_wrt_typ with (A2 := (typ_var_f X)).
    auto.
Qed.

#[local] Hint Resolve trans_ftyp_lc_ftyp : core.

Theorem trans_env_notin_dom : forall Ψ X,
  X `notin` dom Ψ -> X `notin` dom ⟦ Ψ ⟧.
Proof.
  intros Ψ. induction Ψ; auto.
  intros X H. destruct a. destruct d; simpl in *; auto.
Qed.

#[local] Hint Resolve trans_env_notin_dom : core.

Theorem trans_env_tvar_in : forall (Ψ:denv) X,
  X ~ □ ∈ᵈ Ψ -> binds X fbind_tvar_empty ⟦ Ψ ⟧.
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

Theorem trans_ftyp_wf : forall Ψ A,
  Ψ ᵗ⊢ᵈ A -> f_wf_typ ⟦ Ψ ⟧ ᵗ⟦ A ⟧.
Proof.
  intros. induction H; simpl; eauto...
  - apply f_wf_typ__all with (L:=dom Ψ).
    intros. apply trans_env_notin_dom in H.
    unfold open_ftyp_wrt_ftyp. simpl. auto.
  - apply f_wf_typ__tvar. apply trans_env_tvar_in. auto.
  - apply f_wf_typ__tvar. apply trans_env_stvar_in. auto.
  - apply f_wf_typ__all with (L:= L `union` dom Ψ). 
    intros. inst_cofinites_with X.
    rewrite trans_ftyp_open_typ_wrt_typ in H1. auto.
Qed.

Theorem trans_env_wf_tenv_wf_fenv : forall Ψ,
  ⊢ᵈₜ Ψ -> ⊢ᶠ ⟦ Ψ ⟧.
Proof with eauto using trans_ftyp_wf.
  intros. induction H; simpl; eauto...
  constructor...
  constructor... 
Qed.

Theorem trans_env_wf_env_wf_fenv : forall Ψ,
  ⊢ᵈ Ψ -> ⊢ᶠ ⟦ Ψ ⟧.
Proof with eauto using trans_env_wf_tenv_wf_fenv.
  intros. induction H; simpl; eauto;
  try solve [apply trans_env_notin_dom in H0; apply wf_env_sub; auto]...
  constructor...
Qed.

Lemma f_wf_typ_weaken : forall Δ1 Δ2 Δ3 A,
  Δ3 ++ Δ1 ᵗ⊢ᶠ A ->
  uniq (Δ3 ++ Δ2 ++ Δ1) ->
  Δ3 ++ Δ2 ++ Δ1 ᵗ⊢ᶠ A.
Proof.
  intros. dependent induction H; eauto.
  - remember (dom (Δ3 ++ Δ2 ++ Δ1)).
    inst_cofinites_for f_wf_typ__all. intros. inst_cofinites_with X.
    rewrite_env ((X ~ fbind_tvar_empty ++ Δ3) ++ Δ2 ++ Δ1).
    eapply H0; eauto. simpl. subst. constructor; eauto.
Qed.

Lemma f_wf_typ_weaken_cons : forall Δ x A B,
  Δ ᵗ⊢ᶠ A ->
  uniq ((x , fbind_typ B) :: Δ) ->
  (x , fbind_typ B) :: Δ ᵗ⊢ᶠ A.
Proof.
  intros. rewrite_env (nil ++ (x ~ fbind_typ B) ++ Δ).
  eapply f_wf_typ_weaken; eauto.
Qed.

Lemma f_wf_typ_strengthen_var : forall Δ1 Δ2 x A B,
  Δ2 ++ (x , fbind_typ B) :: Δ1 ᵗ⊢ᶠ A ->
  Δ2 ++ Δ1 ᵗ⊢ᶠ A.
Proof.
  intros. dependent induction H; eauto.
  - apply binds_remove_mid_diff_bind in H; eauto. solve_false.
  - remember (dom (Δ2 ++ Δ1)). inst_cofinites_for f_wf_typ__all. intros.
    inst_cofinites_with X. rewrite_env ((X ~ fbind_tvar_empty ++ Δ2) ++ Δ1).
    eapply H0 with (x:=x) (B:=B); eauto; subst.
Qed.

Lemma f_wf_env_uniq : forall Δ,
  ⊢ᶠ Δ -> uniq Δ.
Proof.
  intros. induction H; eauto. 
Qed.

#[local] Hint Resolve f_wf_env_uniq : core.

Lemma f_wf_env_binds_f_wf_typ : forall Δ x A,
  ⊢ᶠ Δ -> 
  binds x (fbind_typ A) Δ -> 
  Δ ᵗ⊢ᶠ A.
Proof.
  intros. induction H; eauto.
  - inversion H0.
  - destruct_binds. rewrite_env (nil ++ (X ~ fbind_tvar_empty) ++ Δ).
    apply f_wf_typ_weaken; eauto. 
  - destruct_binds.
    + rewrite_env (nil ++ (x ~ fbind_typ A) ++ Δ).
      apply f_wf_typ_weaken; eauto. 
    + rewrite_env (nil ++ (x0 ~ fbind_typ A0) ++ Δ).
      apply f_wf_typ_weaken; eauto. 
Qed.

Lemma f_wf_typ_lc_ftyp : forall Δ A,
  Δ ᵗ⊢ᶠ A -> lc_ftyp A.
Proof.
  intros. induction H; auto.
Qed.

Lemma f_wf_typ_subst_tvar : forall Δ1 Δ2 X A B,
  Δ2 ++ (X ~ fbind_tvar_empty) ++ Δ1 ᵗ⊢ᶠ A ->
  Δ1 ᵗ⊢ᶠ B ->
  uniq (map (subst_ftyp_in_fbind B X) Δ2 ++ Δ1) ->
  map (subst_ftyp_in_fbind B X) Δ2 ++ Δ1 ᵗ⊢ᶠ (subst_ftyp_in_ftyp B X A).
Proof.
  intros. dependent induction H; simpl in *; eauto.
  - destruct_eq_atom...
    rewrite_env (nil ++ map (subst_ftyp_in_fbind B X) Δ2 ++ Δ1).
    apply f_wf_typ_weaken; eauto.
    apply binds_remove_mid in H; auto.
    apply binds_app_iff in H. destruct H; auto.
    + apply binds_map with (f:=subst_ftyp_in_fbind B X) in H; auto. 
  - remember (dom (map (subst_ftyp_in_fbind B X) Δ2 ++ Δ1)). inst_cofinites_for f_wf_typ__all. intros.  
    inst_cofinites_with X0. subst. rewrite_env (map (subst_ftyp_in_fbind B X) (X0 ~ fbind_tvar_empty ++ Δ2) ++ Δ1).
    replace (ftyp_var_f X0) with (subst_ftyp_in_ftyp B X (ftyp_var_f X0)); eauto.
    rewrite <- subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp; eauto.
    + eapply H0; eauto. simpl. constructor; eauto.
    + eapply f_wf_typ_lc_ftyp; eauto.
    + simpl. destruct_eq_atom; auto.
Qed.

Lemma f_wf_typ_open : forall Δ A B,
  uniq Δ ->
  f_wf_typ Δ (ftyp_all A) ->
  f_wf_typ Δ B ->
  f_wf_typ Δ (open_ftyp_wrt_ftyp A B).
Proof with simpl_env; eauto.
  intros.
  dependent destruction H0. 
  remember (ftvar_in_ftyp A).
  pick fresh X. inst_cofinites_with X. subst.
  rewrite (subst_ftyp_in_ftyp_intro X)...
  rewrite_env (map (subst_ftyp_in_fbind B X) nil ++ Δ).
  apply f_wf_typ_subst_tvar...
Qed.

Lemma f_typing_wf : forall Δ e A,
  Δ ⊢ e : A -> ⊢ᶠ Δ /\ Δ ᵗ⊢ᶠ A.
Proof with eauto. 
  intros. induction H; try solve [intuition].
  - intuition.
    apply f_wf_env_binds_f_wf_typ in H0...
  - split.
    + pick fresh x. inst_cofinites_with x. intuition. dependent destruction H1...
    + remember (dom Δ). pick fresh x. inst_cofinites_with x. intuition. subst.
      dependent destruction H1.
      rewrite_env (nil ++ (x ~ fbind_typ A1) ++ Δ) in H3.
      apply f_wf_typ_strengthen_var in H3...
  - intuition. dependent destruction H2...
  - split.
    + pick fresh X. inst_cofinites_with X. intuition. dependent destruction H1...
    + remember (dom Δ). inst_cofinites_for f_wf_typ__all. intros.
      inst_cofinites_with X. subst. intuition. 
  - intuition.
    apply f_wf_typ_open; eauto.
  - remember (dom Δ). pick fresh x.
    inst_cofinites_with x.
    intuition.
    rewrite_env (nil ++ (x ~ fbind_typ A1) ++ Δ) in H5.
    apply f_wf_typ_strengthen_var in H5... 
  - intuition. dependent destruction H1...
  - intuition. dependent destruction H1...
Qed.

Lemma f_typing_weaken : forall Δ1 Δ2 Δ3 e A,
  Δ3 ++ Δ1 ⊢ e : A -> 
  ⊢ᶠ Δ3 ++ Δ2 ++ Δ1 ->
  Δ3 ++ Δ2 ++ Δ1 ⊢ e : A.
Proof with eauto using f_wf_typ_weaken.
  intros. dependent induction H...
  - remember (dom (Δ3 ++ Δ2 ++ Δ1)). inst_cofinites_for f_typing__abs. intros.
    inst_cofinites_with x. 
    rewrite_env ((x ~ fbind_typ A1 ++ Δ3) ++ Δ2 ++ Δ1).
    eapply H0... simpl. subst. constructor...
    apply f_typing_wf in H. intuition. dependent destruction H3...
  - remember (dom (Δ3 ++ Δ2 ++ Δ1)).
    inst_cofinites_for f_typing__tabs. intros. inst_cofinites_with X.
    rewrite_env ((X ~ fbind_tvar_empty ++ Δ3) ++ Δ2 ++ Δ1).
    eapply H0... simpl. subst. constructor...
  - remember (dom (Δ3 ++ Δ2 ++ Δ1)). inst_cofinites_for f_typing__case A1:=A1,A2:=A2...
    + intros. inst_cofinites_with x.
      rewrite_env ((x ~ fbind_typ A1 ++ Δ3) ++ Δ2 ++ Δ1).
      eapply H1... simpl. subst. constructor...
      apply f_typing_wf in H. intuition. dependent destruction H7...
    + intros. inst_cofinites_with y.  
      rewrite_env ((y ~ fbind_typ A2 ++ Δ3) ++ Δ2 ++ Δ1).
      eapply H3... simpl. subst. constructor...
      apply f_typing_wf in H. intuition. dependent destruction H7...
Qed.

Lemma f_typing_weaken_cons_var : forall Δ e A x B,
  Δ ⊢ e : A -> 
  ⊢ᶠ (x , fbind_typ B) :: Δ ->
  (x , fbind_typ B) :: Δ ⊢ e : A.
Proof.
  intros. rewrite_env (nil ++ (x ~ fbind_typ B) ++ Δ).
  eapply f_typing_weaken; eauto.
Qed.

Lemma f_typing_weaken_cons_tvar : forall Δ e A X,
  Δ ⊢ e : A -> 
  ⊢ᶠ (X , fbind_tvar_empty) :: Δ ->
  (X , fbind_tvar_empty) :: Δ ⊢ e : A.
Proof.
  intros. rewrite_env (nil ++ (X ~ fbind_tvar_empty) ++ Δ).
  eapply f_typing_weaken; eauto.
Qed.

Lemma f_wf_env_strengthen : forall Δ1 Δ2 x A,
  ⊢ᶠ Δ2 ++ (x , fbind_typ A) :: Δ1 ->
  ⊢ᶠ Δ2 ++ Δ1.
Proof.
  intros. induction Δ2...
  - simpl in *. dependent destruction H; auto.
  - simpl in *. dependent destruction H; auto.
    + constructor; auto.
    + constructor; auto.
      eapply f_wf_typ_strengthen_var with (B:=A) (x:=x); eauto.
Qed.

Lemma f_typing_strengthen : forall Δ1 Δ2 e A x B,
  Δ2 ++ (x , fbind_typ B) :: Δ1 ⊢ e : A ->
  x `notin` fvar_in_fexp e ->
  Δ2 ++ Δ1 ⊢ e : A.
Proof.
  intros. dependent induction H; simpl in *; eauto using f_wf_typ_strengthen_var, f_wf_env_strengthen.
  - econstructor. eapply f_wf_env_strengthen; eauto. 
    apply binds_remove_mid in H0; eauto.
  - inst_cofinites_for f_typing__abs.
    intros. inst_cofinites_with x0.
    rewrite_env ((x0 ~ fbind_typ A1 ++ Δ2) ++ Δ1).
    eapply H0... reflexivity.
    rewrite fvar_in_fexp_open_fexp_wrt_fexp_upper. auto.
  - inst_cofinites_for f_typing__tabs.
    intros. inst_cofinites_with X.
    rewrite_env ((X ~ fbind_tvar_empty ++ Δ2) ++ Δ1).
    eapply H0. reflexivity.
    rewrite fvar_in_fexp_open_fexp_wrt_ftyp_upper. auto.
  - inst_cofinites_for f_typing__case A1:=A1,A2:=A2...
    + eapply IHf_typing; eauto.
    + intros. inst_cofinites_with x0. 
      rewrite_env ((x0 ~ fbind_typ A1 ++ Δ2) ++ Δ1).
      eapply H1; eauto. reflexivity.
      rewrite fvar_in_fexp_open_fexp_wrt_fexp_upper. auto.
    + intros. inst_cofinites_with y. 
      rewrite_env ((y ~ fbind_typ A2 ++ Δ2) ++ Δ1).
      eapply H3; eauto. reflexivity.
      rewrite fvar_in_fexp_open_fexp_wrt_fexp_upper. auto.
Qed.

Lemma f_typing_strengthen_cons : forall Δ e A x B,
  (x , fbind_typ B) :: Δ ⊢ e : A ->
  x `notin` fvar_in_fexp e ->
  Δ ⊢ e : A.
Proof.  
  intros. rewrite_env (nil ++ Δ).
  eapply f_typing_strengthen; eauto.
Qed.

Inductive d_sub_elab : denv -> typ -> typ -> fexp -> Prop :=
  | d_sub_elab__top : forall (Ψ:denv) (A:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ A ->
      d_sub_elab Ψ A typ_top (fexp_abs (trans_ftyp A) fexp_unit)
  | d_sub_elab__bot : forall (Ψ:denv) (B:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ B ->
      d_sub_elab Ψ typ_bot B (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_tapp (fexp_var_b 0) (trans_ftyp B)))
  | d_sub_elab__unit : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_sub_elab Ψ typ_unit typ_unit (fexp_abs ftyp_unit (fexp_var_b 0))
  | d_sub_elab__tvar : forall (Ψ:denv) (X:typvar),
      d_wf_env Ψ ->
      d_wf_typ Ψ (typ_var_f X) ->
      d_sub_elab Ψ (typ_var_f X) (typ_var_f X) (fexp_abs (ftyp_var_f X) (fexp_var_b 0))
  | d_sub_elab__arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ) (co1ᶠ co2ᶠ:fexp),
      d_sub_elab Ψ B1 A1 co1ᶠ ->
      d_sub_elab Ψ A2 B2 co2ᶠ ->
      d_sub_elab Ψ (typ_arrow A1 A2) (typ_arrow B1 B2)
        (fexp_abs (ftyp_arrow (trans_ftyp A1) (trans_ftyp A2))
                  (fexp_abs (trans_ftyp B1)
                            (fexp_app co2ᶠ
                                      (fexp_app (fexp_var_b 1)
                                                (fexp_app co1ᶠ (fexp_var_b 0))))))
  | d_sub_elab__all : forall (L:vars) (Ψ:denv) (A B:typ) (coᶠ:fexp),
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  B   (typ_var_f X) ) ) ->
      ( forall X , X \notin L -> d_sub_elab  ( X ~ dbind_stvar_empty  ++  Ψ )   (open_typ_wrt_typ  A   (typ_var_f X) )   (open_typ_wrt_typ  B   (typ_var_f X) ) (open_fexp_wrt_ftyp coᶠ (ftyp_var_f X)) ) ->
      d_sub_elab Ψ (typ_all A) (typ_all B)
        (fexp_abs (trans_ftyp (typ_all A)) (fexp_tabs (fexp_app coᶠ (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0)))))
  | d_sub_elab__alll : forall (L:vars) (Ψ:denv) (A B T:typ) (coᶠ:fexp),
      d_wneq_all Ψ B ->
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
      d_mono_typ Ψ T ->
      d_sub_elab Ψ  (open_typ_wrt_typ  A   T )  B coᶠ ->
      d_sub_elab Ψ (typ_all A) B
        (fexp_abs (trans_ftyp (typ_all A)) (fexp_app coᶠ (fexp_tapp (fexp_var_b 0) (trans_ftyp T))))
  | d_sub_elab__intersection1 : forall (Ψ:denv) (A B1 B2:typ) (co1ᶠ co2ᶠ:fexp),
      d_sub_elab Ψ A B1 co1ᶠ ->
      d_sub_elab Ψ A B2 co2ᶠ ->
      d_sub_elab Ψ A (typ_intersection B1 B2)
        (fexp_abs (trans_ftyp A)
                  (fexp_pair (fexp_app co1ᶠ (fexp_var_b 0))
                          (fexp_app co2ᶠ (fexp_var_b 0))))
  | d_sub_elab__intersection2 : forall (Ψ:denv) (A1 A2 B:typ) (coᶠ:fexp),
      d_sub_elab Ψ A1 B coᶠ ->
      d_wf_typ Ψ A2 ->
      d_sub_elab Ψ (typ_intersection A1 A2) B
        (fexp_abs (trans_ftyp (typ_intersection A1 A2)) (fexp_app coᶠ (fexp_proj1 (fexp_var_b 0))))
  | d_sub_elab__intersection3 : forall (Ψ:denv) (A1 A2 B:typ) (coᶠ:fexp),
      d_sub_elab Ψ A2 B coᶠ ->
      d_wf_typ Ψ A1 ->
      d_sub_elab Ψ (typ_intersection A1 A2) B
        (fexp_abs (trans_ftyp (typ_intersection A1 A2)) (fexp_app coᶠ (fexp_proj2 (fexp_var_b 0))))
  | d_sub_elab__union1 : forall (Ψ:denv) (A B1 B2:typ) (coᶠ:fexp),
      d_sub_elab Ψ A B1 coᶠ ->
      d_wf_typ Ψ B2 ->
      d_sub_elab Ψ A (typ_union B1 B2)
        (fexp_abs (trans_ftyp A) (fexp_inl (fexp_app coᶠ (fexp_var_b 0))))
  | d_sub_elab__union2 : forall (Ψ:denv) (A B1 B2:typ) (coᶠ:fexp),
      d_sub_elab Ψ A B2 coᶠ ->
      d_wf_typ Ψ B1 ->
      d_sub_elab Ψ A (typ_union B1 B2)
        (fexp_abs (trans_ftyp A) (fexp_inr (fexp_app coᶠ (fexp_var_b 0))))
  | d_sub_elab__union3 : forall (Ψ:denv) (A1 A2 B:typ) (co1ᶠ co2ᶠ:fexp),
      d_sub_elab Ψ A1 B co1ᶠ ->
      d_sub_elab Ψ A2 B co2ᶠ ->
      d_sub_elab Ψ (typ_union A1 A2) B
        (fexp_abs (trans_ftyp (typ_union A1 A2)) (fexp_case (fexp_var_b 0) (fexp_app co1ᶠ (fexp_var_b 0)) (fexp_app co2ᶠ (fexp_var_b 0)))).

Notation "Ψ ⊢ A <: B ↪ coᶠ" := (d_sub_elab Ψ A B coᶠ) (at level 65, A at next level, B at next level, no associativity) : type_scope.

Inductive d_infabs_elab : denv -> typ -> typ -> typ -> fexp -> Prop := 
  | d_infabs_elab__bot : forall (Ψ:denv),
      d_wf_tenv Ψ ->
      d_infabs_elab Ψ typ_bot typ_top typ_bot
        (fexp_abs (ftyp_all (ftyp_var_b 0))
              (fexp_tapp (fexp_var_b 0) (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0)))))
  | d_infabs_elab__arr : forall (Ψ:denv) (A B:typ),
      d_wf_tenv Ψ ->
      d_wf_typ Ψ A ->
      d_wf_typ Ψ B ->
      d_infabs_elab Ψ (typ_arrow A B) A B
        (fexp_abs (trans_ftyp (typ_arrow A B)) (fexp_var_b 0))
  | d_infabs_elab__all : forall (Ψ:denv) (A B C T:typ) (coᶠ:fexp),
      d_mono_typ Ψ T -> 
      d_wf_typ Ψ (typ_all A) ->
      d_infabs_elab Ψ  (open_typ_wrt_typ  A   T ) B C coᶠ ->
      d_infabs_elab Ψ (typ_all A) B C
        (fexp_abs (trans_ftyp (typ_all A))
                  (fexp_app coᶠ (fexp_tapp (fexp_var_b 0) (trans_ftyp T))))
  | d_infabs_elab__intersection1 : forall (Ψ:denv) (A1 A2 B C:typ) (coᶠ:fexp),
      d_wf_typ Ψ A2 ->
      d_infabs_elab Ψ A1 B C coᶠ ->
      d_infabs_elab Ψ (typ_intersection A1 A2) B C
        (fexp_abs (trans_ftyp (typ_intersection A1 A2))
                  (fexp_app coᶠ (fexp_proj1 (fexp_var_b 0))))
  | d_infabs_elab__intersection2 : forall (Ψ:denv) (A1 A2 B C:typ) (coᶠ:fexp),
      d_wf_typ Ψ A1 ->
      d_infabs_elab Ψ A2 B C coᶠ ->
      d_infabs_elab Ψ (typ_intersection A1 A2) B C
        (fexp_abs (trans_ftyp (typ_intersection A1 A2))
                  (fexp_app coᶠ (fexp_proj2 (fexp_var_b 0))))
  | d_infabs_elab__union : forall (Ψ:denv) (A1 A2 B1 C1 B2 C2:typ) (co1ᶠ co2ᶠ:fexp),
      d_infabs_elab Ψ A1 B1 C1 co1ᶠ ->
      d_infabs_elab Ψ A2 B2 C2 co2ᶠ ->
      d_infabs_elab Ψ (typ_union A1 A2) (typ_intersection B1 B2) (typ_union C1 C2)
        (fexp_abs (trans_ftyp (typ_union A1 A2))
                  (fexp_abs (trans_ftyp (typ_intersection B1 B2))
                            (fexp_case (fexp_var_b 1)
                                      (fexp_inl (fexp_app (fexp_app co1ᶠ (fexp_var_b 0)) (fexp_proj1 (fexp_var_b 1))))
                                      (fexp_inr (fexp_app (fexp_app co2ᶠ (fexp_var_b 0)) (fexp_proj2 (fexp_var_b 1))))))).

Notation "Ψ ⊢ A ▹ B → C ↪ coᶠ" :=   (d_infabs_elab Ψ A B C coᶠ) 
  (at level 65, A at next level, B at next level, C at next level, no associativity) : type_scope.
    
  
Inductive d_inftapp_elab : denv -> typ -> typ -> typ -> fexp -> fexp -> Prop := 
  | d_inftapp_elab__bot : forall (Ψ:denv) (B:typ),
      d_wf_tenv Ψ -> 
      d_wf_typ Ψ B ->
      d_inftapp_elab Ψ typ_bot B typ_bot
        (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_var_b 0))
        (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_var_b 0))
  | d_inftapp_elab__all : forall (Ψ:denv) (A B:typ),
      d_wf_tenv Ψ -> 
      d_wf_typ Ψ (typ_all A) ->
      d_wf_typ Ψ B ->
      d_inftapp_elab Ψ (typ_all A) B (open_typ_wrt_typ  A   B )  
        (fexp_abs (trans_ftyp (typ_all A)) (fexp_var_b 0))
        (fexp_abs (trans_ftyp (typ_all A)) (fexp_tapp (fexp_var_b 0) (trans_ftyp B)))
  | d_inftapp_elab__intersection1 : forall (Ψ:denv) (A1 A2 B C1:typ) (co1ᶠ co2ᶠ:fexp),
      d_wf_typ Ψ A2 ->
      d_inftapp_elab Ψ A1 B C1 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ (typ_intersection A1 A2) B C1
        (fexp_abs (trans_ftyp (typ_intersection A1 A2))
                  (fexp_app co1ᶠ (fexp_proj1 (fexp_var_b 0))))
        co2ᶠ
  | d_inftapp_elab__intersection2 : forall (Ψ:denv) (A1 A2 B C2:typ) (co1ᶠ co2ᶠ:fexp),
      d_wf_typ Ψ A1 ->
      d_inftapp_elab Ψ A2 B C2 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ (typ_intersection A1 A2) B C2
        (fexp_abs (trans_ftyp (typ_intersection A1 A2))
                  (fexp_app co1ᶠ (fexp_proj2 (fexp_var_b 0))))
        co2ᶠ
  | d_inftapp_elab__union : forall (Ψ:denv) (A1 A2 B C1 C2:typ) (co1ᶠ co2ᶠ co3 co4:fexp),
      d_inftapp_elab Ψ A1 B C1 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ A2 B C2 co3 co4 ->
      d_inftapp_elab Ψ (typ_union A1 A2) B (typ_union C1 C2)
        (fexp_abs (trans_ftyp (typ_union A1 A2))
                  (fexp_case (fexp_var_b 0)
                              (fexp_inl (fexp_app co2ᶠ (fexp_app co1ᶠ (fexp_var_b 0))))
                              (fexp_inr (fexp_app co4 (fexp_app co3 (fexp_var_b 0))))))
        (fexp_abs (trans_ftyp (typ_union C1 C2)) (fexp_var_b 0)).

Notation "Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ" :=
    (d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ) 
      (at level 65, A at next level, B at next level, C at next level, no associativity) : type_scope. 

Inductive d_chk_inf_elab : denv -> exp -> typing_mode -> typ -> fexp -> Prop :=
  | d_chk_inf_elab__inf_var : forall (Ψ:denv) (x:expvar) (A:typ),
      d_wf_tenv Ψ ->
      binds ( x )  ( (dbind_typ A) ) ( Ψ )  ->
      d_chk_inf_elab Ψ (exp_var_f x) typingmode__inf A
        (fexp_var_f x)
  | d_chk_inf_elab__inf_anno : forall (Ψ:denv) (e:exp) (B1:typ) (eᶠ:fexp),
      d_wf_typ Ψ B1 ->
      d_chk_inf_elab Ψ e typingmode__chk B1 eᶠ ->
      d_chk_inf_elab Ψ  ( (exp_anno e B1) )  typingmode__inf B1 eᶠ
  | d_chk_inf_elab__inf_unit : forall (Ψ:denv),
      d_wf_tenv Ψ ->
      d_chk_inf_elab Ψ exp_unit typingmode__inf typ_unit
        fexp_unit
  | d_chk_inf_elab__inf_app : forall (Ψ:denv) (e1 e2:exp) (A B C:typ) (e1ᶠ coᶠ e2ᶠ:fexp),
      d_chk_inf_elab Ψ e1 typingmode__inf A e1ᶠ ->
      d_infabs_elab Ψ A B C coᶠ ->
      d_chk_inf_elab Ψ e2 typingmode__chk B e2ᶠ ->
      d_chk_inf_elab Ψ  ( (exp_app e1 e2) ) typingmode__inf C
        (fexp_app (fexp_app coᶠ e1ᶠ) e2ᶠ)
  | d_chk_inf_elab__inf_abs_mono : forall (L:vars) (Ψ:denv) (e:exp) (A B:typ) (eᶠ:fexp),
      d_mono_typ Ψ (typ_arrow A B) ->
      ( forall x , x \notin  L  -> d_chk_inf_elab  ( x ~ (dbind_typ A)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk B (open_fexp_wrt_fexp eᶠ (fexp_var_f x)))  ->
      d_chk_inf_elab Ψ (exp_abs e) typingmode__inf (typ_arrow A B)
        (fexp_abs (trans_ftyp A) eᶠ)
  | d_chk_inf_elab__inf_tabs : forall (L:vars) (Ψ:denv) (e:exp) (A:typ) (eᶠ:fexp),
      ( forall X , X \notin  L  -> s_in X (open_typ_wrt_typ A (typ_var_f X)))  ->
      ( forall X , X \notin  L  -> d_chk_inf_elab  ( X ~ dbind_tvar_empty  ++  Ψ ) ( open_exp_wrt_typ e (typ_var_f X) ) typingmode__chk ( open_typ_wrt_typ A (typ_var_f X) ) (open_fexp_wrt_ftyp eᶠ (ftyp_var_f X)))  ->
      d_chk_inf_elab Ψ (exp_tabs (exp_anno e A)) typingmode__inf (typ_all A)
        (fexp_tabs eᶠ)
  | d_chk_inf_elab__inf_tapp : forall (Ψ:denv) (e:exp) (A B C:typ) (eᶠ co1ᶠ co2ᶠ:fexp),
      d_wf_typ Ψ B ->
      d_chk_inf_elab Ψ e typingmode__inf A eᶠ ->
      d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ ->
      d_chk_inf_elab Ψ (exp_tapp e B) typingmode__inf C
        (fexp_app co2ᶠ (fexp_app co1ᶠ eᶠ))
  | d_chk_inf_elab__chk_abs_top : forall (L:vars) (Ψ:denv) (e:exp) (eᶠ:fexp),
      ( forall x , x \notin  L  -> d_chk_inf_elab  ( x ~ (dbind_typ typ_bot)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk typ_top (open_fexp_wrt_fexp eᶠ (fexp_var_f x)))  ->
      d_chk_inf_elab Ψ (exp_abs e) typingmode__chk typ_top fexp_unit
  | d_chk_inf_elab__chk_abs : forall (L:vars) (Ψ:denv) (e:exp) (A B:typ) (eᶠ:fexp),
      d_wf_typ Ψ A ->
      ( forall x , x \notin  L  -> d_chk_inf_elab  ( x ~ (dbind_typ A)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk B (open_fexp_wrt_fexp eᶠ (fexp_var_f x)))  ->
      d_chk_inf_elab Ψ (exp_abs e) typingmode__chk (typ_arrow A B)
        (fexp_abs (trans_ftyp A) eᶠ)
  | d_chk_inf_elab__chk_sub : forall (Ψ:denv) (e:exp) ( A B:typ) (eᶠ coᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__inf A eᶠ ->
      d_sub_elab Ψ A B coᶠ ->
      d_chk_inf_elab Ψ e typingmode__chk B
        (fexp_app coᶠ eᶠ)
  | d_chk_inf_elab__chk_intersection : forall (Ψ:denv) (e:exp) (A1 A2:typ) (e1ᶠ e2ᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__chk A1 e1ᶠ ->
      d_chk_inf_elab Ψ e typingmode__chk A2 e2ᶠ ->
      d_chk_inf_elab Ψ e typingmode__chk (typ_intersection A1 A2)
        (fexp_pair e1ᶠ e2ᶠ)
  | d_chk_inf_elab__chk_union1 : forall (Ψ:denv) (e:exp) (A1 A2:typ) (eᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__chk A1 eᶠ ->
      d_wf_typ Ψ A2 ->
      d_chk_inf_elab Ψ e typingmode__chk (typ_union A1 A2)
        (fexp_inl eᶠ)
  | d_chk_inf_elab__chk_union2 : forall (Ψ:denv) (e:exp) (A1 A2:typ) (eᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__chk A2 eᶠ ->
      d_wf_typ Ψ A1 ->
      d_chk_inf_elab Ψ e typingmode__chk (typ_union A1 A2)
        (fexp_inr eᶠ).

#[local] Hint Constructors d_sub_elab d_inftapp_elab d_infabs_elab d_chk_inf_elab : core.
#[local] Hint Constructors f_typing : core.

Theorem d_sub_elab_sound: forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> Ψ ⊢ A <: B.
Proof.
  intros. induction H; eauto.
Qed.

Lemma trans_ftyp_rename_tvar : forall A X Y,
  subst_ftyp_in_ftyp (ftyp_var_f Y) X ᵗ⟦ A ⟧ = ᵗ⟦ {`Y ᵗ/ₜ X} A ⟧.
Proof.
  intros. induction A; simpl; eauto.
  - destruct_eq_atom; auto.
  - rewrite IHA1. rewrite IHA2. auto.
  - rewrite IHA. auto.
  - rewrite IHA1. rewrite IHA2. auto.
  - rewrite IHA1. rewrite IHA2. auto. 
Qed.

Lemma d_sub_elab_rename_dtvar : forall Ψ1 Ψ2 A B b X Y coᶠ,
  b = □ \/ b = ■ ->
  Ψ2 ++ (X , b) :: Ψ1  ⊢ A <: B ↪ coᶠ ->
  Y ∉ (dom (Ψ2 ++ (X, b) :: Ψ1)) ->
  (map (subst_typ_in_dbind `Y X) Ψ2) ++ (Y , b) :: Ψ1  ⊢ {`Y ᵗ/ₜ X} A <: {`Y ᵗ/ₜ X} B ↪ subst_ftyp_in_fexp (ftyp_var_f Y) X coᶠ.
Proof with eauto 6 using d_wf_typ_rename_dtvar, d_wf_env_rename_dtvar.
  intros. dependent induction H0; eauto; try solve [simpl; repeat rewrite trans_ftyp_rename_tvar; eauto 6 using d_wf_typ_rename_dtvar, d_wf_env_rename_dtvar].
  - simpl. destruct_eq_atom; auto.
    + econstructor; eauto... destruct H; eauto.
    + econstructor; eauto...
      dependent destruction H0; apply binds_remove_mid in H; apply binds_app_iff in H; destruct H...
      * econstructor... apply binds_app_2. apply binds_map with (f:=(subst_typ_in_dbind ` Y X)) in H...
      * eapply d_wf_typ__stvar. apply binds_app_2. apply binds_map with (f:=(subst_typ_in_dbind ` Y X)) in H...
  - simpl. repeat rewrite trans_ftyp_rename_tvar.
    replace (ftyp_all ᵗ⟦ {` Y ᵗ/ₜ X} A ⟧) with (ᵗ⟦ typ_all ( {` Y ᵗ/ₜ X} A ) ⟧) by auto.
    inst_cofinites_for d_sub_elab__all; intros; inst_cofinites_with X0; auto.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      replace (ftyp_var_f X0) with (subst_ftyp_in_ftyp (ftyp_var_f Y) X (ftyp_var_f X0))...
      * rewrite <- subst_ftyp_in_fexp_open_fexp_wrt_ftyp...
        rewrite_env (map (subst_typ_in_dbind ` Y X) (X0 ~ ■ ++ Ψ2) ++ (Y, b) :: Ψ1)...
      * simpl. destruct_eq_atom...
  - simpl. repeat rewrite trans_ftyp_rename_tvar.
    inst_cofinites_for d_sub_elab__alll; intros; inst_cofinites_with X0; eauto...
    + eapply d_wneq_all_rename_dtvar; auto.
      eapply d_sub_elab_sound in H2.
      apply d_sub_d_wf_env in H2...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + eapply d_mono_typ_rename_dtvar...
      apply d_sub_elab_sound in H2. apply d_sub_d_wf_env in H2...
    + rewrite <- subst_typ_in_typ_open_typ_wrt_typ...
  - simpl; repeat rewrite trans_ftyp_rename_tvar... econstructor...
  - simpl; repeat rewrite trans_ftyp_rename_tvar... econstructor...
  - simpl; repeat rewrite trans_ftyp_rename_tvar... econstructor...
Qed.

Lemma d_sub_elab_rename_tvar_cons : forall Ψ A B X Y coᶠ b,
  b = □ \/ b = ■ ->
  Y `notin` dom ((X, b) :: Ψ) ->
  (X , b) :: Ψ ⊢ A <: B ↪ coᶠ ->
  (Y , b) :: Ψ ⊢ {`Y ᵗ/ₜ X} A <: {`Y ᵗ/ₜ X} B ↪ subst_ftyp_in_fexp (ftyp_var_f Y) X coᶠ.
Proof.
  intros. rewrite_env ((map (subst_typ_in_dbind `Y X) nil) ++ (Y , b) :: Ψ). 
  eapply d_sub_elab_rename_dtvar; eauto.
Qed.

Ltac rewrite_close_open_subst :=
  match goal with
  | H : _ |- context [open_ftyp_wrt_ftyp (close_ftyp_wrt_ftyp ?X ?A) ?B] =>
      erewrite (subst_ftyp_in_ftyp_intro X (close_ftyp_wrt_ftyp X A)) by apply close_ftyp_wrt_ftyp_notin;
      rewrite open_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp
  | H : _ |- context [open_fexp_wrt_ftyp (close_fexp_wrt_ftyp ?X ?e) ?B] =>
      erewrite (subst_ftyp_in_fexp_intro X (close_fexp_wrt_ftyp X e)) by apply close_fexp_wrt_ftyp_notin;
      rewrite open_fexp_wrt_ftyp_close_fexp_wrt_ftyp
  | H : _ |- context [open_fexp_wrt_fexp (close_fexp_wrt_fexp ?x ?e) ?e'] =>
      erewrite (subst_fexp_in_fexp_intro x (close_fexp_wrt_fexp x e)) by apply close_fexp_wrt_fexp_notin;
      rewrite open_fexp_wrt_fexp_close_fexp_wrt_fexp
  | H : _ |- _ => idtac
  end.

Theorem d_sub_elab_complete: forall Ψ A B,
  Ψ ⊢ A <: B -> exists coᶠ, Ψ ⊢ A <: B ↪ coᶠ.
Proof with auto.
  intros. induction H; eauto 4; try solve [destruct_conj; eauto 4].
  - pick fresh X. inst_cofinites_with_keep X.
    destruct H3 as [coᶠ ?].
    exists 
      (fexp_abs (trans_ftyp (typ_all A)) (fexp_tabs (fexp_app (close_fexp_wrt_ftyp X coᶠ) (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0))))).
    inst_cofinites_for d_sub_elab__all; intros; inst_cofinites_with X0; auto.
    erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X:=X)...
    erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X:=X) (A:=B)...
    erewrite (subst_ftyp_in_fexp_intro X (close_fexp_wrt_ftyp X coᶠ)) by apply close_fexp_wrt_ftyp_notin.
    + rewrite open_fexp_wrt_ftyp_close_fexp_wrt_ftyp.
      eapply d_sub_elab_rename_tvar_cons; eauto.
Qed.

Theorem d_infabs_elab_sound : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ -> Ψ ⊢ A ▹ B → C.
Proof.  
  intros; induction H; eauto.
Qed.

Theorem d_infabs_elab_complete : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> exists coᶠ, Ψ ⊢ A ▹ B → C ↪ coᶠ.
Proof with eauto 4.
  intros. induction H; try solve [destruct_conj; eauto].
Qed.

Theorem d_inftapp_elab_sound : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ -> Ψ ⊢ A ○ B ⇒⇒ C.
Proof.
  intros. induction H; auto 6.
Qed.

Theorem d_inftapp_elab_complete : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C -> exists co1ᶠ co2ᶠ, Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ.
Proof.
  intros. induction H; try solve [destruct_conj; eauto].
Qed.

Theorem d_chk_inf_elab_sound : forall Ψ e mode A eᶠ,
  d_chk_inf_elab Ψ e mode A eᶠ -> d_chk_inf Ψ e mode A.
Proof with eauto using d_sub_elab_sound, d_infabs_elab_sound, d_inftapp_elab_sound.
  intros. induction H...
Qed.

Lemma d_infabs_elab_rename_tvar : forall Ψ1 Ψ2 X Y A B C coᶠ,
  Ψ2 ++ (X , □) :: Ψ1 ⊢ A ▹ B → C ↪ coᶠ ->
  Y `notin` dom (Ψ2 ++ (X , □) :: Ψ1) ->
  (map (subst_typ_in_dbind (`Y) X) Ψ2) ++ (Y , □) :: Ψ1 ⊢ {`Y ᵗ/ₜ X} A ▹ {`Y ᵗ/ₜ X} B → {`Y ᵗ/ₜ X} C ↪ subst_ftyp_in_fexp (ftyp_var_f Y) X coᶠ.
Proof with eauto.
  intros. dependent induction H; eauto; try solve [simpl; 
    repeat rewrite trans_ftyp_rename_tvar; 
    try econstructor; 
    eauto 6 using d_wf_typ_rename_dtvar, d_mono_typ_rename_dtvar, d_wf_tenv_rename_tvar, d_wf_env_rename_dtvar].
  - simpl. repeat rewrite trans_ftyp_rename_tvar.
    econstructor; eauto.
    + eapply d_mono_typ_rename_dtvar...
      eapply d_infabs_elab_sound in H1.
      apply d_infabs_d_wf_env in H1...
    + replace (typ_all ({` Y ᵗ/ₜ X} A)) with ({` Y ᵗ/ₜ X} typ_all A) by auto.
      eapply d_wf_typ_rename_dtvar; eauto.
    + rewrite <- subst_typ_in_typ_open_typ_wrt_typ; eauto.
Qed.

Lemma d_inftapp_elab_rename_tvar : forall Ψ1 Ψ2 X Y A B C co1ᶠ co2ᶠ,
  Ψ2 ++ (X , □) :: Ψ1 ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  Y `notin` dom (Ψ2 ++ (X , □) :: Ψ1) ->
  (map (subst_typ_in_dbind (`Y) X) Ψ2) ++ (Y , □) :: Ψ1 ⊢ {`Y ᵗ/ₜ X} A ○ {`Y ᵗ/ₜ X} B ⇒⇒ {`Y ᵗ/ₜ X} C ↪ subst_ftyp_in_fexp (ftyp_var_f Y) X co1ᶠ | subst_ftyp_in_fexp (ftyp_var_f Y) X co2ᶠ.
Proof.
  intros. dependent induction H; eauto; try solve [simpl; 
    repeat rewrite trans_ftyp_rename_tvar; 
    try econstructor; 
    eauto 6 using d_wf_typ_rename_dtvar, d_mono_typ_rename_dtvar, d_wf_tenv_rename_tvar, d_wf_env_rename_dtvar].
  - simpl. repeat rewrite trans_ftyp_rename_tvar.
    rewrite subst_typ_in_typ_open_typ_wrt_typ; auto.
    econstructor; eauto using d_wf_typ_rename_dtvar, d_mono_typ_rename_dtvar, d_wf_tenv_rename_tvar, d_wf_env_rename_dtvar.
    replace (typ_all ({` Y ᵗ/ₜ X} A)) with ({` Y ᵗ/ₜ X} typ_all A) by auto.
    eapply d_wf_typ_rename_dtvar; eauto.
Qed.

Lemma d_chk_inf_elab_rename_tvar : forall Ψ1 Ψ2 X Y e A eᶠ mode,
  d_chk_inf_elab (Ψ2 ++ (X , □) :: Ψ1) e mode A eᶠ ->
  Y `notin` dom (Ψ2 ++ (X , □) :: Ψ1) ->
  d_chk_inf_elab (map (subst_typ_in_dbind (`Y) X) Ψ2 ++ (Y, □) :: Ψ1) ({` Y ᵉ/ₜ X} e) mode ({` Y ᵗ/ₜ X} A) (subst_ftyp_in_fexp (ftyp_var_f Y) X eᶠ).
Proof with eauto using d_wf_typ_rename_dtvar, d_mono_typ_rename_dtvar, d_wf_tenv_rename_tvar.
  intros. dependent induction H; 
    try solve [simpl; repeat rewrite trans_ftyp_rename_tvar;
               eauto using d_wf_typ_rename_dtvar, d_mono_typ_rename_dtvar, d_wf_tenv_rename_tvar, d_infabs_elab_rename_tvar].
  - simpl. econstructor; eauto...
    apply d_binds_var_typ_rename_tvar; eauto.
  - simpl. repeat rewrite trans_ftyp_rename_tvar. 
    inst_cofinites_for d_chk_inf_elab__inf_abs_mono; intros; inst_cofinites_with X0; eauto.
    + replace (typ_arrow ({` Y ᵗ/ₜ X} A) ({` Y ᵗ/ₜ X} B)) with ({` Y ᵗ/ₜ X} (typ_arrow A B)) by auto.
      eapply d_mono_typ_rename_dtvar; eauto.
      inst_cofinites_by L. apply d_chk_inf_elab_sound in H0.
      apply d_chk_inf_wf_env in H0. dependent destruction H0...
    + replace (exp_var_f x) with ({` Y ᵉ/ₜ X} (exp_var_f x)) by auto. 
      rewrite <- subst_typ_in_exp_open_exp_wrt_exp; eauto.
      rewrite_env (map (subst_typ_in_dbind (`Y) X) (x ~ dbind_typ A ++ Ψ2) ++ (Y, □) :: Ψ1).
      replace (fexp_var_f x) with (subst_ftyp_in_fexp (ftyp_var_f Y) X (fexp_var_f x)) by auto.
      rewrite <- subst_ftyp_in_fexp_open_fexp_wrt_fexp.
      eapply H1; eauto.
  - simpl. repeat rewrite trans_ftyp_rename_tvar. 
    inst_cofinites_for d_chk_inf_elab__inf_tabs; intros; inst_cofinites_with X0; eauto. 
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2...
      replace (ftyp_var_f X0) with (subst_ftyp_in_ftyp (ftyp_var_f Y) X (ftyp_var_f X0)) by (simpl; destruct_eq_atom; auto).
      rewrite <- subst_ftyp_in_fexp_open_fexp_wrt_ftyp...
      rewrite_env (map (subst_typ_in_dbind (`Y) X) (X0 ~ □ ++ Ψ2) ++ (Y, □) :: Ψ1)...
  - simpl. repeat rewrite trans_ftyp_rename_tvar.
    econstructor; eauto.
    + eapply d_wf_typ_rename_dtvar...
    + eapply d_inftapp_elab_rename_tvar; eauto.
  - simpl. repeat rewrite trans_ftyp_rename_tvar. 
    inst_cofinites_for d_chk_inf_elab__chk_abs_top eᶠ:=(subst_ftyp_in_fexp (ftyp_var_f Y) X eᶠ); intros; inst_cofinites_with x; eauto.
    replace (exp_var_f x) with ({` Y ᵉ/ₜ X} (exp_var_f x)) by auto.
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp; eauto.
    replace (fexp_var_f x) with (subst_ftyp_in_fexp (ftyp_var_f Y) X (fexp_var_f x)) by auto.
    rewrite <- subst_ftyp_in_fexp_open_fexp_wrt_fexp; eauto.
    rewrite_env (map (subst_typ_in_dbind (`Y) X) (x ~ dbind_typ typ_bot ++ Ψ2) ++ (Y, □) :: Ψ1).
    eapply H0; eauto.
  - simpl. repeat rewrite trans_ftyp_rename_tvar. 
    inst_cofinites_for d_chk_inf_elab__chk_abs; eauto...
    + intros. inst_cofinites_with x.
      replace (exp_var_f x) with ({` Y ᵉ/ₜ X} (exp_var_f x)) by auto.
      rewrite <- subst_typ_in_exp_open_exp_wrt_exp.
      rewrite_env (map (subst_typ_in_dbind (`Y) X) (x ~ dbind_typ A ++ Ψ2) ++ (Y, □) :: Ψ1).
      replace (fexp_var_f x) with (subst_ftyp_in_fexp (ftyp_var_f Y) X (fexp_var_f x)) by auto.
      rewrite <- subst_ftyp_in_fexp_open_fexp_wrt_fexp.
      eapply H1...
  - simpl. econstructor; eauto.
    eapply d_sub_elab_rename_dtvar; eauto.
Qed.

Corollary d_chk_inf_elab_rename_tvar_cons : forall Ψ X Y e A eᶠ mode,
  Y `notin` dom ((X , □) :: Ψ) ->
  d_chk_inf_elab ((X , □) :: Ψ) e mode A eᶠ ->
  d_chk_inf_elab ((Y , □) :: Ψ) ({` Y ᵉ/ₜ X} e) mode ({` Y ᵗ/ₜ X} A) (subst_ftyp_in_fexp (ftyp_var_f Y) X eᶠ).
Proof.
  intros. rewrite_env (map (subst_typ_in_dbind (`Y) X) nil ++ (Y , □) :: Ψ).
  apply d_chk_inf_elab_rename_tvar; eauto.
Qed.

Lemma d_sub_elab_rename_var : forall Ψ1 Ψ2 x y A B C coᶠ,
  Ψ2 ++ (x , dbind_typ C) :: Ψ1 ⊢ A <: B ↪ coᶠ ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ C) :: Ψ1) ->
  Ψ2 ++ (y , dbind_typ C) :: Ψ1 ⊢ A <: B ↪ subst_fexp_in_fexp (fexp_var_f y) x coᶠ.
Proof with eauto 6 using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_env_rename_var.
  intros. dependent induction H; eauto; try solve 
    [simpl; try solve [constructor; eauto using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_env_rename_var]].
  - simpl. inst_cofinites_for d_sub_elab__all...
    intros. inst_cofinites_with X. eauto.
    rewrite <- subst_fexp_in_fexp_open_fexp_wrt_ftyp...
    rewrite_env ((X ~ ■ ++ Ψ2) ++ (y, dbind_typ C) :: Ψ1)...
  - inst_cofinites_for d_sub_elab__alll...
    eapply d_wneq_all_rename_var; eauto.
Qed.

Lemma d_infabs_elab_rename_var : forall Ψ1 Ψ2 x y A B C D coᶠ,
  Ψ2 ++ (x , dbind_typ D) :: Ψ1 ⊢ A ▹ B → C ↪ coᶠ ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ C) :: Ψ1) ->
  Ψ2 ++ (y , dbind_typ D) :: Ψ1 ⊢ A ▹ B → C ↪ subst_fexp_in_fexp (fexp_var_f y) x coᶠ.
Proof with eauto 6 using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_tenv_rename_var.
  intros. dependent induction H; eauto; try solve [simpl; constructor; 
    eauto using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_tenv_rename_var].
Qed.

Lemma d_inftapp_elab_rename_var : forall Ψ1 Ψ2 x y A B C D co1ᶠ co2ᶠ,
  Ψ2 ++ (x , dbind_typ D) :: Ψ1 ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ C) :: Ψ1) ->
  Ψ2 ++ (y , dbind_typ D) :: Ψ1 ⊢ A ○ B ⇒⇒ C ↪ subst_fexp_in_fexp (fexp_var_f y) x co1ᶠ | subst_fexp_in_fexp (fexp_var_f y) x co2ᶠ.
Proof.
  intros. dependent induction H; eauto; try solve [simpl; constructor; 
    eauto using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_tenv_rename_var].
Qed.

Lemma d_chk_inf_elab_rename_var : forall Ψ1 Ψ2 x y e A B eᶠ mode,
  d_chk_inf_elab (Ψ2 ++ (x , dbind_typ B) :: Ψ1) e mode A eᶠ ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ B) :: Ψ1) ->
  d_chk_inf_elab (Ψ2 ++ (y , dbind_typ B) :: Ψ1) ({exp_var_f y ᵉ/ₑ x} e) mode A (subst_fexp_in_fexp (fexp_var_f y) x eᶠ).
Proof with eauto using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_tenv_rename_var.
  intros. dependent induction H; 
    try solve [simpl; eauto using d_wf_typ_rename_var, d_mono_typ_rename_var, d_wf_tenv_rename_var, d_sub_elab_rename_var, d_infabs_elab_rename_var, d_inftapp_elab_rename_var].
  - simpl. destruct_eq_atom...
    + econstructor...
      assert (x ~ B ∈ᵈ (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) by auto. unify_binds.
    + econstructor... apply binds_remove_mid in H0...
      apply binds_weaken_mid...
  - simpl. inst_cofinites_for d_chk_inf_elab__inf_abs_mono; eauto...
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} (exp_var_f x0)) by (simpl; destruct_eq_atom; auto).
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
    replace (fexp_var_f x0) with (subst_fexp_in_fexp (fexp_var_f y) x (fexp_var_f x0)) by (simpl; destruct_eq_atom; auto).
    rewrite <- subst_fexp_in_fexp_open_fexp_wrt_fexp...
    rewrite_env ((x0 ~ dbind_typ A ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - simpl. inst_cofinites_for d_chk_inf_elab__inf_tabs; intros; inst_cofinites_with X; auto.
    + rewrite <- subst_exp_in_exp_open_exp_wrt_typ...
      rewrite <- subst_fexp_in_fexp_open_fexp_wrt_ftyp...
      rewrite_env ((X ~ □ ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - simpl. inst_cofinites_for d_chk_inf_elab__chk_abs_top eᶠ:=(subst_fexp_in_fexp (fexp_var_f y) x eᶠ).
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} (exp_var_f x0)) by (simpl; destruct_eq_atom; auto).
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
    replace (fexp_var_f x0) with (subst_fexp_in_fexp (fexp_var_f y) x (fexp_var_f x0)) by (simpl; destruct_eq_atom; auto).
    rewrite <- subst_fexp_in_fexp_open_fexp_wrt_fexp...
    rewrite_env ((x0 ~ dbind_typ typ_bot ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - simpl. inst_cofinites_for d_chk_inf_elab__chk_abs.
    + eapply d_wf_typ_rename_var; eauto.
    + intros. inst_cofinites_with x0. 
      replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} (exp_var_f x0)) by (simpl; destruct_eq_atom; auto).
      rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
      replace (fexp_var_f x0) with (subst_fexp_in_fexp (fexp_var_f y) x (fexp_var_f x0)) by (simpl; destruct_eq_atom; auto).
      rewrite <- subst_fexp_in_fexp_open_fexp_wrt_fexp...
      rewrite_env ((x0 ~ dbind_typ A ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
Qed.

Corollary d_chk_inf_elab_rename_var_cons : forall Ψ x y e A B eᶠ mode,
  d_chk_inf_elab ((x ~ dbind_typ B) ++ Ψ) e mode A eᶠ ->
  y `notin` dom ((x ~ dbind_typ B) ++ Ψ) ->
  d_chk_inf_elab ((y ~ dbind_typ B) ++ Ψ) ({exp_var_f y ᵉ/ₑ x} e) mode A (subst_fexp_in_fexp (fexp_var_f y) x eᶠ).
Proof.
  intros. rewrite_env (nil ++ (y ~ dbind_typ B) ++ Ψ).
  apply d_chk_inf_elab_rename_var; eauto.
Qed.

Theorem d_chk_inf_elab_complete : forall Ψ e mode A,
  d_chk_inf Ψ e mode A -> exists eᶠ, d_chk_inf_elab Ψ e mode A eᶠ.
Proof.
  intros. induction H; try solve [destruct_conj; eauto]. 
  - apply d_infabs_elab_complete in H0...
    destruct_conj; eauto.
  (* λx. e => τ1 -> τ2 *)
  - pick fresh x. inst_cofinites_with x.
    destruct H1 as [eᶠ].
    exists (fexp_abs (trans_ftyp A) (close_fexp_wrt_fexp x eᶠ)).
    inst_cofinites_for d_chk_inf_elab__inf_abs_mono; eauto.
    intros. rewrite_close_open_subst.
    erewrite <- subst_exp_in_exp_open_exp_wrt_exp_var2; eauto.
    eapply d_chk_inf_elab_rename_var_cons; eauto.
  - pick fresh X. inst_cofinites_with X (keep).
    destruct H2 as [eᶠ].
    exists (fexp_tabs (close_fexp_wrt_ftyp X eᶠ)).
    inst_cofinites_for d_chk_inf_elab__inf_tabs; intros; inst_cofinites_with X0.
    + auto.
    + rewrite_close_open_subst. 
      erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
      erewrite <- subst_typ_in_exp_open_exp_wrt_typ_tvar2; eauto.
      eapply d_chk_inf_elab_rename_tvar_cons; eauto.
  - apply d_inftapp_elab_complete in H1.
    destruct_conj; eauto.
  (* λx. e <= ⊤ *)
  - exists fexp_unit...
    pick fresh x. inst_cofinites_with x.
    destruct H0 as [eᶠ].
    inst_cofinites_for d_chk_inf_elab__chk_abs_top eᶠ:=(close_fexp_wrt_fexp x eᶠ).
    intros.
    rewrite_close_open_subst.
    erewrite <- subst_exp_in_exp_open_exp_wrt_exp_var2; eauto.
    eapply d_chk_inf_elab_rename_var_cons; eauto.
  - pick fresh x. inst_cofinites_with x.
    destruct H1 as [eᶠ].
    exists (fexp_abs (trans_ftyp A1) (close_fexp_wrt_fexp x eᶠ)).
    inst_cofinites_for d_chk_inf_elab__chk_abs; eauto.
    intros. rewrite_close_open_subst.
    erewrite <- subst_exp_in_exp_open_exp_wrt_exp_var2; eauto.
    eapply d_chk_inf_elab_rename_var_cons; eauto.
  - apply d_sub_elab_complete in H0.
    destruct_conj; eauto.
Qed.


Ltac solve_lc_fexp_base :=
  match goal with
    | _ : _ |- forall x , _ => intros
    | _ : _ |- context [open_fexp_wrt_fexp ?e1 ?e2] =>  unfold open_fexp_wrt_fexp; simpl; eauto
    | _ : _ |- context [open_ftyp_wrt_ftyp ?A1 ?A2] =>  unfold open_ftyp_wrt_ftyp; simpl; eauto
    | H : lc_fexp ?e |- context [open_fexp_wrt_fexp_rec ?n ?e1 ?e] => rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto
  end.

Lemma d_sub_elab_lc_ftyp : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> lc_ftyp (trans_ftyp A) /\ lc_ftyp (trans_ftyp B).
Proof.
  intros. apply d_sub_elab_sound in H.
  apply d_sub_d_wf in H.
  intuition; eauto using trans_ftyp_lc_ftyp.
Qed.

Lemma d_sub_elab_lc_ftyp1 : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> lc_ftyp (trans_ftyp A).
Proof.
  intros. apply d_sub_elab_lc_ftyp in H. intuition.
Qed.

Lemma d_sub_elab_lc_ftyp2 : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> lc_ftyp (trans_ftyp B).
Proof.
  intros. apply d_sub_elab_lc_ftyp in H. intuition.
Qed.

Lemma d_infabs_elab_lc_ftyp : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ -> 
  lc_ftyp (trans_ftyp A) /\ lc_ftyp (trans_ftyp B) /\ lc_ftyp (trans_ftyp C).
Proof.
  intros. apply d_infabs_elab_sound in H.
  apply d_infabs_d_wf in H.
  intuition; eauto using trans_ftyp_lc_ftyp.
Qed.

Corollary d_infabs_elab_lc_ftyp1 : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ ->
  lc_ftyp (trans_ftyp A).
Proof.
  intros. apply d_infabs_elab_lc_ftyp in H. intuition.  
Qed.

Corollary d_infabs_elab_lc_ftyp2 : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ ->
  lc_ftyp (trans_ftyp B).
Proof.
  intros. apply d_infabs_elab_lc_ftyp in H. intuition.
Qed.

Corollary d_infabs_elab_lc_ftyp3 : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ ->
  lc_ftyp (trans_ftyp C). 
Proof.
  intros. apply d_infabs_elab_lc_ftyp in H. intuition.
Qed.

Lemma d_inftapp_elab_lc_ftyp : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ -> 
  lc_ftyp (trans_ftyp A) /\ lc_ftyp (trans_ftyp B) /\ lc_ftyp (trans_ftyp C).
Proof.
  intros. apply d_inftapp_elab_sound in H.
  apply d_inftapp_d_wf in H.
  intuition; eauto using trans_ftyp_lc_ftyp.
Qed.

Corollary d_inftapp_elab_lc_ftyp1 : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  lc_ftyp ᵗ⟦ A ⟧.
Proof.
  intros. apply d_inftapp_elab_lc_ftyp in H. intuition.
Qed.

Corollary d_inftapp_elab_lc_ftyp2 : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  lc_ftyp ᵗ⟦ B ⟧.
Proof.
  intros. apply d_inftapp_elab_lc_ftyp in H. intuition.
Qed.

Corollary d_inftapp_elab_lc_ftyp3 : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  lc_ftyp ᵗ⟦ C ⟧.
Proof.
  intros. apply d_inftapp_elab_lc_ftyp in H. intuition.
Qed.

Ltac solve_lc_fexp := 
  repeat
    try solve_lc_fexp_base;
    try match goal with 
      | H : ?Ψ ⊢ ?A <: ?B ↪ ?coᶠ |- lc_ftyp (trans_ftyp ?A) => eapply d_sub_elab_lc_ftyp1; eauto
      | H : ?Ψ ⊢ ?A <: ?B ↪ ?coᶠ |- lc_ftyp (trans_ftyp ?B) => eapply d_sub_elab_lc_ftyp2; eauto
      | H : ?Ψ ⊢ ?A ▹ ?B → ?C ↪ ?co |- lc_ftyp (trans_ftyp ?A) => eapply d_infabs_elab_lc_ftyp1; eauto
      | H : ?Ψ ⊢ ?A ▹ ?B → ?C ↪ ?co |- lc_ftyp (trans_ftyp ?B) => eapply d_infabs_elab_lc_ftyp2; eauto
      | H : ?Ψ ⊢ ?A ▹ ?B → ?C ↪ ?co |- lc_ftyp (trans_ftyp ?C) => eapply d_infabs_elab_lc_ftyp3; eauto
      | H : ?Ψ ⊢ ?A ○ ?B ⇒⇒ ?C ↪ ?co1ᶠ | ?co2ᶠ |- lc_ftyp (trans_ftyp ?A) => eapply d_inftapp_elab_lc_ftyp1; eauto
      | H : ?Ψ ⊢ ?A ○ ?B ⇒⇒ ?C ↪ ?co1ᶠ | ?co2ᶠ |- lc_ftyp (trans_ftyp ?B) => eapply d_inftapp_elab_lc_ftyp2; eauto
      | H : ?Ψ ⊢ ?A ○ ?B ⇒⇒ ?C ↪ ?co1ᶠ | ?co2ᶠ |- lc_ftyp (trans_ftyp ?C) => eapply d_inftapp_elab_lc_ftyp3; eauto
    end;
    econstructor;
    eauto.

Hint Extern 2 (lc_ftyp ?A) => solve_lc_fexp : core.
Hint Extern 1 (lc_fexp ?A) => solve_lc_fexp : core.

Theorem d_sub_elab_lc_fexp : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> lc_fexp coᶠ.
Proof with eauto.
  intros. induction H...
  - solve_lc_fexp.
    + simpl. pick fresh X. inst_cofinites_with X.
      apply d_sub_elab_sound in H1.
      apply d_sub_d_wf in H1. intuition.
      apply d_wf_typ_lc_typ in H1.
      eapply lc_ftyp_all_exists with (X1:=X)...
      replace (ftyp_var_f X) with (trans_ftyp (typ_var_f X))...
      rewrite <- trans_ftyp_open_typ_wrt_typ...
    + intros. unfold open_fexp_wrt_fexp. simpl. 
      pick fresh X. apply lc_fexp_tabs_exists with (X1:=X). 
      unfold open_fexp_wrt_ftyp. simpl. constructor.
      * inst_cofinites_with X.
        apply degree_fexp_wrt_fexp_of_lc_fexp in H2 as Hdeg.
        apply degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_inv_mutual in Hdeg.
        rewrite open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp_mutual...
      * solve_lc_fexp.
  - solve_lc_fexp.
    simpl. pick fresh X. inst_cofinites_with X. 
    apply lc_ftyp_all_exists with (X1:=X)...
    apply d_sub_elab_sound in H2.
    apply d_sub_d_wf_typ1 in H2.
    apply d_wf_typ_lc_typ in H2.
    eapply lc_typ_open_stvar_subst_mono with (X:=X) in H2; eauto.
    replace (ftyp_var_f X) with (trans_ftyp (typ_var_f X))...
    rewrite <- trans_ftyp_open_typ_wrt_typ...
  - simpl...
  - simpl...
  - simpl...
Qed.

Theorem d_infabs_elab_lc_fexp : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ -> lc_fexp coᶠ.
Proof with eauto.
  intros. induction H...
  - simpl...
  - simpl...
  - simpl...
Qed.

Theorem d_inftapp_elab_lc_fexp : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ -> lc_fexp co1ᶠ /\ lc_fexp co2ᶠ.
Proof with eauto.
  intros. induction H...
  - intuition... simpl...
  - intuition... simpl...
  - intuition; simpl...
Qed.

Theorem d_chk_inf_elab_lc_fexp : forall Ψ e A eᶠ mode,
  d_chk_inf_elab Ψ e mode A eᶠ -> lc_fexp eᶠ.
Proof with eauto using d_sub_elab_lc_fexp, d_infabs_elab_lc_fexp, d_inftapp_elab_lc_fexp.
  intros. induction H; eauto; simpl...
  - pick fresh x.
    apply lc_fexp_abs_exists with (x1:=x)...
    dependent destruction H.
    apply d_mono_typ_d_wf_typ in H.
    apply d_wf_typ_lc_typ in H...
  - apply d_inftapp_elab_lc_fexp in H1. intuition.
Qed.

Ltac solve_f_wf_env :=
  match goal with 
    | H : ⊢ᵈ ?Ψ |- f_wf_env (trans_env ?Ψ) => eapply trans_env_wf_env_wf_fenv; eauto
    | H : ⊢ᵈₜ ?Ψ |- f_wf_env (trans_env ?Ψ) => eapply trans_env_wf_tenv_wf_fenv; eauto
  end.

Hint Extern 1 (f_wf_env ?Ψ) => solve_f_wf_env : core.

Ltac destruct_f_wf_typ :=
  repeat
    match goal with
      | H : f_wf_typ ?Δ (ftyp_arrow ?A ?B) |- _ => dependent destruction H
    end.

Ltac gen_wf_trans_typ :=
  (repeat 
  match goal with
    | H : ?Ψ ᵗ⊢ᵈ ?A |- _ => 
      let H1 := fresh "H" in 
      apply trans_ftyp_wf in H as H1;
      destruct_f_wf_typ;
      generalize dependent H
  end);
  intros.

Ltac gen_f_typing_wf_typ :=
  (repeat 
  match goal with
    | H : ?Ψ ⊢ ?e : ?A |- _ => 
      let H1 := fresh "H" in 
      apply f_typing_wf in H as H1;
      destruct_conj; 
      destruct_f_wf_typ;
      generalize dependent H
  end);
  intros.

Ltac solve_f_wf_typ :=
  gen_wf_trans_typ;
  gen_f_typing_wf_typ;
  repeat (constructor; simpl; eauto).

Theorem d_sub_elab_sound_f : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> ⟦ Ψ ⟧ ⊢ coᶠ : ftyp_arrow ᵗ⟦ A ⟧ ᵗ⟦ B ⟧.
Proof with eauto 6 using f_wf_typ, f_wf_env, d_sub_elab_lc_fexp, d_infabs_elab_lc_fexp.
  intros. induction H...
  - inst_cofinites_for f_typing__abs. intros. 
    unfold open_fexp_wrt_fexp. simpl.
    solve_f_wf_typ. 
  - inst_cofinites_for f_typing__abs. intros. 
    unfold open_fexp_wrt_fexp. simpl. 
    replace (ᵗ⟦ B ⟧) with (open_ftyp_wrt_ftyp (ftyp_var_b 0) ᵗ⟦ B ⟧) at 2 by auto.
    apply f_typing__tapp...
    apply f_wf_typ_weaken_cons... solve_f_wf_typ...
    econstructor... econstructor; auto.
    + inst_cofinites_for f_wf_typ__all... intros... 
      econstructor... 
  - inst_cofinites_for f_typing__abs. intros. 
    unfold open_fexp_wrt_fexp. simpl...
    eauto 10 using f_wf_typ, f_wf_env.
    econstructor... econstructor...
  - inst_cofinites_for f_typing__abs. intros. 
    unfold open_fexp_wrt_fexp. simpl...
    econstructor... solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs. intros.
    simpl. 
    unfold open_fexp_wrt_fexp. simpl...
    inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__app with (A1:=ᵗ⟦ A2 ⟧)...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    eapply f_typing_weaken_cons_var; eauto. eapply f_typing_weaken_cons_var...
    solve_f_wf_typ.
    solve_f_wf_typ. apply f_wf_typ_weaken_cons...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    eapply f_typing__app with (A1:=ᵗ⟦ A1 ⟧)...
    econstructor...
    solve_f_wf_typ. apply f_wf_typ_weaken_cons...
    eapply f_typing__app with (A1:=ᵗ⟦ B1 ⟧)...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    eapply f_typing_weaken_cons_var; eauto. eapply f_typing_weaken_cons_var...
    solve_f_wf_typ.
    solve_f_wf_typ. apply f_wf_typ_weaken_cons...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    econstructor...
    solve_f_wf_typ. apply f_wf_typ_weaken_cons...
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    inst_cofinites_for f_typing__tabs; intros. 
    inst_cofinites_with X (keep). 
    unfold open_fexp_wrt_fexp. simpl...
    apply d_sub_elab_lc_fexp in H2 as Hlc.
    apply degree_fexp_wrt_fexp_of_lc_fexp in Hlc.
    apply degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_inv_mutual in Hlc.
    rewrite open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp_mutual...
    unfold open_fexp_wrt_ftyp. simpl.
    eapply f_typing__app with (A1:=ᵗ⟦ A ᵗ^ₜ X  ⟧)...
    + replace (ftyp_var_f X) with (trans_ftyp (typ_var_f X))...
      rewrite <- trans_ftyp_open_typ_wrt_typ. 
      rewrite_env ((X ~ fbind_tvar_empty) ++ (x ~ fbind_typ (ftyp_all ᵗ⟦ A ⟧)) ++ ⟦ Ψ ⟧).
      apply f_typing_weaken...
      solve_f_wf_typ. dependent destruction H9...
      inst_cofinites_for f_wf_typ__all. intros. inst_cofinites_with X0.
      solve_f_wf_typ.
      simpl in *. rewrite trans_ftyp_open_typ_wrt_typ in *. auto.
    + rewrite trans_ftyp_open_typ_wrt_typ. eapply f_typing__tapp.
      econstructor...
      eapply f_typing_weaken_cons_tvar...
      * apply f_typing__var...
        solve_f_wf_typ. 
        solve_f_wf_typ. dependent destruction H9...
        inst_cofinites_for f_wf_typ__all. intros. inst_cofinites_with X0.
        solve_f_wf_typ. simpl in *. rewrite trans_ftyp_open_typ_wrt_typ in *. auto.
      * solve_f_wf_typ. 
        solve_f_wf_typ. dependent destruction H9...
        inst_cofinites_for f_wf_typ__all. intros. inst_cofinites_with X0.
        solve_f_wf_typ. simpl in *. rewrite trans_ftyp_open_typ_wrt_typ in *. auto.
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__app with (A1:=ᵗ⟦ A ᵗ^^ₜ T ⟧ ); eauto.
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      solve_f_wf_typ.
      apply f_typing_weaken_cons_var...
      solve_f_wf_typ. 
      apply d_sub_elab_sound in H2.
      apply d_sub_d_wf_typ1 in H2.
      inst_cofinites_for f_wf_typ__all; intros.
      apply d_wf_typ_open_mono_inv_cons with (X:=X) in H2...
      solve_f_wf_typ. simpl in *. rewrite trans_ftyp_open_typ_wrt_typ in *...
    + rewrite trans_ftyp_open_typ_wrt_typ. econstructor; eauto...
      apply d_mono_typ_d_wf_typ in H1.
      solve_f_wf_typ... apply f_wf_typ_weaken_cons...
      econstructor; eauto. solve_f_wf_typ... 
      apply d_sub_elab_sound in H2.
      apply d_sub_d_wf_typ1 in H2.
      inst_cofinites_for f_wf_typ__all; intros.
      apply d_wf_typ_open_mono_inv_cons with (X:=X) in H2...
      solve_f_wf_typ. simpl in *. rewrite trans_ftyp_open_typ_wrt_typ in *...
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__pair; eapply f_typing__app with (A1:=ᵗ⟦ A ⟧); eauto...
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp...
      eapply f_typing_weaken_cons_var; eauto.
      solve_f_wf_typ.
    + constructor...
      solve_f_wf_typ.
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp...
      eapply f_typing_weaken_cons_var; eauto.
      solve_f_wf_typ.
    + constructor... 
      solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__app with (A1:=ᵗ⟦ A1 ⟧); eauto.
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      eapply f_typing_weaken_cons_var; eauto.
      solve_f_wf_typ.
    + eapply f_typing__proj1; eapply f_typing__var; eauto.
      solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__app with (A1:=ᵗ⟦ A2 ⟧); eauto.
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp...
      eapply f_typing_weaken_cons_var; eauto.
      solve_f_wf_typ.
    + eapply f_typing__proj2; eapply f_typing__var; eauto.
      solve_f_wf_typ.      
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__inl...
    eapply f_typing__app with (A1:=ᵗ⟦ A ⟧); eauto.
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp...
      eapply f_typing_weaken_cons_var; eauto.
      solve_f_wf_typ.
    + eapply f_typing__var...
      solve_f_wf_typ.
    + solve_f_wf_typ. apply f_wf_typ_weaken_cons...
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    eapply f_typing__inr...
    eapply f_typing__app with (A1:=ᵗ⟦ A ⟧); eauto. 
    + rewrite open_fexp_wrt_fexp_rec_lc_fexp...
      eapply f_typing_weaken_cons_var; eauto.
      solve_f_wf_typ.
    + apply f_typing__var...
      solve_f_wf_typ.
    + solve_f_wf_typ. apply f_wf_typ_weaken_cons...
  - inst_cofinites_for f_typing__abs; intros.
    simpl. unfold open_fexp_wrt_fexp. simpl...
    inst_cofinites_for f_typing__case A1:=(ᵗ⟦ A1 ⟧) , A2:=(ᵗ⟦ A2 ⟧); eauto.
    + econstructor...
      solve_f_wf_typ.
    + intros.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      unfold open_fexp_wrt_fexp. simpl.  
      eapply f_typing__app with (A1:=ᵗ⟦ A1 ⟧); eauto.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      apply f_typing_weaken_cons_var. apply f_typing_weaken_cons_var...
      solve_f_wf_typ.
      solve_f_wf_typ. apply f_wf_typ_weaken_cons...
      apply f_typing__var; eauto. 
      solve_f_wf_typ.
      apply f_wf_typ_weaken_cons...
    + intros.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      unfold open_fexp_wrt_fexp. simpl.  
      eapply f_typing__app with (A1:=ᵗ⟦ A2 ⟧); eauto...
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      apply f_typing_weaken_cons_var; eauto. apply f_typing_weaken_cons_var; eauto. 
      solve_f_wf_typ.
      solve_f_wf_typ. apply f_wf_typ_weaken_cons...
      apply f_typing__var; eauto.
      solve_f_wf_typ. apply f_wf_typ_weaken_cons...
Qed.

Theorem d_infabs_elab_sound_f : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ -> 
  ⟦ Ψ ⟧ ⊢ coᶠ : ftyp_arrow ᵗ⟦ A ⟧ (ftyp_arrow ᵗ⟦ B ⟧ ᵗ⟦ C ⟧).
Proof with eauto using d_infabs_elab_lc_fexp.
  intros. induction H...
  - inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    solve_f_wf_typ.
    replace (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0))) with (open_ftyp_wrt_ftyp (ftyp_var_b 0) (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0)))) at 2 by auto.
    eapply f_typing__tapp...
    solve_f_wf_typ. inst_cofinites_for f_wf_typ__all; intros. solve_f_wf_typ.
    apply f_typing__var... solve_f_wf_typ.
    inst_cofinites_for f_wf_typ__all; intros. solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    apply d_mono_typ_d_wf_typ in H.
    eapply f_typing__app with (A1:=ᵗ⟦ A ᵗ^^ₜ T ⟧)...
    rewrite open_fexp_wrt_fexp_rec_lc_fexp...
    eapply f_typing_weaken_cons_var; eauto. solve_f_wf_typ.
    rewrite trans_ftyp_open_typ_wrt_typ. eapply f_typing__tapp...
    solve_f_wf_typ. 
    apply f_wf_typ_weaken_cons; eauto. 
    apply f_typing__var; eauto. solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    eapply f_typing__app with (A1:=ᵗ⟦ A1 ⟧).
    rewrite open_fexp_wrt_fexp_rec_lc_fexp... 
    apply f_typing_weaken_cons_var; eauto. solve_f_wf_typ. 
    eapply f_typing__proj1; eapply f_typing__var; eauto. solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    eapply f_typing__app with (A1:=ᵗ⟦ A2 ⟧).
    rewrite open_fexp_wrt_fexp_rec_lc_fexp... 
    apply f_typing_weaken_cons_var; eauto. solve_f_wf_typ.
    eapply f_typing__proj2; eapply f_typing__var; eauto. solve_f_wf_typ.
  - inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    inst_cofinites_for f_typing__abs. intros.
    unfold open_fexp_wrt_fexp. simpl.
    inst_cofinites_for f_typing__case A1:=ᵗ⟦ A1 ⟧, A2:=ᵗ⟦ A2 ⟧; eauto.
    apply f_typing_weaken_cons_var. 
    apply f_typing__var; solve_f_wf_typ. 
    solve_f_wf_typ. apply f_wf_typ_weaken_cons; eauto. apply f_wf_typ_weaken_cons; eauto.
    + intros. unfold open_fexp_wrt_fexp. simpl. constructor.
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      apply f_typing__app with (A1:=ᵗ⟦ B1 ⟧); eauto.
      apply f_typing__app with (A1:=ᵗ⟦ A1 ⟧); eauto. 
      repeat apply f_typing_weaken_cons_var; solve_f_wf_typ; auto using f_wf_typ_weaken_cons.
      apply f_typing__var; auto. solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto. apply f_wf_typ_weaken_cons; eauto.
      simpl. auto.
      apply f_typing_weaken_cons_var... eapply f_typing__proj1. eapply f_typing__var... solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto.
      solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto.  apply f_wf_typ_weaken_cons; eauto.  auto.
      solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto.  apply f_wf_typ_weaken_cons; eauto.  auto. apply f_wf_typ_weaken_cons; eauto.  auto.
      auto.
    + intros. unfold open_fexp_wrt_fexp. simpl. constructor.
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; eauto...
      apply f_typing__app with (A1:=ᵗ⟦ B2 ⟧); eauto.
      apply f_typing__app with (A1:=ᵗ⟦ A2 ⟧); eauto. 
      repeat apply f_typing_weaken_cons_var; solve_f_wf_typ; auto using f_wf_typ_weaken_cons.
      apply f_typing__var; auto. solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto. apply f_wf_typ_weaken_cons; eauto.
      simpl. auto.
      apply f_typing_weaken_cons_var... eapply f_typing__proj2. eapply f_typing__var... solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto.
      solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto.  apply f_wf_typ_weaken_cons; eauto.  auto.
      solve_f_wf_typ; apply f_wf_typ_weaken_cons; eauto.  apply f_wf_typ_weaken_cons; eauto.  auto. apply f_wf_typ_weaken_cons; eauto.  auto.
      auto.
Qed.

Theorem d_inftapp_elab_sound_f : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  exists D, ⟦ Ψ ⟧ ⊢ co1ᶠ : ftyp_arrow ᵗ⟦ A ⟧ D /\ ⟦ Ψ ⟧ ⊢ co2ᶠ : ftyp_arrow D ᵗ⟦ C ⟧.
Proof.
Admitted.

Theorem d_chk_inf_elab_sound_f : forall Ψ e A eᶠ mode,
  d_chk_inf_elab Ψ e mode A eᶠ -> ⟦ Ψ ⟧ ⊢ eᶠ : ᵗ⟦ A ⟧.
Proof.
Admitted.

(* 

Theorem inftapp_sound_f : forall Ψ A B C co1ᶠ co2ᶠ,
  d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ -> exists D,
  typing (trans_env Ψ) co1ᶠ (ftyp_arrow (trans_ftyp A) D) /\
    typing (trans_env Ψ) co2ᶠ (ftyp_arrow D (trans_ftyp C)).
Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - exists (ftyp_all (ftyp_var_b 0)). split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
  - exists (ftyp_all (trans_ftyp B1)). split.
    + apply typing_abs with (L:=dom Ψ).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite trans_ftyp_open_typ_wrt_typ.
      apply typing_tapp.
      * apply trans_ftyp_lc_ftyp. eauto.
      * apply typing_var; auto. admit. (* wf *)
  - inversion IHinftapp_elab. destruct H2.
    exists x. split.
    + apply typing_abs with (L:=dom Ψ).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply d_inftapp_elab__lc_fexp in H1. auto. }
      destruct Hlc as [Hlc1 Hlc2].
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (B1:=trans_ftyp A1).
      * admit. (* weaken *)
      * apply typing_proj1 with (B2:=trans_ftyp A2).
        apply typing_var; auto. admit. (* wf *)
    + auto.
  - inversion IHinftapp_elab. destruct H2.
    exists x. split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply d_inftapp_elab__lc_fexp in H1. auto. }
      destruct Hlc as [Hlc1 Hlc2].
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (B1:=trans_ftyp A2).
      * admit. (* weaken *)
      * apply typing_proj2 with (B1:=trans_ftyp A1).
        apply typing_var; auto.  admit. (* wf *)
    + auto.
  - inversion IHinftapp_elab1. inversion IHinftapp_elab2.
    destruct H1. destruct H2.
    exists (trans_ftyp (typ_intersection C1 C2)). split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc12: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply d_inftapp_elab__lc_fexp in H. auto. }
      destruct Hlc12 as [Hlc1 Hlc2].
      assert (Hlc34: lc_fexp co3 /\ lc_fexp co4).
      { apply d_inftapp_elab__lc_fexp in H0. auto. }
      destruct Hlc34 as [Hlc3 Hlc4].
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_pair.
      * apply typing_app with (B1:=x).
        -- admit. (* weaken *) 
        -- apply typing_app with (B1:=trans_ftyp A1).
           ++ admit. (* weaken *)
           ++ apply typing_proj1 with (B2:=trans_ftyp A2).
              apply typing_var; auto. admit. (* wf *)
      * apply typing_app with (B1:=x0).
        -- admit. (* weaken *) 
        -- apply typing_app with (B1:=trans_ftyp A2).
           ++ admit. (* weaken *)
           ++ apply typing_proj2 with (B1:=trans_ftyp A1).
              apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
  - inversion IHinftapp_elab1. inversion IHinftapp_elab2.
    destruct H1. destruct H2.
    exists (trans_ftyp (typ_union C1 C2)). split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc12: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply d_inftapp_elab__lc_fexp in H. auto. }
      destruct Hlc12 as [Hlc1 Hlc2].
      assert (Hlc34: lc_fexp co3 /\ lc_fexp co4).
      { apply d_inftapp_elab__lc_fexp in H0. auto. }
      destruct Hlc34 as [Hlc3 Hlc4].
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_case with (L:=dom Ψ `union` singleton x1)
        (B1:=trans_ftyp A1) (B2:=trans_ftyp A2).
      * apply typing_var; auto. admit. (* wf *)
      * unfold open_fexp_wrt_fexp. simpl. intros.
        repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_inl.
        -- apply typing_app with (B1:=x).
           ++ admit. (* weaken *) 
           ++ apply typing_app with (B1:=trans_ftyp A1).
              ** admit. (* weaken *)
              ** apply typing_var; auto. admit. (* wf *)
        -- admit. (* wf *)
      * unfold open_fexp_wrt_fexp. simpl. intros.
        repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_inr.
        -- apply typing_app with (B1:=x0).
           ++ admit. (* weaken *) 
           ++ apply typing_app with (B1:=trans_ftyp A2).
              ** admit. (* weaken *)
              ** apply typing_var; auto. admit. (* wf *)
        -- admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)  
Admitted.

Theorem trans_binds : forall Ψ x T,
  binds x (dbind_typ T) Ψ -> binds x (bind_typ (trans_ftyp T)) (trans_env Ψ).
Proof.
  intros. induction Ψ; auto.
  inversion H.
  - subst. simpl. auto.
  - apply IHE in H0. destruct a.
    destruct b; simpl; auto.
Qed.

Theorem d_chk_inf_elab_lc_fexp : forall Ψ e A eᶠ mode,
  d_chk_inf_elab Ψ e mode A eᶠ -> lc_fexp eᶠ.
Proof.
  intros. induction H; eauto with safety; simpl.
Admitted.

Theorem typing_sound_f : forall Ψ e T C mode,
  d_chk_inf_elab Ψ e mode T C -> typing (trans_env Ψ) C (trans_ftyp T).
Proof.
  intros. induction H; simpl; eauto.
  - apply typing_var; auto. admit. (* wf *)
    apply trans_binds. auto.
  - apply typing_app with (B1:=trans_ftyp B2); auto.
    apply typing_app with (B1:=trans_ftyp B1); auto.
    apply infabs_sound_f; auto.
  - apply typing_tabs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X. assert (Hlc: lc_fexp C).
    { apply d_chk_inf_elab__lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    rewrite <- trans_ftyp_open_typ_wrt_typ with (B2:=typ_var_f X). auto.
  - apply inftapp_sound_f in H1. destruct H1. destruct H1.
    apply typing_app with (B1:=x); auto.
    apply typing_app with (B1:=trans_ftyp B1); auto.
  - apply typing_abs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with x. assert (Hlc: lc_fexp C).
    { apply d_chk_inf_elab__lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_lc_fexp; auto.
  - apply typing_tabs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X. assert (Hlc: lc_fexp C).
    { apply d_chk_inf_elab__lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    rewrite <- trans_ftyp_open_typ_wrt_typ with (B2:=typ_var_f X). auto.
  - eapply typing_app with (B1:=trans_ftyp A1); auto.
    apply sub_sound_f. auto.
Admitted. *)
