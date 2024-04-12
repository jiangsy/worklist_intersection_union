Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import ltac_utils.

Lemma d_wf_typ_rename_var : forall Ψ1 Ψ2 x y A B,
  (Ψ2 ++ (x , dbind_typ B) :: Ψ1) ⊢ A ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ B) :: Ψ1) ->
  (Ψ2 ++ (y , dbind_typ B) :: Ψ1) ⊢ A.
Proof with auto.
  intros. dependent induction H; eauto.
  - econstructor; eauto.
    apply binds_remove_mid_diff_bind in H...
    apply binds_weaken_mid...
    solve_false.
  - eapply d_wf_typ__stvar...
    apply binds_remove_mid_diff_bind in H...
    apply binds_weaken_mid...
    solve_false.
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X; auto.
    rewrite_env ((X ~ □ ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1).
    eapply H1; simpl; eauto.
Qed.

Lemma d_mono_typ_rename_var : forall Ψ1 Ψ2 x y T A,
  (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ⊢ₘ T ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ->
  (Ψ2 ++ (y , dbind_typ A) :: Ψ1) ⊢ₘ T.
Proof with auto.
  intros. dependent induction H; eauto.
  - econstructor; eauto.
    apply binds_remove_mid_diff_bind in H...
    apply binds_weaken_mid...
    solve_false.
Qed.

Lemma d_wf_env_rename_var : forall Ψ1 Ψ2 x y A,
  ⊢ Ψ2 ++ (x , dbind_typ A) :: Ψ1 ->
  y `notin` dom (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ->
  ⊢ Ψ2  ++ (y , dbind_typ A) :: Ψ1.
Proof with eauto.
  intros. induction Ψ2. 
  - dependent destruction H... constructor...
  - dependent destruction H; try solve [constructor; eauto].
    + simpl. constructor...
      eapply d_wf_typ_rename_var with (x:=x); eauto.
Qed.


Lemma subst_var_in_exp_refl : forall x e,
  subst_var_in_exp (exp_var_f x) x e = e
with subst_var_in_body_refl : forall x b,
  subst_var_in_body (exp_var_f x) x b = b.
Proof.
  - intros. dependent induction e; simpl; auto.
    + destruct_eq_atom; eauto.
    + rewrite IHe; auto.
    + rewrite IHe1. rewrite IHe2. auto.
    + rewrite subst_var_in_body_refl. auto.
    + rewrite IHe. auto.
    + rewrite IHe. auto.
  - destruct b. simpl. rewrite subst_var_in_exp_refl.
    auto.
Qed.


Theorem d_sub_rename_var : forall Ψ1 Ψ2 x y A B C, 
  d_sub (Ψ2 ++ (x , dbind_typ C) :: Ψ1) A B->
  y `notin` (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_sub (Ψ2 ++ (y, dbind_typ C) :: Ψ1) A B.
Proof with eauto using d_wf_typ_rename_var, d_wf_env_rename_var, d_mono_typ_rename_var.
  intros. dependent induction H; eauto...
  - inst_cofinites_for d_sub__all...
    intros. inst_cofinites_with X.
    rewrite_env ((X ~ ■ ++ Ψ2) ++ (y, dbind_typ C) :: Ψ1)...
    eapply H2... eauto.
Qed.

Theorem d_infabs_rename_var : forall Ψ1 Ψ2 x y A B C D, 
  d_infabs (Ψ2 ++ (x , dbind_typ D) :: Ψ1) A B C ->
  y `notin` (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_infabs (Ψ2 ++ (y, dbind_typ D) :: Ψ1) A B C.
Proof with eauto 4 using d_wf_typ_rename_var, d_wf_env_rename_var, d_mono_typ_rename_var.
  intros. dependent induction H...
  - constructor...
  - eapply d_infabs__all with (T:=T)...
Qed.

Theorem d_inftapp_rename_var : forall Ψ1 Ψ2 x y A B C D, 
  d_inftapp (Ψ2 ++ (x , dbind_typ D) :: Ψ1) A B C ->
  y `notin` (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_inftapp (Ψ2 ++ (y, dbind_typ D) :: Ψ1) A B C.
Proof with eauto using d_wf_typ_rename_var, d_wf_env_rename_var, d_mono_typ_rename_var.
  intros. dependent induction H...
Qed.

Theorem d_chk_inf_rename_var' : forall Ψ1 Ψ2 x y e A B mode, 
  d_chk_inf (Ψ2 ++ (x , dbind_typ B) :: Ψ1) e mode A ->
  y `notin` (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_chk_inf (Ψ2 ++ (y, dbind_typ B) :: Ψ1) (subst_var_in_exp (exp_var_f y) x e) mode A.
Proof with eauto using d_wf_typ_rename_var, d_wf_env_rename_var, d_sub_rename_var, d_infabs_rename_var, d_inftapp_rename_var.
  intros. dependent induction H; simpl...
  - simpl. destruct_eq_atom.
    + assert (x ~ B ∈ᵈ (Ψ2 ++ x ~ dbind_typ B ++ Ψ1)) by auto.
      unify_binds...
    + apply binds_remove_mid in H0...
      constructor...
      apply binds_weaken_mid...
  - inst_cofinites_for d_chk_inf__inf_abs_mono...
    eapply d_mono_typ_rename_var...
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} exp_var_f x0) by (apply subst_var_in_exp_fresh_eq; eauto).
    rewrite <- subst_var_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ dbind_typ A ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__inf_tabs...
    intros. inst_cofinites_with X.
    rewrite <- subst_var_in_exp_open_exp_wrt_typ...
    rewrite_env ((X ~ □ ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__chk_abstop...
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} exp_var_f x0) by (apply subst_var_in_exp_fresh_eq; eauto).
    rewrite <- subst_var_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ dbind_typ typ_bot ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__chk_abs...
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} exp_var_f x0) by (apply subst_var_in_exp_fresh_eq; eauto).
    rewrite <- subst_var_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ dbind_typ A1 ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
Qed.


Theorem d_chk_inf_rename_var : forall Ψ1 Ψ2 x y e A B mode, 
  d_chk_inf (Ψ2 ++ (x ,dbind_typ B) :: Ψ1) e mode A ->
  y `notin` (dom (Ψ2 ++ Ψ1)) ->
  d_chk_inf (Ψ2 ++ (y, dbind_typ B):: Ψ1) (subst_var_in_exp (exp_var_f y) x e) mode A.
Proof with eauto.
  intros. destruct (x == y); subst.
  - rewrite subst_var_in_exp_refl...
  - assert (y `notin` (dom (Ψ2 ++ x ~ (dbind_typ B) ++ Ψ1))) by auto.
    eapply d_chk_inf_rename_var'...
Qed.

Theorem d_chk_inf_rename_var_cons : forall Ψ x y e A B mode, 
  d_chk_inf ((x ,dbind_typ B) :: Ψ) e mode A ->
  y `notin` (dom Ψ) ->
  d_chk_inf ((y, dbind_typ B):: Ψ) (subst_var_in_exp (exp_var_f y) x e) mode A.
Proof.
  intros. rewrite_env (nil ++ y ~ (dbind_typ B) ++ Ψ).
  eapply  d_chk_inf_rename_var; eauto.
Qed.


Theorem d_sub_rename_dtvar_cons : forall Ψ X Y b A B, 
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  (X, b) :: Ψ ⊢ A <: B ->
  Y `notin` dom Ψ ->
  (Y, b):: Ψ ⊢ {` Y /ᵗ X} A <: {` Y /ᵗ X} B.
Proof.
Admitted.


Theorem d_chk_inf_rename_dtvar_cons : forall Ψ X Y b e A mode, 
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  d_chk_inf ((X, b) :: Ψ) e mode A ->
  Y `notin` (dom Ψ) ->
  d_chk_inf ((Y, b):: Ψ) (subst_tvar_in_exp `Y X e) mode (subst_tvar_in_typ `Y X A).
Proof.
Admitted.