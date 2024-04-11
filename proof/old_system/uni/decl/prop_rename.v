Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import ltac_utils.


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

Theorem d_chk_inf_rename_var' : forall Ψ1 Ψ2 x y e A B mode, 
  d_chk_inf (Ψ2 ++ (x , dbind_typ B) :: Ψ1) e mode A ->
  y `notin` (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_chk_inf (Ψ2 ++ (y, dbind_typ B) :: Ψ1) (subst_var_in_exp (exp_var_f y) x e) mode A.
Proof with eauto.
  intros. dependent induction H.
  - simpl. destruct_eq_atom.
    + assert (x ~ B ∈ᵈ (Ψ2 ++ x ~ dbind_typ B ++ Ψ1)) by auto.
      unify_binds. constructor...
      eapply d_wf_env_rename_var...
    + apply binds_remove_mid in H0...
      constructor.
      eapply d_wf_env_rename_var with (x:=x)... admit.
  - simpl. econstructor.
    (* apply d_wf_typ_rename_var. *)
  admit.
    apply IHd_chk_inf; auto.
  - simpl. apply d_chk_inf__inf_unit.
    eapply d_wf_env_rename_var...
  - simpl. eapply d_chk_inf__inf_app. 
    + eapply IHd_chk_inf1; auto.
    + admit.
    + apply IHd_chk_inf2; auto.
Admitted.


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