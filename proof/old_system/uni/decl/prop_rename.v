Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import ltac_utils.


Fixpoint rename_var_in_denv (x' x: atom) (Ψ : denv) : denv :=
  match Ψ with
  | nil => nil
  | (X, dbind_tvar_empty) :: Ψ' => (X, dbind_tvar_empty) :: rename_var_in_denv x' x Ψ' 
  | (X, dbind_stvar_empty) :: Ψ' => (X, dbind_stvar_empty) :: rename_var_in_denv x' x Ψ' 
  | (x0, dbind_typ A) :: Ψ' => (if (x0 == x) then x' else x0, dbind_typ A) :: rename_var_in_denv x' x Ψ'
  end.

Ltac destruct_binds_eq :=
  repeat
    lazymatch goal with
    | H1 : (?X1, ?b1) = (?X2, ?b2) |- _ =>
      dependent destruction H1
    end.

Ltac destruct_binds :=
  simpl in *;
  repeat
  match goal with
  | H1 : binds ?X ?b ((?X', ?b') :: ?θ) |- _ =>
    let H_1 := fresh "H" in
    let H_2 := fresh "H" in
    inversion H1 as [H_1 | H_2];
    clear H1;
    try destruct_binds_eq;
    try solve [solve_notin_eq X];
    try solve [solve_notin_eq X']
  end.


Fixpoint rename_tvar_in_denv (X' X : atom) (Ψ : denv) : denv :=
  match Ψ with
  | nil => nil
  | (X0, dbind_tvar_empty) :: Ψ' => (if X0 == X then X' else X0, dbind_tvar_empty) :: rename_tvar_in_denv X' X Ψ' 
  | (X0, dbind_stvar_empty) :: Ψ' => (if X0 == X then X' else X0, dbind_stvar_empty) :: rename_tvar_in_denv X' X Ψ' 
  | (x, dbind_typ A) :: Ψ' => (x, dbind_typ ({`X' /ᵗ X } A)) :: rename_tvar_in_denv X' X Ψ'
  end.

Lemma dtvar_binds_same_rename_var_in_denv : forall Ψ x y X b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  binds X b Ψ ->
  binds X b (rename_var_in_denv y x Ψ).
Proof.  
  intros. induction Ψ; auto.
  - simpl in H0. destruct a. destruct d; simpl in *; 
      destruct_eq_atom; subst; eauto; destruct_binds; eauto.
    + destruct H; inversion H.
Qed. 

Lemma d_wf_typ_raname_var : forall Ψ x y A,
  Ψ ⊢ A ->
  y `notin` dom Ψ ->
  (rename_var_in_denv y x Ψ) ⊢ A.
Proof with eauto using dtvar_binds_same_rename_var_in_denv.
  intros. dependent induction H...
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X; auto.
Qed.


Lemma d_wf_typ_raname_tvar : forall Ψ X Y A,
  Ψ ⊢ A ->
  Y `notin` dom Ψ ->
  (rename_tvar_in_denv Y X Ψ) ⊢ {` Y /ᵗ X} A.
Proof with eauto.
  intros. dependent induction H...
Admitted.

Lemma rename_var_in_denv_dom_upper : forall Ψ x y,
  y `notin` dom Ψ ->
  dom (rename_var_in_denv y x Ψ) [<=] add y (dom Ψ).
Proof.
  intros. induction Ψ; simpl in *; try fsetdec.
  - destruct a; destruct d; simpl in *;
    rewrite IHΨ; auto; try fsetdec.
    destruct_eq_atom; subst; fsetdec.
Qed. 

Lemma rename_tvar_in_denv_dom_upper : forall Ψ X Y,
  Y `notin` dom Ψ ->
  dom (rename_tvar_in_denv Y X Ψ) [<=] add Y (dom Ψ).
Proof.
  intros. induction Ψ; simpl in *; try fsetdec.
  - destruct a; destruct d; simpl in *;
    rewrite IHΨ; auto; try fsetdec;
    destruct_eq_atom; subst; fsetdec.
Qed. 

Lemma var_notin_rename_var_notin : forall Ψ x y,
  x `notin` dom Ψ ->
  y `notin` dom Ψ ->
  y `notin` dom (rename_var_in_denv y x Ψ).
Proof.
  intros. induction Ψ; simpl; try fsetdec.
  - destruct a; destruct d; simpl in *; try fsetdec.
    destruct_eq_atom; subst; fsetdec.  
Qed.

Lemma tvar_notin_rename_tvar_notin : forall Ψ X Y,
  X `notin` dom Ψ ->
  Y `notin` dom Ψ ->
  Y `notin` dom (rename_tvar_in_denv Y X Ψ).
Proof.
  intros. induction Ψ; simpl; try fsetdec.
  - destruct a; destruct d; simpl in *; try fsetdec.
    destruct_eq_atom; subst; fsetdec.  
Qed.


Lemma d_wf_env_rename_var : forall Ψ x y,
  ⊢ Ψ ->
  y `notin` dom Ψ ->
  ⊢ rename_var_in_denv y x Ψ.
Proof with eauto.
  intros. induction Ψ. 
  - dependent destruction H...
  - dependent destruction H; simpl in *; try solve [constructor; eauto].
    + constructor; eauto. 
      rewrite rename_var_in_denv_dom_upper...
    + constructor; eauto.
      rewrite rename_var_in_denv_dom_upper...
    + destruct_eq_atom.
      * constructor... apply d_wf_typ_raname_var...
        apply var_notin_rename_var_notin...
      * constructor; eauto.
        apply d_wf_typ_raname_var...
        rewrite rename_var_in_denv_dom_upper...
Qed.


Lemma d_wf_env_rename_tvar : forall Ψ X Y,
  ⊢ Ψ ->
  Y `notin` dom Ψ ->
  ⊢ rename_tvar_in_denv Y X Ψ.
Proof with eauto using tvar_notin_rename_tvar_notin.
  intros. induction Ψ. 
  - dependent destruction H...
  - dependent destruction H; simpl in *; try solve [constructor; eauto]; destruct_eq_atom...
    + constructor; eauto. 
      apply tvar_notin_rename_tvar_notin...
    + constructor; eauto.
      rewrite rename_tvar_in_denv_dom_upper...
    + constructor...
    + constructor...
      rewrite rename_tvar_in_denv_dom_upper...
    + constructor...
      admit.
      rewrite rename_tvar_in_denv_dom_upper...
Admitted.

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



Theorem d_sub_rename_tvar : forall Ψ A B X X',
  Ψ ⊢ A <: B ->
  X' `notin` dom Ψ ->
  (rename_tvar_in_denv X' X Ψ) ⊢ {`X' /ᵗ X } A <: {`X' /ᵗ X } B.
Proof with eauto using d_wf_typ d_wf_env_rename_tvar.
  intros. induction H; simpl; eauto...
  - constructor... admit. admit.
Qed.


Theorem d_chk_inf_rename_var : forall Ψ x y e A mode, 
  d_chk_inf Ψ e mode A ->
  y `notin` dom Ψ ->
  d_chk_inf (rename_var_in_denv y x Ψ) (subst_var_in_exp (exp_var_f y) x e) mode A.
Proof with eauto.
  intros. dependent induction H...
  - simpl. destruct_eq_atom.
    + admit.
Admitted.


Theorem d_chk_inf_rename_var_cons : forall Ψ x y e A B mode, 
  d_chk_inf ((x ,dbind_typ B) :: Ψ) e mode A ->
  y `notin` (dom Ψ) ->
  d_chk_inf ((y, dbind_typ B):: Ψ) (subst_var_in_exp (exp_var_f y) x e) mode A.
Proof.
  intros. destruct (x == y).
  - subst. rewrite subst_var_in_exp_refl; auto.
  - intros. replace ((y, dbind_typ B) :: Ψ) with (rename_var_in_denv y x ((x, dbind_typ B) :: Ψ)).
    eapply  d_chk_inf_rename_var; eauto.
    simpl; destruct_eq_atom...
    admit.
Admitted.


(* Lemma d_subtying_rename_tvar : *)
(* Lemma d_subtying_rename_var : *)
(* Lemma d_infabs_rename_tvar : *)
(* Lemma d_infabs_rename_var : *)
(* Lemma d_inftapp_rename_tvar : *)
(* Lemma d_inftapp_rename_var : *)
(* Lemma d_chk_inf_rename_tvar : *)
(* Lemma d_chk_inf_rename_var : *)
