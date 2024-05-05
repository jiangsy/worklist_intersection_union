Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import uni.ltac_utils.


Open Scope aworklist_scope.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.
#[local] Hint Rewrite dom_app dom_cons : core.


Fixpoint rename_tvar_in_aworklist (Y X:typvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ' X' b) => 
    match b with 
    | abind_var_typ A => aworklist_cons_var (rename_tvar_in_aworklist Y X Γ') X' (subst_tvar_in_abind (`Y ) X b)
    | _ => aworklist_cons_var (rename_tvar_in_aworklist Y X Γ') (if X' == X then Y else X') b
    end
  | (aworklist_cons_work Γ' w) => aworklist_cons_work (rename_tvar_in_aworklist Y X Γ') (subst_tvar_in_work (` Y) X w)
end.

Fixpoint rename_var_in_aworklist (y x:expvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ' x' b) => 
    match b with 
    | abind_var_typ _ => aworklist_cons_var (rename_var_in_aworklist y x Γ') (if x' == x then y else x') b
    | _ => aworklist_cons_var (rename_var_in_aworklist y x Γ') x' b
    end
  | (aworklist_cons_work Γ' w) => aworklist_cons_work (rename_var_in_aworklist y x Γ') (subst_var_in_work (exp_var_f y) x w)
  end.

Notation "{ Y ᵃʷ/ₜᵥ X } Γ" :=
  (rename_tvar_in_aworklist Y X Γ)
    ( at level 49, Y at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "{ y ᵃʷ/ₑᵥ x } Γ" :=
  (rename_var_in_aworklist y x Γ)
    ( at level 49, y at level 50, x at level 0
    , right associativity) : type_scope. 


Lemma rename_tvar_in_aworklist_tvar_bind_same : forall Γ X1 X2 Y b,
  ⊢ᵃʷ Γ ->
  Y ∉ ftvar_in_aworklist' Γ ->
  binds X1 b (⌊ Γ ⌋ᵃ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds (if X1 == X2 then Y else X1) b (⌊ {Y ᵃʷ/ₜᵥ X2} Γ ⌋ᵃ).
Proof.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H. destruct_eq_atom.
    + destruct_binds; destruct_eq_atom; auto. solve_false.
    + destruct_binds; destruct_eq_atom; auto. solve_false.
    + destruct_binds; destruct_eq_atom; auto.
    + destruct_binds; destruct_eq_atom; auto.
    + destruct_binds; destruct_eq_atom; auto.
  - destruct_eq_atom; dependent destruction H; auto.
Qed.

Corollary rename_tvar_in_aworklist_neq_tvar_bind_same : forall Γ X1 X2 Y b,
  ⊢ᵃʷ Γ ->
  X1 <> X2 ->
  Y ∉ ftvar_in_aworklist' Γ ->
  binds X1 b  (⌊ Γ ⌋ᵃ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds X1 b (⌊ rename_tvar_in_aworklist Y X2 Γ ⌋ᵃ).
Proof.
  intros. eapply rename_tvar_in_aworklist_tvar_bind_same with (X2:=X2) in H1; eauto.
  destruct_eq_atom; auto.
Qed.

Corollary rename_tvar_in_aworklist_eq_tvar_bind_same : forall Γ X X' b,
  ⊢ᵃʷ Γ ->
  X' ∉ ftvar_in_aworklist' Γ ->
  binds X b (⌊ Γ ⌋ᵃ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds X' b (⌊ {X' ᵃʷ/ₜᵥ X} Γ ⌋ᵃ).
Proof.
  intros. eapply rename_tvar_in_aworklist_tvar_bind_same with (X2:=X) in H1; eauto...
  destruct_eq_atom; auto.
Qed.

Lemma rename_tvar_in_aworklist_app : forall Γ1 Γ2 X Y,
  {Y ᵃʷ/ₜᵥ X} Γ2 ⧺ {Y ᵃʷ/ₜᵥ X} Γ1 = {Y ᵃʷ/ₜᵥ X} (Γ2 ⧺ Γ1).
Proof.
  intros. induction Γ2; simpl in *; auto.
  - destruct ab; simpl in *; destruct_eq_atom; rewrite IHΓ2; auto.
  - rewrite IHΓ2; auto.
Qed.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

Lemma ftvar_in_aworklist'_awl_app : forall Γ1 Γ2,
  ftvar_in_aworklist' (Γ2 ⧺ Γ1) [=] ftvar_in_aworklist' Γ2 `union` ftvar_in_aworklist' Γ1.
Proof.
  induction Γ2; simpl; try fsetdec.
    destruct ab; auto; fsetdec.
Qed.

Ltac rewrite_ftvar_in_aworklist' :=
  match goal with
  | H : context [ftvar_in_aworklist' (awl_app _ _)] |- _ =>
    rewrite ftvar_in_aworklist'_awl_app in H; simpl in H; repeat (case_if in H; [ ])
  | |- context [ftvar_in_aworklist' (awl_app _ _)] =>
    rewrite ftvar_in_aworklist'_awl_app; simpl; repeat (case_if; [ ])
  end; auto.

Ltac rewrite_ftvar_in_aworklist := repeat rewrite_ftvar_in_aworklist'.

#[local] Hint Rewrite dom_app dom_cons : core.

Lemma ftvar_in_a_wf_typ_upper : forall Γ A,
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ftvar_in_typ A [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros; dependent induction H; try solve [simpl; fsetdec].
  - simpl. apply binds_In in H. fsetdec.
  - simpl. apply binds_In in H. fsetdec.
  - simpl. apply binds_In in H. fsetdec.
  - simpl. rewrite IHa_wf_typ1; auto.
    rewrite IHa_wf_typ2; auto.
    fsetdec.
  - simpl. simpl.
    inst_cofinites_by (L `union` dom (⌊ Γ ⌋ᵃ) `union` ftvar_in_typ A) using_name X.
    assert (X ~ abind_tvar_empty ++ awl_to_aenv Γ = awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) by (simpl; auto).
    specialize (H1 (aworklist_cons_var Γ X abind_tvar_empty) H2); auto.
    simpl in H1.
    assert ((ftvar_in_typ A) [<=] (ftvar_in_typ (A ᵗ^ₜ X))) by apply ftvar_in_typ_open_typ_wrt_typ_lower.
    fsetdec.
  - simpl. rewrite IHa_wf_typ1; auto.
    rewrite IHa_wf_typ2; auto.
    fsetdec.
  - simpl. rewrite IHa_wf_typ1; auto.
    rewrite IHa_wf_typ2; auto.
    fsetdec.
Qed.


Lemma ftvar_in_wf_exp_upper : forall Γ e,
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  ftvar_in_exp e [<=] dom (⌊ Γ ⌋ᵃ)
with ftvar_in_wf_body_upper : forall Γ b,
  ⌊ Γ ⌋ᵃ ᵇ⊢ᵃ b ->
  ftvar_in_body b [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  - intros. dependent induction H; try solve [simpl; fsetdec].
    + inst_cofinites_by (L `union` dom (⌊ Γ ⌋ᵃ) `union` ftvar_in_exp e).
      assert (ftvar_in_exp e [<=] ftvar_in_exp (e ᵉ^ₑ exp_var_f x)) by apply ftvar_in_exp_open_exp_wrt_exp_lower.
      assert (x ~ abind_var_typ T ++ awl_to_aenv Γ = awl_to_aenv (x ~ᵃ T ;ᵃ Γ)) by (simpl; auto).
      eapply H1 in H3.
      simpl in *.
      fsetdec.
    + simpl.
      rewrite IHa_wf_exp1; eauto.
      rewrite IHa_wf_exp2; eauto.
      fsetdec.
    + inst_cofinites_by (L `union` dom (⌊ Γ ⌋ᵃ) `union` ftvar_in_body body5) using_name X.
      replace (X ~ abind_tvar_empty ++ awl_to_aenv Γ) with (awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) in H0 by auto.
      assert (ftvar_in_body body5 [<=] ftvar_in_body (open_body_wrt_typ body5 ` X)) by apply
        ftvar_in_body_open_body_wrt_typ_lower.
      apply ftvar_in_wf_body_upper in H0.
      simpl in *.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto.
      rewrite ftvar_in_a_wf_typ_upper; eauto.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto.
      rewrite ftvar_in_a_wf_typ_upper; eauto.
      fsetdec.
  - intros. destruct b; simpl.
    + dependent destruction H.
      rewrite ftvar_in_wf_exp_upper; eauto.
      rewrite ftvar_in_a_wf_typ_upper; eauto.
      fsetdec.
Qed.


Lemma ftvar_in_wf_conts_upper : forall Γ cs,
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ cs ->
  ftvar_in_conts cs [<=] dom (⌊ Γ ⌋ᵃ)
with ftvar_in_wf_contd_upper : forall Γ cd,
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cd ->
  ftvar_in_contd cd [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  - intros. intros; dependent induction H;
    simpl in *;
    try repeat erewrite ftvar_in_a_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite IHa_wf_conts; eauto; 
    try rewrite ftvar_in_wf_contd_upper; eauto;
    try fsetdec.
  - intros. intros; dependent induction H;
    simpl in *;
    try solve [
    try destruct_wf_arrow;
    try repeat erewrite ftvar_in_a_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite ftvar_in_wf_conts_upper; eauto;
    try rewrite IHa_wf_contd; eauto; 
    try fsetdec].
Qed.

Lemma ftvar_in_wf_work_upper : forall Γ w,
  ⌊ Γ ⌋ᵃ ʷ⊢ᵃ w ->
  ftvar_in_work w [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros. intros; dependent destruction H;
    simpl in *;
    try solve [
    try repeat destruct_wf_arrow;
    try repeat erewrite ftvar_in_a_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite ftvar_in_wf_conts_upper; eauto; 
    try rewrite ftvar_in_wf_contd_upper; eauto; try fsetdec].
Qed.

Lemma ftvar_in_a_wf_wwl_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  ftvar_in_aworklist' Γ [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros; induction H; auto; try solve [simpl; fsetdec].
  - simpl. rewrite ftvar_in_a_wf_typ_upper; eauto. fsetdec.
  - simpl. rewrite ftvar_in_wf_work_upper; eauto. fsetdec.
Qed.
