Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import ln_utils.
Require Import LibTactics.


Open Scope aworklist_scope.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.
#[local] Hint Rewrite dom_app dom_cons : core.

Lemma awl_app_rename_tvar_comm : forall Γ1 Γ2 X X',
  awl_app (rename_tvar_in_aworklist X' X Γ2) (rename_tvar_in_aworklist X' X Γ1) =
  rename_tvar_in_aworklist X' X (awl_app Γ2 Γ1).
Proof.
  intros. induction Γ2; simpl in *; auto; rewrite IHΓ2; auto.
Qed.

Lemma awl_cons_rename_tvar_comm : forall a b t Γ X,
  aworklist_constvar (rename_tvar_in_aworklist a b Γ)
      (if X == b then a else X)
      (subst_tvar_in_abind ` a b t) =
  rename_tvar_in_aworklist a b (aworklist_constvar Γ X t).
Proof.
  induction Γ; simpl; fsetdec.
Qed.

Lemma ftvar_in_aworklist'_awl_cons : forall a b Γ,
  ftvar_in_aworklist' (aworklist_constvar Γ a b) [=]
    union (ftvar_in_aworklist' Γ) (union (ftvar_in_abind b) (singleton a)).
Proof.
  intros. simpl; fsetdec.
Qed.

Lemma ftvar_in_aworklist'_awl_app : forall Γ1 Γ2,
  ftvar_in_aworklist' (awl_app Γ2 Γ1) [=] ftvar_in_aworklist' Γ2 `union` ftvar_in_aworklist' Γ1.
Proof.
  induction Γ2; simpl; fsetdec.
Qed.



#[local] Hint Rewrite dom_app dom_cons : core.


Lemma ftvar_in_wf_typ_upper : forall Γ A,
  a_wf_typ (awl_to_aenv Γ) A ->
  ftvar_in_typ A [<=] dom (awl_to_aenv Γ).
Proof.
  intros; dependent induction H; try solve [simpl; fsetdec].
  - simpl. apply binds_In in H. fsetdec.
  - simpl. apply binds_In in H. fsetdec.
  - simpl. apply binds_In in H. fsetdec.
  - simpl. rewrite IHa_wf_typ1; auto.
    rewrite IHa_wf_typ2; auto.
    fsetdec.
  - simpl. simpl.
    inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_typ A) using_name X.
    assert (X ~ abind_tvar_empty ++ awl_to_aenv Γ = awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) by (simpl; auto).
    specialize (H1 (aworklist_constvar Γ X abind_tvar_empty) H2); auto.
    simpl in H1.
    assert ((ftvar_in_typ A) [<=] (ftvar_in_typ (A ^ᵗ X))) by apply ftvar_in_typ_open_typ_wrt_typ_lower.
    fsetdec.
  - simpl. rewrite IHa_wf_typ1; auto.
    rewrite IHa_wf_typ2; auto.
    fsetdec.
  - simpl. rewrite IHa_wf_typ1; auto.
    rewrite IHa_wf_typ2; auto.
    fsetdec.
Qed.


Lemma ftvar_in_wf_exp_upper : forall Γ e,
  a_wf_exp (awl_to_aenv Γ) e ->
  ftvar_in_exp e [<=] dom (awl_to_aenv Γ)
with ftvar_in_wf_body_upper : forall Γ b,
  a_wf_body (awl_to_aenv Γ) b ->
  ftvar_in_body b [<=] dom (awl_to_aenv Γ).
Proof.
  - intros. dependent induction H; try solve [simpl; fsetdec].
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_exp e).
      assert (ftvar_in_exp e [<=] ftvar_in_exp (e ^ᵉₑ exp_var_f x)) by apply ftvar_in_exp_open_exp_wrt_exp_lower.
      assert (x ~ abind_var_typ T ++ awl_to_aenv Γ = awl_to_aenv (x ~ᵃ T ;ᵃ Γ)) by (simpl; auto).
      eapply H1 in H3.
      simpl in *.
      fsetdec.
    + simpl.
      rewrite IHa_wf_exp1; eauto.
      rewrite IHa_wf_exp2; eauto.
      fsetdec.
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_body body5) using_name X.
      replace (X ~ abind_tvar_empty ++ awl_to_aenv Γ) with (awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) in H0 by auto.
      assert (ftvar_in_body body5 [<=] ftvar_in_body (open_body_wrt_typ body5 ` X)) by apply
        ftvar_in_body_open_body_wrt_typ_lower.
      apply ftvar_in_wf_body_upper in H0.
      simpl in *.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto.
      rewrite ftvar_in_wf_typ_upper; eauto.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto.
      rewrite ftvar_in_wf_typ_upper; eauto.
      fsetdec.
  - intros. destruct b; simpl.
    + dependent destruction H.
      rewrite ftvar_in_wf_exp_upper; eauto.
      rewrite ftvar_in_wf_typ_upper; eauto.
      fsetdec.
Qed.


Lemma ftvar_in_wf_conts_upper : forall Γ cs,
  a_wf_conts (awl_to_aenv Γ) cs ->
  ftvar_in_conts cs [<=] dom (awl_to_aenv Γ)
with ftvar_in_wf_contd_upper : forall Γ cd,
  a_wf_contd (awl_to_aenv Γ) cd ->
  ftvar_in_contd cd [<=] dom (awl_to_aenv Γ).
Proof.
  - intros. intros; dependent induction H;
    simpl in *;
    try repeat erewrite ftvar_in_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite IHa_wf_conts; eauto; 
    try rewrite ftvar_in_wf_contd_upper; eauto;
    try fsetdec.
  - intros. intros; dependent induction H;
    simpl in *;
    try solve [
    try destruct_wf_arrow;
    try repeat erewrite ftvar_in_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite ftvar_in_wf_conts_upper; eauto;
    try rewrite IHa_wf_contd; eauto; 
    try fsetdec].
Qed.

Lemma ftvar_in_wf_work_upper : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w ->
  ftvar_in_work w [<=] dom (awl_to_aenv Γ).
Proof.
  intros. intros; dependent destruction H;
    simpl in *;
    try solve [
    try repeat destruct_wf_arrow;
    try repeat erewrite ftvar_in_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite ftvar_in_wf_conts_upper; eauto; 
    try rewrite ftvar_in_wf_contd_upper; eauto; try fsetdec].
Qed.

Lemma ftvar_in_aworklist_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  ftvar_in_aworklist' Γ [<=] dom (awl_to_aenv Γ).
Proof.
  intros; induction H; auto; try solve [simpl; fsetdec].
  - simpl. rewrite ftvar_in_wf_typ_upper; eauto. fsetdec.
  - simpl. rewrite ftvar_in_wf_work_upper; eauto. fsetdec.
Qed.

(* -- *)

Lemma dom_aworklist_subst : forall Γ X A Γ1 Γ2,
    aworklist_subst Γ X A Γ1 Γ2 -> dom (awl_to_aenv Γ) [=] dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv (subst_tvar_in_aworklist A X Γ2)) `union` (singleton X).
Proof with simpl in *; fsetdec.
  introv HS. induction HS.
  1: auto...
  -  simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
     repeat rewrite KeySetProperties.add_union_singleton.
     fsetdec.
  -  simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
     repeat rewrite KeySetProperties.add_union_singleton.
     clear H H0.
     fsetdec.
  -  simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
     repeat rewrite KeySetProperties.add_union_singleton.
     clear H H0.
     fsetdec.
  -  simpl. rewrite IHHS. fsetdec.
  -  simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
     repeat rewrite KeySetProperties.add_union_singleton.
     clear H H0.
     fsetdec.
  -  simpl. rewrite awl_to_aenv_app, awl_to_aenv_cons in *.
     autorewrite with core in *. rewrite <- IHHS.
     rewrite AtomSetProperties.add_union_singleton.
     clear IHHS H0 H.
     fsetdec.
Qed.


#[local] Hint Rewrite ftvar_in_aworklist'_awl_cons ftvar_in_aworklist'_awl_app : core.

Lemma rename_tvar_in_typ_rev_eq : forall X X' A,
  X' `notin` ftvar_in_typ A ->
  subst_tvar_in_typ (typ_var_f X) X' (subst_tvar_in_typ (typ_var_f X') X A) = A.
Proof.
  intros. induction A; simpl in *; auto;
    try rewrite IHA; try rewrite IHA1; try rewrite IHA2; auto.
  - destruct (X0 == X).
    + simpl. unfold eq_dec.
      destruct (EqDec_eq_of_X X' X'); auto.
      * subst; auto.
      * subst. solve_notin_eq X'.
    + simpl. unfold eq_dec.
      destruct (EqDec_eq_of_X X0 X'); auto.
      * subst. solve_notin_eq X'.
Qed.

Lemma rename_tvar_in_exp_rev_eq : forall X X' e,
  X' `notin` ftvar_in_exp e ->
  subst_tvar_in_exp (typ_var_f X) X' (subst_tvar_in_exp (typ_var_f X') X e) = e
with rename_tvar_in_body_rev_eq : forall X X' b,
  X' `notin` ftvar_in_body b ->
  subst_tvar_in_body (typ_var_f X) X' (subst_tvar_in_body (typ_var_f X') X b) = b.
Proof.
  - intros. induction e; simpl in *; auto;
    try rewrite IHe; try rewrite IHe1; try rewrite IHe2; auto.
    + rewrite rename_tvar_in_body_rev_eq; auto.
    + rewrite rename_tvar_in_typ_rev_eq; auto.
    + rewrite rename_tvar_in_typ_rev_eq; auto.
  - intros. destruct b; simpl in *; auto.
    + rewrite rename_tvar_in_typ_rev_eq; auto.
      rewrite rename_tvar_in_exp_rev_eq; auto.
Qed.

Lemma rename_tvar_in_conts_rev_eq : forall X X' cs,
  X' `notin` ftvar_in_conts cs ->
  subst_tvar_in_conts (typ_var_f X) X' (subst_tvar_in_conts (typ_var_f X') X cs) = cs
with rename_tvar_in_contd_rev_eq : forall X X' cd,
  X' `notin` ftvar_in_contd cd ->
  subst_tvar_in_contd (typ_var_f X) X' (subst_tvar_in_contd (typ_var_f X') X cd) = cd.
Proof.
  - induction cs; simpl in *; intros;
      try repeat rewrite rename_tvar_in_typ_rev_eq; auto;
      try rewrite rename_tvar_in_exp_rev_eq; auto;
      try rewrite IHcs; auto;
      try rewrite rename_tvar_in_contd_rev_eq; auto.
  - induction cd; simpl in *; intros;
      try repeat rewrite rename_tvar_in_typ_rev_eq; auto;
      try rewrite rename_tvar_in_exp_rev_eq; auto;
      try rewrite IHcd; auto;
      try rewrite rename_tvar_in_conts_rev_eq; auto.
Qed.

Lemma rename_tvar_in_work_rev_eq : forall X X' w,
  X' `notin` ftvar_in_work w ->
  subst_tvar_in_work (typ_var_f X) X' (subst_tvar_in_work (typ_var_f X') X w) = w.
Proof.
  destruct w; intros; simpl in *;
    try repeat rewrite rename_tvar_in_typ_rev_eq; auto;
    try rewrite rename_tvar_in_exp_rev_eq; auto;
    try rewrite rename_tvar_in_conts_rev_eq; auto;
    try rewrite rename_tvar_in_contd_rev_eq; auto.
Qed.

Lemma rename_tvar_in_abind_rev_eq : forall X X' b,
  X' `notin` ftvar_in_abind b ->
  subst_tvar_in_abind (typ_var_f X) X' (subst_tvar_in_abind (typ_var_f X') X b) = b.
Proof.
  intros. destruct b; auto.
  - simpl. rewrite rename_tvar_in_typ_rev_eq; auto.
Qed.

Lemma rename_tvar_in_aworklist_rev_eq : forall X X' Γ,
  X' `notin` ftvar_in_aworklist' Γ ->
  rename_tvar_in_aworklist X X' (rename_tvar_in_aworklist X' X Γ) = Γ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - simpl. rewrite IHΓ; auto. rewrite rename_tvar_in_abind_rev_eq; auto.
  - unfold eq_dec.
    destruct (EqDec_eq_of_X X0 X); destruct (EqDec_eq_of_X X' X');
    destruct (EqDec_eq_of_X X0 X'); subst; try contradiction.
    + rewrite IHΓ; auto. rewrite rename_tvar_in_abind_rev_eq; auto.
    + rewrite IHΓ; auto. rewrite rename_tvar_in_abind_rev_eq; auto.
    + solve_notin_eq X'.
    + rewrite IHΓ; auto. rewrite rename_tvar_in_abind_rev_eq; auto.
  - rewrite IHΓ; auto. rewrite rename_tvar_in_work_rev_eq; auto.
Qed.

Lemma subst_tvar_in_typ_rename_tvar : forall X X' A B,
  X' `notin` ftvar_in_typ A ->
  {` X' /ᵗ X} {B /ᵗ X} A = {({` X' /ᵗ X} B) /ᵗ X'} {` X' /ᵗ X} A.
Proof.
  intros. induction A; simpl; auto.
  - destruct (X0 == X); auto.
    + simpl. unfold eq_dec. destruct (EqDec_eq_of_X X' X'); auto.
      contradiction.
    + simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
      * subst. contradiction.
      * destruct (EqDec_eq_of_X X0 X').
        subst. solve_notin_eq X'.
        auto.
  - simpl in *.
    rewrite IHA1; auto.
    rewrite IHA2; auto.
  - simpl in *.
    rewrite IHA; auto.
  - simpl in *.
    rewrite IHA1; auto.
    rewrite IHA2; auto.
  - simpl in *.
    rewrite IHA1; auto.
    rewrite IHA2; auto.
Qed.


Lemma subst_tvar_in_exp_rename_tvar : forall X X' e A,
  X' `notin` ftvar_in_exp e ->
  (subst_tvar_in_exp ` X' X (subst_tvar_in_exp A X e)) =
  (subst_tvar_in_exp ({` X' /ᵗ X} A) X' (subst_tvar_in_exp ` X' X e))
with subst_tvar_in_body_rename_tvar : forall X X' b A,
  X' `notin` ftvar_in_body b ->
  (subst_tvar_in_body ` X' X (subst_tvar_in_body A X b)) =
  (subst_tvar_in_body ({` X' /ᵗ X} A) X' (subst_tvar_in_body ` X' X b)).
Proof.
  - intros. induction e; simpl in *; auto.
    + rewrite IHe; auto.
    + rewrite IHe1; auto.
      rewrite IHe2; auto.
    + erewrite subst_tvar_in_body_rename_tvar; auto.
    + rewrite IHe; auto.
      rewrite subst_tvar_in_typ_rename_tvar; auto.
    + rewrite IHe; auto.
      rewrite subst_tvar_in_typ_rename_tvar; auto.
  - intros. induction b.
    simpl in *.
    erewrite subst_tvar_in_exp_rename_tvar; auto.
    rewrite subst_tvar_in_typ_rename_tvar; auto.
Qed.


Lemma subst_tvar_in_conts_rename : forall X X' A cs,
  X' `notin` ftvar_in_conts cs ->
  {` X' /ᶜˢₜ X} {A /ᶜˢₜ X} cs = {({` X' /ᵗ X} A) /ᶜˢₜ X'} {` X' /ᶜˢₜ X} cs
with subst_tvar_in_contd_rename : forall X X' A cd,
  X' `notin` ftvar_in_contd cd ->
  {` X' /ᶜᵈₜ X} {A /ᶜᵈₜ X} cd = {({` X' /ᵗ X} A) /ᶜᵈₜ X'} {` X' /ᶜᵈₜ X} cd.
Proof.
  - intros. induction cs; simpl in *;
    try repeat rewrite subst_tvar_in_typ_rename_tvar; auto;
    try rewrite subst_tvar_in_exp_rename_tvar; auto;
    try rewrite IHcs; auto;
    try rewrite subst_tvar_in_contd_rename; auto.
  - intros. induction cd; simpl in *;
    try repeat rewrite subst_tvar_in_typ_rename_tvar; auto;
    try rewrite subst_tvar_in_exp_rename_tvar; auto;
    try rewrite IHcd; auto;
    try rewrite subst_tvar_in_conts_rename; auto.
Qed.


Lemma subst_tvar_in_work_rename : forall X X' w A,
  X' `notin` ftvar_in_work w ->
  {` X' /ʷₜ X} {A /ʷₜ X} w = {({` X' /ᵗ X} A) /ʷₜ X'} {` X' /ʷₜ X} w.
Proof.
  intros. destruct w; simpl in *;
    try repeat rewrite subst_tvar_in_typ_rename_tvar; auto;
    try rewrite subst_tvar_in_exp_rename_tvar; auto;
    try rewrite subst_tvar_in_conts_rename; auto;
    try rewrite subst_tvar_in_contd_rename; auto.
Qed.


Lemma subst_tvar_in_awl_rename_tvar_comm_eq : forall Γ X X' A,
  X' `notin` ftvar_in_aworklist' Γ ->
  (rename_tvar_in_aworklist X' X (subst_tvar_in_aworklist A X Γ)) =
  (subst_tvar_in_aworklist ({` X' /ᵗ X} A) X' (rename_tvar_in_aworklist X' X Γ)).
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal. destruct ab; auto.
    + simpl. rewrite subst_tvar_in_typ_rename_tvar; auto.
  - apply f_equal.
    + destruct ab; auto.
      * simpl. rewrite subst_tvar_in_typ_rename_tvar; auto.
  - apply f_equal.
    + rewrite subst_tvar_in_work_rename; auto.
Qed.

Lemma subst_tvar_in_awl_rename_tvar_comm_neq : forall Γ X1 X2 X' A,
  X' <> X2 ->
  X1 <> X2 ->
  (rename_tvar_in_aworklist X' X1 (subst_tvar_in_aworklist A X2 Γ)) =
  (subst_tvar_in_aworklist ({` X' /ᵗ X1} A) X2 (rename_tvar_in_aworklist X' X1 Γ)).
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal. rewrite subst_tvar_in_abind_subst_tvar_in_abind; auto.
  - apply f_equal. rewrite subst_tvar_in_abind_subst_tvar_in_abind; auto.
  - apply f_equal. rewrite subst_tvar_in_work_subst_tvar_in_work; auto.
Qed.

Lemma a_worklist_subst_ftavr_in_aworklist : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist'
    (awl_app (subst_tvar_in_aworklist A X Γ2) Γ1) [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - rewrite ftvar_in_typ_subst_tvar_in_typ_upper; fsetdec.
  - rewrite ftvar_in_work_subst_tvar_in_work_upper; fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.

Lemma a_worklist_subst_ftavr_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ1 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.


Lemma a_worklist_subst_ftavr_in_aworklist_2 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ2 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.


Ltac rewrite_aworklist_rename_tvar' :=
  repeat
  match goal with
  | H : context [rename_tvar_in_aworklist _ _ (awl_app _ _)] |- _ =>
    progress (repeat rewrite <- awl_app_rename_tvar_comm in H); simpl in H; repeat (case_if in H; [ ])
  | H : context [rename_tvar_in_aworklist _ _ _] |- _ =>
    progress (repeat rewrite <- awl_cons_rename_tvar_comm in H); simpl in H; repeat (case_if in H; [ ])
  | |- context [rename_tvar_in_aworklist _ _ (awl_app _ _)] =>
    repeat rewrite <- awl_app_rename_tvar_comm; simpl; repeat (case_if; [ ])
  | |- context [rename_tvar_in_aworklist _ _ _] =>
    progress rewrite <- awl_cons_rename_tvar_comm; simpl; repeat (case_if; [ ])
  end; auto.

Ltac rewrite_aworklist_rename_subst :=
  match goal with
  | H : context [rename_tvar_in_aworklist _ ?X (subst_tvar_in_aworklist ?A ?X _)] |- _ =>
    rewrite subst_tvar_in_awl_rename_tvar_comm_eq in H; try solve
      [rewrite a_worklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
  | H : context [rename_tvar_in_aworklist _ ?X (subst_tvar_in_aworklist _ ?X0 _)] |- _ =>
    rewrite subst_tvar_in_awl_rename_tvar_comm_neq in H; auto
  end.


Lemma notin_rename_tvar_in_aworklist : forall X X' Γ,
  X <> X' ->
  X `notin` ftvar_in_aworklist' (rename_tvar_in_aworklist X' X Γ).
Proof.
  induction Γ; intros; simpl in *; auto.
  - simpl. rewrite ftvar_in_abind_subst_tvar_in_abind_upper; simpl; auto.
  - destruct (X0 == X); auto; subst;
    rewrite ftvar_in_abind_subst_tvar_in_abind_upper; simpl; auto.
  - rewrite ftvar_in_work_subst_tvar_in_work_upper; simpl; auto.
Qed.


Ltac solve_notin_rename_tvar :=
  repeat
    match goal with
    | H : _ |- context [?e1 ^ᵉₑ ?e2] => rewrite ftvar_in_exp_open_exp_wrt_exp_upper
    | H : _ |- context [rename_tvar_in_aworklist ?X' ?X ?Γ] =>
      (* assert True *)
      match goal with
      | H1 : X `notin` ftvar_in_aworklist' (rename_tvar_in_aworklist X' X Γ) |- _ => fail 1
      | _ =>
        assert (X `notin` ftvar_in_aworklist' (rename_tvar_in_aworklist X' X Γ)) by now apply notin_rename_tvar_in_aworklist
      end
    | H : _ |- context [subst_tvar_in_conts ?X' ?X ?c] =>
      match goal with
      | H1 : (X `notin` (ftvar_in_conts (subst_tvar_in_conts X' X c))) |- _ => fail 1
      | _ =>
        assert (X `notin` (ftvar_in_conts (subst_tvar_in_conts X' X c))) by (simpl; apply subst_tvar_in_conts_fresh_same; auto)
      end
    | H : _ |- context [subst_tvar_in_contd ?X' ?X ?c] =>
      match goal with
      | H1 : (X `notin` (ftvar_in_contd (subst_tvar_in_contd X' X c))) |- _ => fail 1
      | _ =>
        assert (X `notin` (ftvar_in_contd (subst_tvar_in_contd X' X c))) by (simpl; apply subst_tvar_in_contd_fresh_same; auto)
      end
    | H : _ |- context [subst_tvar_in_exp ?X' ?X ?e] =>
      match goal with
      | H1 : (X `notin` (ftvar_in_exp (subst_tvar_in_exp X' X e))) |- _ => fail 1
      | _ =>
        assert (X `notin` (ftvar_in_exp (subst_tvar_in_exp X' X e))) by (simpl; apply subst_tvar_in_exp_fresh_same; auto)
      end
    | H : _ |- context [subst_tvar_in_typ ?X' ?X ?t] =>
      match goal with
      | H1 : (X `notin` (ftvar_in_typ (subst_tvar_in_typ X' X t))) |- _ => fail 1
      | _ =>
        assert (X `notin` (ftvar_in_typ (subst_tvar_in_typ X' X t))) by (simpl; apply subst_tvar_in_typ_fresh_same; auto)
      end
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- context [ftvar_in_aworklist' ?Γ2] =>
      rewrite (a_worklist_subst_ftavr_in_aworklist_2 _ _ _ _ _ H); eauto
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- context [ftvar_in_aworklist' ?Γ1] =>
      rewrite (a_worklist_subst_ftavr_in_aworklist_1 _ _ _ _ _ H); eauto
    | H : _ |- _ => idtac
    end; auto.


(* Ltac solve_tvar_notin_ftvarlist_worklist_subst :=
  (* repeat *)
    lazymatch goal with
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- ?X ∉ ftvar_in_aworklist' ?Γ2 =>
      rewrite (a_worklist_subst_ftavr_in_aworklist_2 _ _ _ _ _ H); eauto; try (progress simpl; auto); try (progress solve_notin_rename_tvar; auto)
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- ?X ∉ ftvar_in_aworklist' ?Γ1 =>
      rewrite (a_worklist_subst_ftavr_in_aworklist_1 _ _ _ _ _ H); eauto; try (progress simpl; auto); try (progress solve_notin_rename_tvar; auto)
    end. *)

Ltac rewrite_aworklist_rename_rev' :=
  lazymatch goal with
  | H : context [rename_tvar_in_aworklist _ _ (rename_tvar_in_aworklist ?X' ?X ?Γ)] |- _ =>
    let H1 := fresh "H" in
    assert (H1: X' `notin` ftvar_in_aworklist' Γ) by (auto; solve_notin_rename_tvar);
    rewrite rename_tvar_in_aworklist_rev_eq in H; auto
  end.

Ltac rewrite_aworklist_rename_rev :=
  repeat rewrite_aworklist_rename_rev'.


Ltac rewrite_aworklist_rename_subst' :=
  match goal with
  | H : context [rename_tvar_in_aworklist _ ?X (subst_tvar_in_aworklist ?A ?X _)] |- _ =>
    rewrite subst_tvar_in_awl_rename_tvar_comm_eq in H; try solve [apply notin_rename_tvar_in_aworklist; auto]; try solve
      [rewrite a_worklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
  | H : context [rename_tvar_in_aworklist _ ?X (subst_tvar_in_aworklist _ ?X0 _)] |- _ =>
    rewrite subst_tvar_in_awl_rename_tvar_comm_neq in H; auto
  end.

Ltac rewrite_aworklist_rename :=
  rewrite_aworklist_rename_tvar';
  rewrite_aworklist_rename_subst'.

(* - *)

Lemma rename_tvar_in_aworklist_fresh_eq : forall X X' Γ,
  X `notin` ftvar_in_aworklist' Γ ->
  rename_tvar_in_aworklist X' X Γ = Γ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - rewrite IHΓ; auto.
    rewrite subst_tvar_in_abind_fresh_eq; auto.
  - rewrite IHΓ; auto.
    rewrite subst_tvar_in_abind_fresh_eq; auto.
    destruct (X0 == X); auto.
    + subst. solve_notin_eq X.
  - rewrite IHΓ; auto.
    rewrite subst_tvar_in_work_fresh_eq; auto.
Qed.


Lemma ftvar_in_typ_rename : forall A X Y,
   X `in` ftvar_in_typ A -> Y `in` ftvar_in_typ ({`Y /ᵗ X} A).
Proof.
  intros. induction A; simpl in *; auto; try fsetdec.
  - simpl in *. apply singleton_iff in H. subst.
    destruct_eq_atom. simpl. fsetdec.
Qed.

Lemma worklist_subst_rename_tvar : forall Γ X1 X2 X' A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_typ A `union` ftvar_in_aworklist' Γ `union` singleton X2 ->
  aworklist_subst Γ X2 A Γ1 Γ2 ->
  aworklist_subst (rename_tvar_in_aworklist X' X1 Γ) (if X2 == X1 then X' else X2) ({` X' /ᵗ X1} A)
      (rename_tvar_in_aworklist X' X1 Γ1) (rename_tvar_in_aworklist X' X1 Γ2).
Proof with auto.
  intros. induction H1; try solve [simpl; eauto].
  - simpl in *. destruct (X == X1).
    + subst.
      constructor...
      apply IHaworklist_subst; auto.
      dependent destruction H...
    + constructor...
      apply IHaworklist_subst...
      dependent destruction H...
  - simpl in *.
    _apply_IH_a_wl_red...
    destruct_eq_atom.
    + subst. constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + subst. constructor...
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *.  _apply_IH_a_wl_red...
    destruct_eq_atom.
    + subst. constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + subst. constructor...
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *. _apply_IH_a_wl_red...
  - simpl in *. _apply_IH_a_wl_red...
      destruct_eq_atom.
    + subst. constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + subst. constructor...
      rewrite subst_tvar_in_typ_fresh_eq...
    + constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *.
    assert (⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1)) by applys a_wf_wl_move_etvar_back H.
    apply IHaworklist_subst in H4. destruct_eq_atom.
    + rewrite_aworklist_rename_tvar'.
      applys a_ws1__etvar_move H4... applys* ftvar_in_typ_subst_tvar_in_typ_lower.
    + rewrite_aworklist_rename_tvar'.
      forwards*: a_ws1__etvar_move X' H4.
      apply ftvar_in_typ_rename...
    + rewrite_aworklist_rename_tvar'.
      applys a_ws1__etvar_move H4... applys* ftvar_in_typ_subst_tvar_in_typ_lower.
    + autorewrite with core. rewrite ftvar_in_aworklist'_awl_app in H0.
      rewrite ftvar_in_aworklist'_awl_cons in H0.
      solve_notin.
Qed.


Lemma a_wf_wl_rename_tvar_in_awl : forall Γ X X',
  ⊢ᵃʷ Γ ->
  X' `notin` dom (awl_to_aenv Γ) ->
  ⊢ᵃʷ (rename_tvar_in_aworklist X' X Γ).
Proof.
  intros. induction H; try solve [simpl in *; eauto].
  - simpl in *. econstructor; auto.
    admit. admit.
  - simpl in *. destruct (X0 == X); subst.
    + constructor; auto.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto.
    + constructor; auto. admit.
  - simpl in *. destruct (X0 == X); subst.
    + constructor; auto.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto.
    + constructor; auto. admit.
  - simpl in *. destruct (X0 == X); subst.
    + constructor; auto.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto.
    + constructor; auto. admit.
  - simpl.
Admitted.



Theorem a_wl_red_rename_tvar : forall Γ X X',
  X <> X' ->
  ⊢ᵃʷ Γ ->
  (* needs to change to (dom (awl_to_aenv Γ))*)
  X' `notin` ftvar_in_aworklist' Γ ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_tvar_in_aworklist X' X Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto; solve_false.
  intros. dependent induction H2; try solve [simpl in *; try _apply_IH_a_wl_red; eauto].
  - simpl in *. destruct (X0 == X); _apply_IH_a_wl_red...
  - simpl.
    destruct_a_wf_wl. dependent destruction H0.
    inst_cofinites_for a_wl_red__sub_alll.
    + apply neq_all_rename...
    + apply neq_intersection_rename...
    + apply neq_union_rename...
    + intros. simpl in *. inst_cofinites_with X0.
      rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      destruct_eq_atom.
      auto_apply.
      * admit. (* wf *)
      * repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *. destruct_a_wf_wl.
    dependent destruction H0. dependent destruction H2.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X0.
    simpl in H0.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    destruct_eq_atom.
    auto_apply.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    destruct (X0 == X);
    inst_cofinites_for a_wl_red__sub_arrow1...
    + subst. apply rename_tvar_in_aworklist_bind_same_eq; auto...
      destruct_a_wf_wl; auto.
    + admit. (* mono *)
    + subst. admit.
    + intros. simpl in *. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H9 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        apply H6 in Hws as Hawlred; simpl; auto.
        -- destruct_eq_atom. clear Hws.
           rewrite_aworklist_rename; simpl; eauto.
           rewrite_aworklist_rename_rev.
           simpl in *. destruct_eq_atom. auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl. apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); eauto.
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
      destruct_a_wf_wl; auto.
    + admit. (* mono *)
    + admit.
    + intros. simpl in *.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H9 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl; apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); auto.
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__sub_arrow2...
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + admit. (* mono *)
    + admit.
    + intros. simpl in *. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H10 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        apply H8 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl. apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); auto.
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + admit. (* mono *)
    + admit.
    + intros. simpl in *.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H10 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H8 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl. apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); auto...
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto. 
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename_tvar with (X':=X') (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
      apply a_wl_red__sub_etvarmono1 with
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + apply rename_tvar_in_aworklist_bind_same_eq; eauto...
    + apply a_mono_typ_rename_tvar...
    + admit.
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply a_worklist_subst_wf_wl; eauto.
      rewrite a_worklist_subst_ftavr_in_aworklist with (Γ:=Γ); auto.
    + admit. (* bind *)
    + apply a_mono_typ_rename_tvar...
    + admit.
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply a_worklist_subst_wf_wl; eauto.
      * rewrite a_worklist_subst_ftavr_in_aworklist; auto...
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename_tvar with (X':=X') (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
      apply a_wl_red__sub_etvarmono2 with
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + apply a_mono_typ_rename_tvar...
    + admit.
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply a_worklist_subst_wf_wl; eauto.
      rewrite a_worklist_subst_ftavr_in_aworklist; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + apply a_mono_typ_rename_tvar...
    + admit.
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply a_worklist_subst_wf_wl; eauto.
      * rewrite a_worklist_subst_ftavr_in_aworklist; auto.
  - simpl in *. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H5...
    auto_apply.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *; destruct_a_wf_wl; destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__chk_absetvar.
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + intros. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H11 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        simpl in Hws.
        replace (exp_var_f x) with (subst_tvar_in_exp (` X') X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_tvar_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        eapply H7 with (x:=x) in Hws as Hawlred; simpl in *; auto.
        assert (X `notin` (ftvar_in_exp (subst_tvar_in_exp ` X' X e ^ᵉₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto. admit. admit. (* wf *)
        -- rewrite a_worklist_subst_ftavr_in_aworklist with
            (Γ:=(work_check (e ^ᵉₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); auto. simpl.
          solve_notin_rename_tvar; auto.
        -- solve_notin_rename_tvar; auto.
      * admit. (* wf *)
      * simpl. solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H11 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        replace (exp_var_f x) with (subst_tvar_in_exp (` X') X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_tvar_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        eapply H7 with (x:=x) in Hws as Hawlred; simpl; auto.
        assert (X `notin`(ftvar_in_exp (subst_tvar_in_exp ` X' X e ^ᵉₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto. admit.
           repeat (apply binds_cons). auto.
        -- admit. (* wf *)
        -- rewrite ftvar_in_exp_open_exp_wrt_exp_upper; auto.
      * admit. (* wf *)
      * simpl; solve_notin_rename_tvar; auto.
  - simpl in *.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H3...
    apply H3.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    dependent destruction H0.
    apply a_wf_wl_wf_bind_typ in H3 as Hwfa...
    assert (⊢ᵃʷ (work_applys cs A ⫤ᵃ Γ)) by now destruct_a_wf_wl; eauto.
    eapply a_wl_red__inf_var with (A:=({` X' /ᵗ X} A))...
    apply binds_var_typ_rename_tvar...
    auto_apply.
    + admit. (* wf *)
    + apply tvar_notin_awl_notin_bind_typ with (X:=X') in H3...
  - simpl in *.
    inst_cofinites_for a_wl_red__inf_tabs...
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_exp_open_exp_wrt_typ in H3...
    simpl in H3.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ_fresh2 in H3...
    destruct_eq_atom.
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_exp_open_exp_wrt_typ_upper.
      rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H3.
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    destruct_eq_atom.
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst; inst_cofinites_for a_wl_red__infabs_etvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_contd_rev_eq in Hws; auto.
        assert (X `notin` (ftvar_in_contd ({` X' /ᶜᵈₜ X} cd))) by (solve_notin_rename_tvar; auto).
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- admit. (* wf *)
        -- rewrite a_worklist_subst_ftavr_in_aworklist with
            (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ));
            auto.
      * admit. (* wf *)
      * simpl; solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_contd_rev_eq in Hws; auto.
        assert (X `notin` (ftvar_in_contd ({` X' /ᶜᵈₜ X} cd))) by now solve_notin_rename_tvar.
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- admit. (* wf *)
        -- rewrite a_worklist_subst_ftavr_in_aworklist with
            (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); auto.
      * admit. (* wf *)
      * simpl; solve_notin_rename_tvar; auto...
  - simpl in *. destruct_a_wf_wl.
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    eapply apply_conts_rename_tvar with (X:=X) (X':=X') in H2 as Hac...
    eapply a_wl_red__applys; eauto.
    auto_apply.
    eapply a_wf_wl_apply_conts in H0; eauto.
    + apply ftvar_in_work_apply_cont_eq in H2...
      fsetdec.
  - admit. (* **, should be same as above *)
Admitted.

Lemma worklist_subst_rename_var : forall Γ x x' X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  aworklist_subst (rename_var_in_aworklist x' x Γ) X A (rename_var_in_aworklist x' x Γ1) (rename_var_in_aworklist x' x Γ2).
Proof.
  intros. induction H1; try solve [simpl in *; destruct_a_wf_wl; constructor; auto].
  simpl. admit.
  (* apply IHaworklist_subst *)
Admitted.

Lemma rename_var_in_aworklist_rev_eq : forall x x' Γ,
  x' `notin` fvar_in_aworklist' Γ ->
  rename_var_in_aworklist x x' (rename_var_in_aworklist x' x Γ) = Γ.
Proof.
  induction Γ; simpl in *; auto; intros; destruct_a_wf_wl.
  - destruct_eq_atom.  unfold eq_dec in *. destruct_eq_atom.
    + rewrite IHΓ; auto.
    + rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
    admit.
Admitted.




Lemma awl_app_rename_var_comm : forall Γ1 Γ2 X X',
  awl_app (rename_var_in_aworklist X' X Γ2) (rename_var_in_aworklist X' X Γ1) =
  rename_var_in_aworklist X' X (awl_app Γ2 Γ1).
Proof.
  intros. induction Γ2; simpl in *; auto; rewrite IHΓ2; auto.
Qed.


Lemma fvar_in_aworklist_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  fvar_in_aworklist' Γ [<=] dom (awl_to_aenv Γ).
Proof.
Admitted.


Ltac rewrite_fvar_in_aworklist :=
  match goal with
  | H : context [dom (awl_to_aenv ?Γ)] |- context [fvar_in_aworklist' ?Γ] =>
    rewrite fvar_in_aworklist_upper; auto
  end.

(* Lemma rename_var_in_etvar_list_eq : forall x x' E,
  rename_var_in_aworklist x x' (etvar_list_to_awl E) = (etvar_list_to_awl E).
Proof.
  induction E; simpl; auto.
  rewrite IHE; auto.
Qed. *)


Lemma subst_var_in_awl_rename_tvar_comm : forall Γ x x' X A,
  x' `notin` fvar_in_aworklist' Γ ->
  (rename_var_in_aworklist x' x (subst_tvar_in_aworklist A X Γ)) =
  (subst_tvar_in_aworklist A X (rename_var_in_aworklist x' x Γ)).
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal.
    admit.
Admitted.


Lemma a_worklist_subst_fvar_in_aworklist_2 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  fvar_in_aworklist' Γ2 [<=] fvar_in_aworklist' Γ.
Proof.
  intros. induction H; simpl; try fsetdec.
  admit.
Admitted.


Lemma a_worklist_subst_fvar_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  fvar_in_aworklist' Γ1 [<=] fvar_in_aworklist' Γ.
Proof.
  intros. induction H; simpl; try fsetdec.
  admit.
Admitted.


Lemma notin_rename_var_in_aworklist : forall x x' Γ,
  x <> x' ->
  x `notin` fvar_in_aworklist' (rename_var_in_aworklist x' x Γ).
Proof.
  induction Γ; intros; simpl in *; auto.
  - destruct_eq_atom; auto.
  - simpl. rewrite fvar_in_work_subst_var_in_work_upper; simpl; auto.
Qed.

Lemma rename_var_in_exp_rev_eq : forall x x' e,
  x' `notin` fvar_in_exp e ->
  subst_var_in_exp (exp_var_f x) x' (subst_var_in_exp (exp_var_f x') x e) = e
with rename_var_in_body_rev_eq : forall x x' b,
  x' `notin` fvar_in_body b ->
  subst_var_in_body (exp_var_f x) x' (subst_var_in_body (exp_var_f x') x b) = b.
Proof.
  - intros. induction e; simpl in *; auto;
    try rewrite IHe; try rewrite IHe1; try rewrite IHe2; auto.
    + destruct_eq_atom.
      * simpl. destruct_eq_atom; auto.
      * simpl. destruct_eq_atom; auto.
    + rewrite rename_var_in_body_rev_eq; auto.
  - intros. destruct b; simpl in *; auto.
    rewrite rename_var_in_exp_rev_eq; auto.
Qed.

Lemma apply_cont_rename_var : forall x x' c w A,
  apply_conts c A w ->
  apply_conts (subst_var_in_conts (exp_var_f x') x c) A (subst_var_in_work (exp_var_f x') x w).
Proof.
  intros. induction H; simpl; try constructor.
Qed.

Ltac solve_notin_rename_var' :=
  match goal with
  | H : context [(dom (awl_to_aenv ?Γ))] |- context [fvar_in_aworklist' ?Γ] =>
    rewrite fvar_in_aworklist_upper; auto
  | H : _ |- context [open_exp_wrt_exp ?e1 ?e2] =>
    rewrite fvar_in_exp_open_exp_wrt_exp_upper; auto
  | H : _ |- context [subst_var_in_exp ?e1 ?x ?e2]  =>
    match goal with
    | H1 : x `notin` fvar_in_exp (subst_var_in_exp e1 x e2) |- _ => fail 1
    | _ => assert (x `notin` fvar_in_exp (subst_var_in_exp e1 x e2)) by (apply subst_var_in_exp_fresh_same; auto)
    end
  | H : _ |- context [rename_var_in_aworklist ?x' ?x ?Γ] =>
    (* assert True *)
    match goal with
    | H1 : x `notin` fvar_in_aworklist' (rename_var_in_aworklist x' x Γ) |- _ => fail 1
    | _ =>
      assert (x `notin` fvar_in_aworklist' (rename_var_in_aworklist x' x Γ)) by
        (apply notin_rename_var_in_aworklist; auto)
    end
  | H : aworklist_subst ?Γ ?X ?A ?Γ1 ?Γ2 |- context [fvar_in_aworklist' ?Γ2] =>
      rewrite a_worklist_subst_fvar_in_aworklist_2; eauto
  | H : aworklist_subst ?Γ ?X ?A ?Γ1 ?Γ2 |- context [fvar_in_aworklist' ?Γ1] =>
      rewrite a_worklist_subst_fvar_in_aworklist_1; eauto
  end; auto.

Ltac solve_notin_rename_var :=
  simpl in *;
  repeat solve_notin_rename_var'.

Ltac rewrite_aworklist_rename_var_rev' :=
  match goal with
  | H : context [rename_var_in_aworklist _ _ (rename_var_in_aworklist _ _ _)] |- _ =>
      rewrite rename_var_in_aworklist_rev_eq in H; repeat solve_notin_rename_var
  end.

Ltac rewrite_aworklist_rename_var_rev :=
  repeat rewrite_aworklist_rename_var_rev'.


Ltac rewrite_aworklist_rename_var' :=
  match goal with
  | H : context [rename_var_in_aworklist _ _ (awl_app _ _)] |- _ =>
      rewrite <- awl_app_rename_var_comm in H; simpl; auto
  | H : context [rename_var_in_aworklist _ _ (subst_tvar_in_aworklist _ _ _)] |- _ =>
      rewrite subst_var_in_awl_rename_tvar_comm in H; auto;
      solve_notin_rename_var
  end.

Ltac rewrite_aworklist_rename_var :=
  repeat rewrite_aworklist_rename_var'.

Theorem a_wl_red_rename_var : forall Γ x x',
  ⊢ᵃʷ Γ ->
  x' <> x ->
  x' `notin` (dom (awl_to_aenv Γ)) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_var_in_aworklist x' x Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto.
  intros. dependent induction H2; try solve [simpl in *; try _apply_IH_a_wl_red; eauto].
  - simpl.
    dependent destruction H.
    inst_cofinites_for a_wl_red__sub_alll; auto.
    + intros. simpl in *. inst_cofinites_with X.
      auto_apply; auto.
      admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X...
    auto_apply; auto.
    admit.  (* wf *)
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow1; auto.
    + admit. (* binds *)
    + admit. (* mono *)
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H10 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H8 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev.
           auto.
        -- admit. (* wf *)
        -- admit. (* notin *)
      * admit.
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow2; auto.
    + admit.
    + admit.
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H12 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H9 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev.
           auto.
        -- admit. (* wf *)
        -- admit. (* notin *)
      * admit. (* wf *)
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono1 with (Γ1:=(rename_var_in_aworklist x' x Γ1))
      (Γ2:=(rename_var_in_aworklist x' x Γ2)); auto.
    + admit. (* binds *)
    + admit. (* mono *)
    + apply worklist_subst_rename_var with (x:=x) (x':=x') in H7 as Hws; eauto.
      * rewrite fvar_in_aworklist_upper; auto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev.
      auto_apply; auto.
      * admit. (* wf *)
      * admit. (* notin *)
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono2 with (Γ1:=(rename_var_in_aworklist x' x Γ1))
      (Γ2:=(rename_var_in_aworklist x' x Γ2)); auto.
    + admit. (* binds *)
    + admit. (* mono *)
    + apply worklist_subst_rename_var with (x:=x) (x':=x') in H7 as Hws; eauto.
      * rewrite fvar_in_aworklist_upper; auto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev.
      auto_apply.
      * admit. (* wf *)
      * admit. (* notin *)
  - simpl in *.
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x0.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    admit. (* wf *)
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absetvar.
    + admit. (* binds *)
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H11 as Hws.
      simpl in Hws. destruct_eq_atom.
      rewrite_aworklist_rename_var_rev.
      * simpl in Hws.
        replace (({exp_var_f x' /ᵉₑ x} e) ^ᵉₑ exp_var_f x0) with
          (({exp_var_f x' /ᵉₑ x} e) ^ᵉₑ ({exp_var_f x' /ᵉₑ x} exp_var_f x0)) in Hws by (simpl; destruct_eq_atom; auto).
        rewrite <- subst_var_in_exp_open_exp_wrt_exp in Hws; auto.
        rewrite rename_var_in_exp_rev_eq in Hws.
        -- apply H7 in Hws; auto.
           ++ rewrite_aworklist_rename_var.
              rewrite_aworklist_rename_var_rev.
              auto.
           ++ admit. (* wf *)
           ++ admit. (* notin *)
        -- admit. (* notin *)
      * admit. (* wf *)
      * simpl.
        rewrite fvar_in_exp_open_exp_wrt_exp_upper.
        assert (x `notin` fvar_in_exp ({exp_var_f x' /ᵉₑ x} e)) by (apply subst_var_in_exp_fresh_same; auto).
        solve_notin_rename_var.
  - simpl in *.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x0.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    admit. (* wf *)
  - simpl in *.
    destruct (x0 == x); subst; apply a_wl_red__inf_var with (A:=A).
    + admit.
    + auto_apply; auto. admit.
    + admit.
    + auto_apply; auto. admit.
  - simpl in *.
    inst_cofinites_for  a_wl_red__inf_tabs...
    intros. inst_cofinites_with X.
    rewrite subst_var_in_exp_open_exp_wrt_typ in *...
    auto_apply...
    admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros.
    destruct_eq_atom.
    inst_cofinites_with x0. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *; auto; simpl in *.
    destruct_eq_atom.
    auto_apply; auto.
    admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X.
    auto_apply; auto.
    admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__infabs_etvar; auto.
    + admit. (* binds *)
    + intros. admit.
  - simpl in *.
    eapply a_wl_red__inftapp_all.
    auto_apply; auto.
    admit. (* wf *)
  - simpl in *.
    eapply apply_cont_rename_var with (x':=x') (x:=x) in H2 as Hac.
    econstructor; eauto.
    auto_apply...
    eapply a_wf_wl_apply_conts; eauto.
  - admit. (* *, should be same as above *)
Admitted.
