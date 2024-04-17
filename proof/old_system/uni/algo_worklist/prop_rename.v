Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import ltac_utils.


Open Scope aworklist_scope.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.
#[local] Hint Rewrite dom_app dom_cons : core.


Fixpoint rename_tvar_in_aworklist (X' X:typvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_consvar Γ' x b) => aworklist_consvar (rename_tvar_in_aworklist X' X Γ') x (subst_tvar_in_abind (typ_var_f X') X b)
  | (aworklist_constvar Γ' X0 b) => aworklist_constvar (rename_tvar_in_aworklist X' X Γ') (if X0 == X then X' else X0) (subst_tvar_in_abind (typ_var_f X') X b)
  | (aworklist_conswork Γ' w) => aworklist_conswork (rename_tvar_in_aworklist X' X Γ') (subst_tvar_in_work (typ_var_f X') X w)
end.

Fixpoint rename_var_in_aworklist (x' x:expvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_consvar Γ' x0 b) => aworklist_consvar (rename_var_in_aworklist x' x Γ')  (if x0 == x then x' else x0) b
  | (aworklist_constvar Γ' X b) => aworklist_constvar (rename_var_in_aworklist x' x Γ') X b
  | (aworklist_conswork Γ' w) => aworklist_conswork (rename_var_in_aworklist x' x Γ') (subst_var_in_work (exp_var_f x') x w)
  end.


(* a group of rename lemmas for tvar *)
Lemma rename_tvar_in_aworklist_bind_same : forall Γ X1 X2 X' b,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_aworklist' Γ ->
  binds X1 b (⌊ Γ ⌋ᵃ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds (if X1 == X2 then X' else X1) b (⌊ rename_tvar_in_aworklist X' X2 Γ ⌋ᵃ).
Proof with solve_false.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H. destruct_eq_atom.
    + inversion H3.
      * dependent destruction H5...
      * apply binds_cons; auto.
    + inversion H3.
      * dependent destruction H5...
      * apply binds_cons; auto.
  - dependent destruction H; destruct_eq_atom; subst;
    try solve constructor; inversion H2; try dependent destruction H4; try solve [apply binds_cons; auto]...
    all: try solve [simpl; constructor; auto].
  - destruct_eq_atom; dependent destruction H; auto.
Qed.

Corollary rename_tvar_in_aworklist_bind_same_neq : forall Γ X1 X2 X' b,
  ⊢ᵃʷ Γ ->
  X1 <> X2 ->
  X' `notin` ftvar_in_aworklist' Γ ->
  binds X1 b  (⌊ Γ ⌋ᵃ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds X1 b (⌊ rename_tvar_in_aworklist X' X2 Γ ⌋ᵃ).
Proof.
  intros. eapply rename_tvar_in_aworklist_bind_same with (X2:=X2) in H1; eauto.
  destruct_eq_atom; auto.
Qed.

Corollary rename_tvar_in_aworklist_bind_same_eq : forall Γ X X' b,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_aworklist' Γ ->
  binds X b (awl_to_aenv Γ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds (X') b (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)).
Proof with solve_false.
  intros. eapply rename_tvar_in_aworklist_bind_same with (X2:=X) in H1; eauto...
  destruct_eq_atom; auto.
Qed.

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
  ftvar_in_aworklist' (Γ2 ⧺ Γ1) [=] ftvar_in_aworklist' Γ2 `union` ftvar_in_aworklist' Γ1.
Proof.
  induction Γ2; simpl; fsetdec.
Qed.



#[local] Hint Rewrite dom_app dom_cons : core.


Lemma ftvar_in_a_wf_typ_upper : forall Γ A,
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
  a_wf_exp (awl_to_aenv Γ) e ->
  ftvar_in_exp e [<=] dom (awl_to_aenv Γ)
with ftvar_in_wf_body_upper : forall Γ b,
  a_wf_body (awl_to_aenv Γ) b ->
  ftvar_in_body b [<=] dom (awl_to_aenv Γ).
Proof.
  - intros. dependent induction H; try solve [simpl; fsetdec].
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_exp e).
      assert (ftvar_in_exp e [<=] ftvar_in_exp (e ᵉ^ₑ exp_var_f x)) by apply ftvar_in_exp_open_exp_wrt_exp_lower.
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
  a_wf_conts (awl_to_aenv Γ) cs ->
  ftvar_in_conts cs [<=] dom (awl_to_aenv Γ)
with ftvar_in_wf_contd_upper : forall Γ cd,
  a_wf_contd (awl_to_aenv Γ) cd ->
  ftvar_in_contd cd [<=] dom (awl_to_aenv Γ).
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
  a_wf_work (awl_to_aenv Γ) w ->
  ftvar_in_work w [<=] dom (awl_to_aenv Γ).
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

Lemma ftvar_in_aworklist_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  ftvar_in_aworklist' Γ [<=] dom (awl_to_aenv Γ).
Proof.
  intros; induction H; auto; try solve [simpl; fsetdec].
  - simpl. rewrite ftvar_in_a_wf_typ_upper; eauto. fsetdec.
  - simpl. rewrite ftvar_in_wf_work_upper; eauto. fsetdec.
Qed.

(* -- *)


#[local] Hint Rewrite ftvar_in_aworklist'_awl_cons ftvar_in_aworklist'_awl_app : core.

Lemma rename_tvar_in_typ_rev_eq : forall X X' A,
  X' `notin` ftvar_in_typ A ->
  {` X ᵗ/ₜ X'} {` X' ᵗ/ₜ X} A = A.
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
  {` X ᵉ/ₜ X'} {` X' ᵉ/ₜ X} e = e
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
  {` X ᶜˢ/ₜ X'} {` X' ᶜˢ/ₜ X} cs = cs
with rename_tvar_in_contd_rev_eq : forall X X' cd,
  X' `notin` ftvar_in_contd cd ->
  {` X ᶜᵈ/ₜ X'} {` X' ᶜᵈ/ₜ X} cd = cd.
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
  {` X ʷ/ₜ X'} {` X' ʷ/ₜ X} w = w.
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
  {` X' ᵗ/ₜ X} {B ᵗ/ₜ X} A = {({` X' ᵗ/ₜ X} B) ᵗ/ₜ X'} {` X' ᵗ/ₜ X} A.
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
  {` X' ᵉ/ₜ X} {A ᵉ/ₜ X} e = {({` X' ᵗ/ₜ X} A) ᵉ/ₜ X'} {` X' ᵉ/ₜ X} e
with subst_tvar_in_body_rename_tvar : forall X X' b A,
  X' `notin` ftvar_in_body b ->
  (subst_tvar_in_body ` X' X (subst_tvar_in_body A X b)) =
  (subst_tvar_in_body ({` X' ᵗ/ₜ X} A) X' (subst_tvar_in_body ` X' X b)).
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
  {` X' ᶜˢ/ₜ X} {A ᶜˢ/ₜ X} cs = {({` X' ᵗ/ₜ X} A) ᶜˢ/ₜ X'} {` X' ᶜˢ/ₜ X} cs
with subst_tvar_in_contd_rename : forall X X' A cd,
  X' `notin` ftvar_in_contd cd ->
  {` X' ᶜᵈ/ₜ X} {A ᶜᵈ/ₜ X} cd = {({` X' ᵗ/ₜ X} A) ᶜᵈ/ₜ X'} {` X' ᶜᵈ/ₜ X} cd.
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
  {` X' ʷ/ₜ X} {A ʷ/ₜ X} w = {({` X' ᵗ/ₜ X} A) ʷ/ₜ X'} {` X' ʷ/ₜ X} w.
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
  (subst_tvar_in_aworklist ({` X' ᵗ/ₜ X} A) X' (rename_tvar_in_aworklist X' X Γ)).
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
  (subst_tvar_in_aworklist ({` X' ᵗ/ₜ X1} A) X2 (rename_tvar_in_aworklist X' X1 Γ)).
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal. rewrite subst_tvar_in_abind_subst_tvar_in_abind; auto.
  - apply f_equal. rewrite subst_tvar_in_abind_subst_tvar_in_abind; auto.
  - apply f_equal. rewrite subst_tvar_in_work_subst_tvar_in_work; auto.
Qed.

Lemma aworklist_subst_ftavr_in_aworklist : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' ({A ᵃʷ/ₜ X} Γ2 ⧺ Γ1) [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - rewrite ftvar_in_typ_subst_tvar_in_typ_upper; fsetdec.
  - rewrite ftvar_in_work_subst_tvar_in_work_upper; fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.

Lemma aworklist_subst_ftavr_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ1 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.


Lemma aworklist_subst_ftavr_in_aworklist_2 : forall Γ X A Γ1 Γ2,
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
      [rewrite aworklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
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
    | H : _ |- context [?e1 ᵉ^ₑ ?e2] => rewrite ftvar_in_exp_open_exp_wrt_exp_upper
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
      rewrite (aworklist_subst_ftavr_in_aworklist_2 _ _ _ _ _ H); eauto
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- context [ftvar_in_aworklist' ?Γ1] =>
      rewrite (aworklist_subst_ftavr_in_aworklist_1 _ _ _ _ _ H); eauto
    | H : _ |- _ => idtac
    end; auto.


(* Ltac solve_tvar_notin_ftvarlist_worklist_subst :=
  (* repeat *)
    lazymatch goal with
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- ?X ∉ ftvar_in_aworklist' ?Γ2 =>
      rewrite (aworklist_subst_ftavr_in_aworklist_2 _ _ _ _ _ H); eauto; try (progress simpl; auto); try (progress solve_notin_rename_tvar; auto)
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- ?X ∉ ftvar_in_aworklist' ?Γ1 =>
      rewrite (aworklist_subst_ftavr_in_aworklist_1 _ _ _ _ _ H); eauto; try (progress simpl; auto); try (progress solve_notin_rename_tvar; auto)
    end. *)
Ltac preprocess_ftvar_aworklist_subst X :=
  match goal with 
  | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- _ =>
    match goal with 
    | H_1 : X `notin` ftvar_in_aworklist' Γ |- _ => fail 1
    | _ : _ |- _ => assert (X `notin` ftvar_in_aworklist' Γ) by (auto; solve_notin_rename_tvar)
    end;
    match goal with 
    | H_1 :  (X `notin` ftvar_in_typ A) |- _ => fail 1
    | _ : _ |- _ => assert (X `notin` ftvar_in_typ A) by (auto; solve_notin_rename_tvar)
    end
  end.
    

Ltac rewrite_aworklist_rename_rev' :=
  lazymatch goal with
  | H : context [rename_tvar_in_aworklist _ _ (rename_tvar_in_aworklist ?X' ?X ?Γ)] |- _ =>
    try preprocess_ftvar_aworklist_subst X';
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
      [rewrite aworklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
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
   X `in` ftvar_in_typ A -> Y `in` ftvar_in_typ ({`Y ᵗ/ₜ X} A).
Proof.
  intros. induction A; simpl in *; auto; try fsetdec.
  - simpl in *. apply singleton_iff in H. subst.
    destruct_eq_atom. simpl. fsetdec.
Qed.

Lemma worklist_subst_rename_tvar : forall Γ X1 X2 X' A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_typ A `union` ftvar_in_aworklist' Γ `union` singleton X2 ->
  aworklist_subst Γ X2 A Γ1 Γ2 ->
  aworklist_subst (rename_tvar_in_aworklist X' X1 Γ) (if X2 == X1 then X' else X2) ({` X' ᵗ/ₜ X1} A)
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

Ltac create_notin_set :=
  match goal with 
  | H1 : ⊢ᵃʷ ?Γ , H2 : ?X `notin` dom (⌊ ?Γ ⌋ᵃ) |- _ =>
    let Hfv := fresh "Hfv" in
    assert (Hfv: X `notin` ftvar_in_aworklist' Γ) by (rewrite ftvar_in_aworklist_upper; auto)
  end.

Lemma a_mono_typ_rename_tvar : forall Γ X X' A,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_aworklist' Γ ->
  a_mono_typ (⌊ Γ ⌋ᵃ) A ->
  a_mono_typ (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) ({` X' ᵗ/ₜ X} A).
Proof.
  intros.
  dependent induction H1; simpl in *; destruct_eq_atom; auto.
  - constructor; auto.
    apply rename_tvar_in_aworklist_bind_same_eq; eauto. solve_false.
  - constructor; auto.
    apply rename_tvar_in_aworklist_bind_same_neq; eauto. solve_false.
  - apply a_mono_typ__etvar.
    apply rename_tvar_in_aworklist_bind_same_eq; eauto. solve_false.
  - apply a_mono_typ__etvar.
    apply rename_tvar_in_aworklist_bind_same_neq; eauto. solve_false. 
Qed.

(* Lemma awl_binds_atvar_to_env : forall Γ X X' b,
  b = □ \/ b = ■ \/ b = ⬒ ->
  ⊢ᵃʷ Γ ->
  binds X b (awl_to_aenv Γ) ->
  exists Σ1 Σ2, ⌊ Γ ⌋ᵃ = (Σ2 ++ (X, b) :: Σ1) /\ 
               ⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ = ((map (subst_tvar_in_abind `X' X) Σ2) ++ (X', b) :: Σ1).
Proof with eauto.
  intros. induction H0; simpl in *; try solve [eexists; eauto].
  - inversion H1.
  - destruct_binds.
    + destruct H. inversion H. destruct H. inversion H. inversion H.
    + apply IHa_wf_wl in H5...
      destruct H5 as [Σ1 [Σ2 [Heq Hrenameeq]]].
      exists Σ1 ((x, abind_var_typ A) :: Σ2). split; auto.
      * simpl. rewrite Heq. auto.
      * simpl. rewrite Hrenameeq. auto.
  - destruct_binds; destruct_eq_atom.
    + exists (⌊ Γ ⌋ᵃ), (@nil (atom * abind)). 
      split; auto. simpl.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite ftvar_in_aworklist_upper; auto.
    + apply binds_dom_contradiction in H4... contradiction. 
    + apply IHa_wf_wl in H4...
      destruct H4 as [Σ1 [Σ2 [Heq Hrenameeq]]].
      exists Σ1 ((X0, □) :: Σ2). split; auto.
      * simpl. rewrite Heq. auto.
      * simpl. rewrite Hrenameeq. auto.
  - destruct_binds; destruct_eq_atom.
    + exists (⌊ Γ ⌋ᵃ), (@nil (atom * abind)). 
      split; auto. simpl.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite ftvar_in_aworklist_upper; auto.
    + apply binds_dom_contradiction in H4... contradiction. 
    + apply IHa_wf_wl in H4...
      destruct H4 as [Σ1 [Σ2 [Heq Hrenameeq]]].
      exists Σ1 ((X0, ■) :: Σ2). split; auto.
      * simpl. rewrite Heq. auto.
      * simpl. rewrite Hrenameeq. auto.
  - destruct_binds; destruct_eq_atom.
    + exists (⌊ Γ ⌋ᵃ), (@nil (atom * abind)). 
      split; auto. simpl.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite ftvar_in_aworklist_upper; auto.
    + apply binds_dom_contradiction in H4... contradiction. 
    + apply IHa_wf_wl in H4...
      destruct H4 as [Σ1 [Σ2 [Heq Hrenameeq]]].
      exists Σ1 ((X0, ⬒) :: Σ2). split; auto.
      * simpl. rewrite Heq. auto.
      * simpl. rewrite Hrenameeq. auto.
  - destruct_binds; destruct_eq_atom.
    apply IHa_wf_wl in H1...
Qed. *)

Lemma rename_tvar_dom_upper : forall Γ X X',
  dom (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)) [<=] dom (awl_to_aenv Γ) `union` singleton X'.
Proof.
  intros. induction Γ; simpl; try fsetdec.
  destruct_eq_atom; fsetdec.
Qed.


Lemma a_wl_rename_tvar_wf_typ : forall Γ X X' A,
  ⊢ᵃʷ Γ ->
  X' `notin` dom (awl_to_aenv Γ) ->
  a_wf_typ (⌊ Γ ⌋ᵃ) A ->
  a_wf_typ (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) ({` X' ᵗ/ₜ X} A).
Proof.
  intros. dependent induction H1; simpl in *; eauto; destruct_eq_atom; eauto.
  - constructor; auto.
    apply rename_tvar_in_aworklist_bind_same_eq; eauto.
    rewrite ftvar_in_aworklist_upper; eauto. solve_false.
  - constructor; auto.
    apply rename_tvar_in_aworklist_bind_same_neq; eauto.
    rewrite ftvar_in_aworklist_upper; eauto. solve_false.
  - apply a_wf_typ__stvar.
    apply rename_tvar_in_aworklist_bind_same_eq; eauto.
    rewrite ftvar_in_aworklist_upper; eauto. solve_false.
  - apply a_wf_typ__stvar.
    apply rename_tvar_in_aworklist_bind_same_neq; eauto.
    rewrite ftvar_in_aworklist_upper; eauto. solve_false.
  - apply a_wf_typ__etvar.
    apply rename_tvar_in_aworklist_bind_same_eq; eauto.
    rewrite ftvar_in_aworklist_upper; eauto. solve_false.
  - apply a_wf_typ__etvar.
    apply rename_tvar_in_aworklist_bind_same_neq; eauto.
    rewrite ftvar_in_aworklist_upper; eauto. solve_false.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
      apply s_in_subst_inv; auto.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
      replace (X0 ~ □ ++ ⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) with  
        (⌊ rename_tvar_in_aworklist X' X (X0 ~ᵃ □ ;ᵃ Γ) ⌋ᵃ).
      apply H1; eauto.
      simpl. destruct_eq_atom. auto.
Qed.


Lemma binds_var_typ_rename_tvar : forall x A X X' Γ,
  ⊢ᵃʷ Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  binds x (abind_var_typ ({` X' ᵗ/ₜ X} A)) (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)).
Proof with auto.
  intros. induction Γ.
  - simpl in *. inversion H0.
  - simpl in *. inversion H0.
    + dependent destruction H1.
      simpl. constructor...
    + apply binds_cons...
      dependent destruction H...
  - simpl in *. inversion H0.
    + dependent destruction H1.
      inversion H.
    + dependent destruction H; apply binds_cons...
  - dependent destruction H. simpl in *...
Qed.


Lemma a_wl_rename_tvar_wf_exp : forall Γ X X' e,
  ⊢ᵃʷ Γ ->
  X' ∉ dom (⌊ Γ ⌋ᵃ)  ->
  a_wf_exp (⌊ Γ ⌋ᵃ) e ->
  a_wf_exp (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) (subst_tvar_in_exp (typ_var_f X') X e)
with a_wl_rename_tvar_wf_body : forall Γ X X' b,
  ⊢ᵃʷ Γ ->
  X' ∉ dom (⌊ Γ ⌋ᵃ)  ->
  a_wf_body (⌊ Γ ⌋ᵃ) b ->
  a_wf_body (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) (subst_tvar_in_body (typ_var_f X') X b).
Proof with eauto using a_wl_rename_tvar_wf_typ.
  - intros. clear a_wl_rename_tvar_wf_exp. dependent induction H1; simpl in *; auto...
    + eapply binds_var_typ_rename_tvar with (X':=X') (X:=X) in H1...
    + inst_cofinites_for a_wf_exp__abs T:=({`X' ᵗ/ₜ X}T)...
      intros. inst_cofinites_with x.
      replace (x ~ abind_var_typ ({` X' ᵗ/ₜ X} T) ++ ⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) with  
      (⌊ rename_tvar_in_aworklist X' X (x ~ᵃ T ;ᵃ Γ) ⌋ᵃ).
      replace (subst_tvar_in_exp ` X' X e ᵉ^ₑ exp_var_f x) with (subst_tvar_in_exp ` X' X (e ᵉ^ₑ exp_var_f x)).
      apply H1...
      rewrite subst_tvar_in_exp_open_exp_wrt_exp...
      simpl. destruct_eq_atom...
    + inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X0...
      * rewrite subst_tvar_in_body_open_body_wrt_typ_fresh2...
        apply s_in_b_subst_inv...
      * rewrite subst_tvar_in_body_open_body_wrt_typ_fresh2; auto.
        replace (X0 ~ □ ++ ⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) with  
          (⌊ rename_tvar_in_aworklist X' X (X0 ~ᵃ □ ;ᵃ Γ) ⌋ᵃ).
        apply a_wl_rename_tvar_wf_body; eauto.
        simpl. destruct_eq_atom. auto.
  - intros. clear a_wl_rename_tvar_wf_body. dependent destruction H1; simpl in *; auto...
Qed.


Lemma a_wf_exp_weaken_etvar_twice : forall x X1 X2 T e Γ,
  x ~ abind_var_typ T ++ ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ᵉ^ₑ exp_var_f x ->
  (x, abind_var_typ ` X1) :: (X2, ⬒) :: (X1, ⬒) :: ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ᵉ^ₑ exp_var_f x.
Proof.
  intros. apply a_wf_exp_var_binds_another_cons with (A1:=T); auto.
  rewrite_env ((x ~ abind_var_typ T) ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ).
  apply a_wf_exp_weaken; auto.
Qed.

#[local] Hint Immediate  a_wf_exp_weaken_etvar_twice : core.

Lemma a_wl_rename_tvar_wf_conts : forall Γ X X' cs,
  ⊢ᵃʷ Γ ->
  X' ∉ dom (⌊ Γ ⌋ᵃ)  ->
  a_wf_conts (⌊ Γ ⌋ᵃ) cs ->
  a_wf_conts (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) ({` X' ᶜˢ/ₜ X} cs)
with a_wl_rename_tvar_wf_contd : forall Γ X X' cd,
  ⊢ᵃʷ Γ ->
  X' ∉ dom (⌊ Γ ⌋ᵃ)  ->
  a_wf_contd (⌊ Γ ⌋ᵃ) cd ->
  a_wf_contd (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) ({` X' ᶜᵈ/ₜ X} cd).
Proof with auto using a_wl_rename_tvar_wf_typ, a_wl_rename_tvar_wf_exp.
  - intros. clear a_wl_rename_tvar_wf_conts. dependent induction H1; simpl in *; auto...
  - intros. clear a_wl_rename_tvar_wf_contd. dependent induction H1; try repeat destruct_wf_arrow; simpl in *; auto...
Qed.

Lemma a_wl_rename_tvar_wf_work : forall Γ X X' w,
  ⊢ᵃʷ Γ ->
  X' ∉ dom (⌊ Γ ⌋ᵃ)  ->
  a_wf_work (⌊ Γ ⌋ᵃ) w ->
  a_wf_work (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) (subst_tvar_in_work (typ_var_f X') X w).
Proof with auto 8 using a_wl_rename_tvar_wf_typ, a_wl_rename_tvar_wf_exp, a_wl_rename_tvar_wf_conts, a_wl_rename_tvar_wf_contd.
  intros. dependent destruction H1; try repeat destruct_wf_arrow; simpl... 
Qed.
  

Lemma a_wf_wl_rename_tvar : forall Γ X X',
  ⊢ᵃʷ Γ ->
  X' ∉ dom (⌊ Γ ⌋ᵃ) ->
  ⊢ᵃʷ (rename_tvar_in_aworklist X' X Γ).
Proof with eauto.
  intros. induction H; try solve [simpl in *; eauto].
  - simpl in *.  destruct_binds.
    + econstructor; auto.
      rewrite rename_tvar_dom_upper. fsetdec.
      apply a_wl_rename_tvar_wf_typ...
  - simpl in *. destruct_binds; destruct_eq_atom. 
    + rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto...
    + assert (X' ∉ dom (⌊ Γ ⌋ᵃ)) by auto.  
      apply IHa_wf_wl in H2. constructor; auto.
      rewrite rename_tvar_dom_upper; auto.
  - simpl in *. destruct_binds; destruct_eq_atom. 
    + rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto...
    + assert (X' ∉ dom (⌊ Γ ⌋ᵃ)) by auto.  
      apply IHa_wf_wl in H2. constructor; auto.
      rewrite rename_tvar_dom_upper; auto.
  - simpl in *. destruct_binds; destruct_eq_atom. 
    + rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto...
    + assert (X' ∉ dom (⌊ Γ ⌋ᵃ)) by auto.  
      apply IHa_wf_wl in H2. constructor; auto.
      rewrite rename_tvar_dom_upper; auto.
  - simpl in *. constructor; auto.
    apply a_wl_rename_tvar_wf_work...
Qed.


Lemma apply_conts_rename_tvar : forall cs A w X X',
  apply_conts cs A w ->
  apply_conts ({`X' ᶜˢ/ₜ X} cs) ({`X' ᵗ/ₜ X} A) ({` X' ʷ/ₜ X} w).
Proof.
  intros. induction H; simpl; try solve [simpl; eauto].
Qed.


Lemma apply_contd_rename_tvar : forall cd A B w X X',
  apply_contd cd A B w ->
  apply_contd ({`X' ᶜᵈ/ₜ X} cd) ({`X' ᵗ/ₜ X} A) ({`X' ᵗ/ₜ X} B) ({`X' ʷ/ₜ X} w).
Proof.
  intros. induction H; simpl; try solve [simpl; eauto].
Qed.

Lemma aworlist_subst_dom_upper1' : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  dom (⌊ Γ1 ⌋ᵃ) [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros * Haws; simpl; induction Haws; simpl in *; try fsetdec.
  - autorewrite with core in *. simpl in *. fsetdec.
Qed.

Lemma aworlist_subst_dom_upper2' : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  dom (⌊ Γ2 ⌋ᵃ) [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros. induction H; simpl; try fsetdec.
  - autorewrite with core in *. simpl in *. fsetdec.
Qed.

Lemma subst_typ_in_aworklist_dom_eq : forall Γ X A,
  dom (⌊ {A ᵃʷ/ₜ X} Γ ⌋ᵃ) [=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros. induction Γ; simpl; fsetdec.
Qed.

Lemma aworklist_subst_dom_upper : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  dom (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1⌋ᵃ) [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros. autorewrite with core.
  rewrite subst_typ_in_aworklist_dom_eq.
  specialize (aworlist_subst_dom_upper1' _ _ _ _ _ H).
  specialize (aworlist_subst_dom_upper2' _ _ _ _ _ H).
  intros. fsetdec.
Qed.



Corollary a_wf_typ_weaken_cons_twice : forall X1 X2 A Σ,
  Σ ᵗ⊢ᵃ A ->
  (X2, ⬒) :: (X1, ⬒) :: Σ ᵗ⊢ᵃ A.
Proof.
  intros. apply a_wf_typ_weaken_cons. apply a_wf_typ_weaken_cons. auto.
Qed.

Lemma a_mono_typ_false_rename : forall Γ X X' A,
  ⊢ᵃʷ Γ ->
  (a_mono_typ (⌊ Γ ⌋ᵃ) A -> False) ->
  X' `notin` ftvar_in_aworklist' Γ `union` ftvar_in_typ A `union` dom (⌊ Γ ⌋ᵃ) `union` singleton X ->
  a_mono_typ (⌊ rename_tvar_in_aworklist X' X Γ ⌋ᵃ) ({` X' ᵗ/ₜ X} A) -> False.
Proof with eauto.
  intros.
  apply a_mono_typ_rename_tvar with (X':=X) (X:=X') in H2...
  - simpl in H2. rewrite rename_tvar_in_aworklist_rev_eq in H2...
    rewrite rename_tvar_in_typ_rev_eq in H2...  
  - apply a_wf_wl_rename_tvar...
  - apply notin_rename_tvar_in_aworklist...
Qed.


#[local] Hint Immediate a_wf_typ_weaken_cons_twice : core.

Ltac fold_subst :=
  match goal with
  | _ : _ |- context [typ_arrow ({` ?X' ᵗ/ₜ ?X} ?A1) ({` ?X' ᵗ/ₜ ?X} ?A2)] => 
    replace (typ_arrow ({` X' ᵗ/ₜ X} A1) ({` X' ᵗ/ₜ X} A2)) with ({` X' ᵗ/ₜ X} (typ_arrow A1 A2)) by auto
  | H : context [typ_arrow ({` ?X' ᵗ/ₜ ?X} ?A1) ({` ?X' ᵗ/ₜ ?X} ?A2)] |- _ => 
    replace (typ_arrow ({` X' ᵗ/ₜ X} A1) ({` X' ᵗ/ₜ X} A2)) with ({` X' ᵗ/ₜ X} (typ_arrow A1 A2)) in H by auto
  end.


Theorem a_wl_red_rename_tvar : forall Γ X X',
  X <> X' ->
  ⊢ᵃʷ Γ ->
  X' `notin` dom (awl_to_aenv Γ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_tvar_in_aworklist X' X Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto; solve_false.
  intros. dependent induction H2; try solve [simpl in *; try _apply_IH_a_wl_red; eauto]; create_notin_set.
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
      * repeat (constructor; simpl; auto).
        -- apply a_wf_typ_tvar_etvar_cons...
        -- apply a_wf_typ_weaken_cons...
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
    + repeat (constructor; simpl; auto).
      * apply a_wf_typ_tvar_stvar_cons...
      * apply a_wf_typ_tvar_stvar_cons...
    + repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    destruct (X0 == X);
    inst_cofinites_for a_wl_red__sub_arrow1...
    + subst. apply rename_tvar_in_aworklist_bind_same_eq; auto...
      destruct_a_wf_wl; auto.
    + destruct_a_wf_wl. 
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H8 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        apply H5 in Hws as Hawlred; simpl; auto.
        -- clear Hws.
           rewrite_aworklist_rename; simpl; eauto.
           rewrite_aworklist_rename_rev.
           simpl in *. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with 
            (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); eauto. 
      * replace ((work_sub ` X' (typ_arrow ({` X' ᵗ/ₜ X} A1) ({` X' ᵗ/ₜ X} A2)) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                 (rename_tvar_in_aworklist X' X (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_tvar...
        destruct_a_wf_wl. repeat (constructor; simpl; auto).
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
      destruct_a_wf_wl; auto.
    + destruct_a_wf_wl.
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H8 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H5 in Hws as Hawlred; simpl; auto.
        -- destruct_eq_atom. clear Hws.
           rewrite_aworklist_rename; simpl; eauto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub ` X0 (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * replace ((work_sub ` X0 (typ_arrow ({` X' ᵗ/ₜ X} A1) ({` X' ᵗ/ₜ X} A2)) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                 (rename_tvar_in_aworklist X' X (work_sub ` X0 (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_tvar.
        destruct_a_wf_wl. repeat (constructor; simpl; auto). simpl...
      * solve_notin_rename_tvar; auto.
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__sub_arrow2...
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + destruct_a_wf_wl. 
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H9 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        apply H7 in Hws as Hawlred; simpl; auto.
        -- clear Hws. destruct_eq_atom.
           rewrite_aworklist_rename; simpl; eauto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)... 
      * replace ((work_sub (typ_arrow ({` X' ᵗ/ₜ X} A1) ({` X' ᵗ/ₜ X} A2)) ` X'  ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with
                 (rename_tvar_in_aworklist X' X (work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_tvar...
        destruct_a_wf_wl.
        repeat (constructor; simpl; auto).
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + destruct_a_wf_wl. 
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H9 as Hws.
      * simpl in Hws. destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H7 in Hws as Hawlred; simpl; auto.
        -- clear Hws. 
           rewrite_aworklist_rename; simpl; eauto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub (typ_arrow A1 A2) ` X0 ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * replace ((work_sub (typ_arrow ({` X' ᵗ/ₜ X} A1) ({` X' ᵗ/ₜ X} A2)) ` X0  ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                 (rename_tvar_in_aworklist X' X (work_sub (typ_arrow A1 A2) ` X0 ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_tvar... 
        destruct_a_wf_wl.
        repeat (constructor; simpl; auto).
      * solve_notin_rename_tvar; auto. 
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename_tvar with (X':=X') (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
      apply a_wl_red__sub_etvarmono1 with
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + apply rename_tvar_in_aworklist_bind_same_eq; eauto...
    + apply a_mono_typ_rename_tvar...
    + rewrite subst_tvar_in_typ_fresh_eq...
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply aworklist_subst_wf_wl; eauto.
      rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
    + apply rename_tvar_in_aworklist_bind_same_neq... 
    + apply a_mono_typ_rename_tvar...
    + rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply aworklist_subst_wf_wl; eauto.
      * rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename_tvar with (X':=X') (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
      apply a_wl_red__sub_etvarmono2 with
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + apply a_mono_typ_rename_tvar...
    + rewrite subst_tvar_in_typ_fresh_eq...
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply aworklist_subst_wf_wl; eauto.
      rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + apply a_mono_typ_rename_tvar...
    + rewrite ftvar_in_typ_subst_tvar_in_typ_upper... 
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply aworklist_subst_wf_wl; eauto.
      * rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
  - simpl in *. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H5...
    auto_apply.
    + repeat (constructor; simpl; auto).
      -- apply a_wf_exp_var_binds_another_cons with (A1:=T)... 
      -- apply a_wf_typ_weaken_cons...
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *; destruct_a_wf_wl; destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__chk_absetvar. 
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + intros.
      inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H11 as Hws.
      simpl in Hws. destruct_eq_atom.
      * rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        simpl in Hws.
        replace (exp_var_f x) with (subst_tvar_in_exp (` X') X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_tvar_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        -- eapply H7 in Hws as Hawlred; simpl in *; auto.
           ++ assert (X `notin` (ftvar_in_exp (subst_tvar_in_exp ` X' X e ᵉ^ₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
              clear Hws. destruct_eq_atom.
              rewrite_aworklist_rename; simpl; auto.
              rewrite_aworklist_rename_rev. 
              simpl in Hawlred. destruct_eq_atom. auto.
           ++ eapply aworklist_subst_wf_wl in Hws; simpl in *; eauto 9. 
              ** repeat (constructor; simpl; eauto). eapply a_wf_exp_weaken_etvar_twice with (T:=T)...
           ++ rewrite aworklist_subst_dom_upper with (Γ:=(work_check (e ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))... 
        -- solve_notin_rename_tvar; auto.
      * replace ((work_check (subst_tvar_in_exp ` X' X e ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                (rename_tvar_in_aworklist X' X (work_check (e ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        apply a_wf_wl_rename_tvar... repeat (constructor; simpl; eauto).
        simpl. destruct_eq_atom. rewrite subst_tvar_in_exp_open_exp_wrt_exp...
      * simpl. solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.  
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H11 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        replace (exp_var_f x) with (subst_tvar_in_exp (` X') X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_tvar_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        -- eapply H7 in Hws as Hawlred; simpl; auto.
           ++ assert (X `notin`(ftvar_in_exp (subst_tvar_in_exp ` X' X e ᵉ^ₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
              clear Hws. destruct_eq_atom.
              rewrite_aworklist_rename; simpl; auto.
              rewrite_aworklist_rename_rev.
              simpl in Hawlred. destruct_eq_atom. auto.
           ++ eapply aworklist_subst_wf_wl in Hws; simpl; eauto 9.
              repeat (constructor; simpl; eauto).
           ++ rewrite aworklist_subst_dom_upper with (Γ:=(work_check (e ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        -- rewrite ftvar_in_exp_open_exp_wrt_exp_upper; auto.
      * replace ((work_check (subst_tvar_in_exp ` X' X e ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                (rename_tvar_in_aworklist X' X (work_check (e ᵉ^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        apply a_wf_wl_rename_tvar... repeat (constructor; simpl; eauto). 
        simpl. destruct_eq_atom. rewrite subst_tvar_in_exp_open_exp_wrt_exp...
      * simpl; solve_notin_rename_tvar; auto.
  - simpl in *.
    destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H6...
    apply H6.
    + repeat (constructor; simpl; auto).
      apply a_wf_exp_var_binds_another_cons with (A1:=T)...
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    dependent destruction H0.
    apply a_wf_wl_wf_bind_typ in H3 as Hwfa...
    assert (⊢ᵃʷ (work_applys cs A ⫤ᵃ Γ)) by now destruct_a_wf_wl; eauto.
    eapply a_wl_red__inf_var with (A:=({` X' ᵗ/ₜ X} A))...
    apply binds_var_typ_rename_tvar...
  - simpl in *.
    destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__inf_tabs...
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_exp_open_exp_wrt_typ in H6...
    simpl in H6.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ_fresh2 in H6...
    destruct_eq_atom...
    auto_apply...
    + rewrite open_body_wrt_typ_anno in *.
      dependent destruction H1. dependent destruction H0.
      repeat (constructor; simpl; auto)...
      inst_cofinites_for a_wf_typ__all; intros.
      * apply s_in_rename with (Y:=X1) in H1.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H1...
      * apply a_wf_typ_rename_tvar_cons with (Y:=X1) in H2.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2...
  - simpl in *. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H6...
    auto_apply...
    + repeat (constructor; simpl; auto). auto...
      rewrite_env (nil ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ).
      apply a_wf_conts_weaken...
  - simpl in *. destruct_a_wf_wl. dependent destruction H0.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    destruct_eq_atom.
    auto_apply.
    + repeat (constructor; simpl; auto).
      * apply a_wf_typ_tvar_etvar_cons...
      * apply a_wf_contd_weaken_cons... 
    + auto. 
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
        assert (X `notin` (ftvar_in_contd ({` X' ᶜᵈ/ₜ X} cd))) by (solve_notin_rename_tvar; auto).
        apply H6 in Hws as Hawlred; simpl; auto.
        -- clear Hws. destruct_eq_atom.
           rewrite_aworklist_rename; simpl; auto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wl with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; eauto 8.
           repeat (constructor; simpl; auto). 
           apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))... 
      * replace ((work_infabs (typ_arrow ` X1 ` X2) ({` X' ᶜᵈ/ₜ X} cd) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                 (rename_tvar_in_aworklist X' X (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_tvar...
        destruct_a_wf_wl. 
        repeat (constructor; simpl; auto). 
        apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
      * simpl; solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_contd_rev_eq in Hws; auto.
        assert (X `notin` (ftvar_in_contd ({` X' ᶜᵈ/ₜ X} cd))) by now solve_notin_rename_tvar.
        apply H6 in Hws as Hawlred; simpl; auto.
        -- clear Hws. destruct_eq_atom. rewrite_aworklist_rename; simpl; auto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wl with (Γ:= (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ); simpl; eauto 8.
           repeat (constructor; simpl; auto). 
           apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))... 
      * replace ((work_infabs (typ_arrow ` X1 ` X2) ({` X' ᶜᵈ/ₜ X} cd) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_tvar_in_aworklist X' X Γ)) with 
                 (rename_tvar_in_aworklist X' X ((work_infabs (typ_arrow ` X1 ` X2) cd) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_tvar... 
        destruct_a_wf_wl. 
        repeat (constructor; simpl; auto). 
        apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
      * simpl; solve_notin_rename_tvar; auto...
  - simpl in *. destruct_a_wf_wl.
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
    auto_apply...
    + repeat (constructor; simpl; auto).
      eapply a_wf_typ_all_open...
  - simpl in *.
    eapply apply_conts_rename_tvar with (X:=X) (X':=X') in H2 as Hac...
    eapply a_wl_red__applys...
    auto_apply...
    eapply a_wf_wl_apply_conts in H0...
  - simpl in *.
    eapply apply_contd_rename_tvar with (X:=X) (X':=X') in H2 as Hac...
    eapply a_wl_red__applyd...
    auto_apply...
    eapply a_wf_wl_apply_contd in H0... 
Qed.



Lemma rename_var_dom_upper : forall Γ x x',
  dom (awl_to_aenv (rename_var_in_aworklist x' x Γ)) [<=] dom (awl_to_aenv Γ) `union` singleton x'.
Proof.
  intros. induction Γ; simpl; try fsetdec.
  destruct_eq_atom; fsetdec.
Qed.


Lemma fvar_in_aworklist'_awl_app : forall Γ1 Γ2,
  fvar_in_aworklist' (Γ2 ⧺ Γ1) [=] fvar_in_aworklist' Γ2 `union` fvar_in_aworklist' Γ1.
Proof.
  induction Γ2; simpl; fsetdec.
Qed.

Lemma awl_app_rename_var_comm : forall Γ1 Γ2 X X',
  (rename_var_in_aworklist X' X Γ2) ⧺ (rename_var_in_aworklist X' X Γ1) =
  rename_var_in_aworklist X' X (Γ2 ⧺ Γ1).
Proof.
  intros. induction Γ2; simpl in *; auto; rewrite IHΓ2; auto.
Qed.



Lemma worklist_subst_rename_var : forall Γ x x' X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  aworklist_subst (rename_var_in_aworklist x' x Γ) X A (rename_var_in_aworklist x' x Γ1) (rename_var_in_aworklist x' x Γ2).
Proof.
  intros. induction H1; try solve [simpl in *; destruct_a_wf_wl; constructor; auto].
  simpl.
  rewrite <- awl_app_rename_var_comm... simpl.
  constructor; auto.
  replace (rename_var_in_aworklist x' x Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ rename_var_in_aworklist x' x Γ1) with (rename_var_in_aworklist x' x (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1)).
  apply IHaworklist_subst. apply a_wf_wl_move_etvar_back... auto.
  - simpl in *. rewrite fvar_in_aworklist'_awl_app in *. simpl in *. solve_notin.
  - rewrite <- awl_app_rename_var_comm... simpl. auto.
Qed.


Lemma fvar_in_wf_exp_upper : forall Γ e,
  a_wf_exp (awl_to_aenv Γ) e ->
  fvar_in_exp e [<=] dom (awl_to_aenv Γ)
with fvar_in_wf_body_upper : forall Γ b,
  a_wf_body (awl_to_aenv Γ) b ->
  fvar_in_body b [<=] dom (awl_to_aenv Γ).
Proof.
  - intros. dependent induction H; try solve [simpl; fsetdec].
    + simpl. apply binds_In in H... fsetdec.
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` fvar_in_exp e).
      assert (fvar_in_exp e [<=] fvar_in_exp (e ᵉ^ₑ exp_var_f x)) by apply fvar_in_exp_open_exp_wrt_exp_lower.
      assert (x ~ abind_var_typ T ++ awl_to_aenv Γ = awl_to_aenv (x ~ᵃ T ;ᵃ Γ)) by (simpl; auto).
      eapply H1 in H3.
      simpl in *.
      fsetdec.
    + simpl.
      rewrite IHa_wf_exp1; eauto.
      rewrite IHa_wf_exp2; eauto.
      fsetdec.
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` fvar_in_body body5) using_name X.
      replace (X ~ abind_tvar_empty ++ awl_to_aenv Γ) with (awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) in H0 by auto.
      assert (fvar_in_body body5 [<=] fvar_in_body (open_body_wrt_typ body5 ` X)) by apply
        fvar_in_body_open_body_wrt_typ_lower.
      apply fvar_in_wf_body_upper in H0.
      simpl in *.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto. fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto. fsetdec.
  - intros. destruct b; simpl.
    + dependent destruction H.
      rewrite fvar_in_wf_exp_upper; eauto. fsetdec.
Qed.


Lemma fvar_in_wf_conts_upper : forall Γ cs,
  a_wf_conts (awl_to_aenv Γ) cs ->
  fvar_in_conts cs [<=] dom (awl_to_aenv Γ)
with fvar_in_wf_contd_upper : forall Γ cd,
  a_wf_contd (awl_to_aenv Γ) cd ->
  fvar_in_contd cd [<=] dom (awl_to_aenv Γ).
Proof.
  - intros. intros; dependent induction H;
    simpl in *;
    try erewrite fvar_in_wf_exp_upper; eauto;
    try rewrite IHa_wf_conts; eauto; 
    try rewrite ftvar_in_wf_contd_upper; eauto;
    try fsetdec.
  - intros. intros; dependent induction H;
    simpl in *;
    try solve [
    try destruct_wf_arrow;
    try erewrite fvar_in_wf_exp_upper; eauto;
    try rewrite fvar_in_wf_conts_upper; eauto;
    try rewrite IHa_wf_contd; eauto; 
    try fsetdec].
Qed.

Lemma fvar_in_wf_work_upper : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w ->
  fvar_in_work w [<=] dom (awl_to_aenv Γ).
Proof.
  intros. intros; dependent destruction H;
    simpl in *;
    try solve [
    try repeat destruct_wf_arrow;
    try erewrite fvar_in_wf_exp_upper; eauto;
    try rewrite fvar_in_wf_conts_upper; eauto; 
    try rewrite fvar_in_wf_contd_upper; eauto; try fsetdec].
Qed.

Lemma fvar_in_aworklist_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  fvar_in_aworklist' Γ [<=] dom (awl_to_aenv Γ).
Proof.
  intros. induction H; simpl in *; try fsetdec.
  rewrite fvar_in_wf_work_upper; eauto.
  fsetdec.
Qed.


Ltac rewrite_fvar_in_aworklist :=
  match goal with
  | H : context [dom (awl_to_aenv ?Γ)] |- context [fvar_in_aworklist' ?Γ] =>
    rewrite fvar_in_aworklist_upper; auto
  end.
  
Lemma rename_var_in_aworklist_fresh_eq : forall x x' Γ,
  x `notin` fvar_in_aworklist' Γ ->
  rename_var_in_aworklist x' x Γ = Γ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - rewrite IHΓ; auto. 
    destruct_eq_atom; auto.
  - rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
    rewrite subst_var_in_work_fresh_eq; auto.
Qed.


Lemma subst_tvar_in_exp_rename_var : forall x x' X e A,
  x' `notin` fvar_in_exp e ->
  {exp_var_f x' ᵉ/ₑ x} {A ᵉ/ₜ X} e = {A ᵉ/ₜ X} {exp_var_f x' ᵉ/ₑ x} e
with subst_tvar_in_body_rename_var : forall x x' X b A,
   x' `notin` fvar_in_body b ->
  (subst_var_in_body (exp_var_f x') x (subst_tvar_in_body A X b)) =
  (subst_tvar_in_body A X ({exp_var_f x' ᵇ/ₑ x} b)).
Proof with eauto.
  - intros. induction e; simpl in *; auto...
    + destruct_eq_atom; simpl; auto. 
    + rewrite IHe...
    + rewrite IHe1...
      rewrite IHe2...
    + rewrite subst_tvar_in_body_rename_var...
    + rewrite IHe...
    + rewrite IHe...
  - intros. destruct b.
    simpl in *.
    erewrite subst_tvar_in_exp_rename_var; auto.
Qed.

Lemma subst_tvar_in_conts_rename_var : forall x x' X A cs,
  x' `notin` fvar_in_conts cs ->
  {exp_var_f x' ᶜˢ/ₑ x} {A ᶜˢ/ₜ X} cs = {A ᶜˢ/ₜ X} {exp_var_f x' ᶜˢ/ₑ x} cs
with subst_tvar_in_contd_rename_var : forall x x' X A cd,
  x' `notin` fvar_in_contd cd ->
  {exp_var_f x' ᶜᵈ/ₑ x} {A ᶜᵈ/ₜ X} cd = {A ᶜᵈ/ₜ X} {exp_var_f x' ᶜᵈ/ₑ x} cd.
Proof.
  - intros. induction cs; simpl in *;
    try rewrite subst_tvar_in_exp_rename_var; auto;
    try rewrite IHcs; auto;
    try rewrite subst_tvar_in_contd_rename_var; auto...
  - intros. induction cd; simpl in *;
    try repeat rewrite subst_tvar_in_exp_rename_var; auto;
    try rewrite IHcd; auto;
    try rewrite subst_tvar_in_conts_rename_var; auto.
Qed.

Lemma subst_tvar_in_work_rename_var : forall x x' X w A,
  x' `notin` fvar_in_work w ->
  {exp_var_f x' ʷ/ₑ x} {A ʷ/ₜ X} w = {A ʷ/ₜ X} {exp_var_f x' ʷ/ₑ x} w.
Proof.
  intros. induction w; simpl in *; auto;
    try rewrite subst_tvar_in_exp_rename_var; auto;
    try rewrite subst_tvar_in_conts_rename_var; auto;
    try rewrite subst_tvar_in_contd_rename_var; auto.
Qed.

Lemma subst_var_in_awl_rename_tvar_comm : forall Γ x x' X A,
  x' `notin` fvar_in_aworklist' Γ ->
  (rename_var_in_aworklist x' x ({A ᵃʷ/ₜ X} Γ)) =
  {A ᵃʷ/ₜ X} rename_var_in_aworklist x' x Γ.
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal.
    rewrite subst_tvar_in_work_rename_var; auto.
Qed.


Lemma aworklist_subst_fvar_in_aworklist_2 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  fvar_in_aworklist' Γ2 [<=] fvar_in_aworklist' Γ.
Proof.
  intros. induction H; simpl; try fsetdec.
  rewrite fvar_in_aworklist'_awl_app in *. fsetdec.
Qed.


Lemma aworklist_subst_fvar_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  fvar_in_aworklist' Γ1 [<=] fvar_in_aworklist' Γ.
Proof.
  intros. induction H; simpl; try fsetdec.
  rewrite fvar_in_aworklist'_awl_app in *. fsetdec.
Qed.

Lemma rename_var_in_aworklist_tvar_bind_same : forall Γ x X' y b,
  ⊢ᵃʷ Γ ->
  b = □ \/ b = ■ \/ b = ⬒ ->
  y `notin` fvar_in_aworklist' Γ ->
  binds X' b (awl_to_aenv Γ) ->
  binds X' b (awl_to_aenv (rename_var_in_aworklist y x Γ)).
Proof with solve_false.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H. destruct_eq_atom.
    + destruct_binds. destruct H2. inversion H2. destruct H2.  inversion H2. inversion H2.
      * apply binds_cons; auto.
    + destruct_binds.
      * destruct H2. inversion H2. destruct H2. inversion H2. inversion H2.
      * apply binds_cons; auto. 
  - dependent destruction H; destruct_binds; auto.
  - dependent destruction H; eauto.
Qed.

Lemma rename_var_in_aworklist_var_bind_same : forall Γ x x' y A,
  ⊢ᵃʷ Γ ->
  y `notin` fvar_in_aworklist' Γ ->
  binds x' (abind_var_typ A) (awl_to_aenv Γ) ->
  binds (if x' == x then y else x') (abind_var_typ A) (awl_to_aenv (rename_var_in_aworklist y x Γ)).
Proof with solve_false.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H. destruct_eq_atom; destruct_binds; auto.
  - dependent destruction H; destruct_binds; auto.
  - dependent destruction H; eauto.
Qed.

Lemma rename_var_in_aworklist_var_bind_same_eq : forall Γ x y A,
  ⊢ᵃʷ Γ ->
  y `notin` fvar_in_aworklist' Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ ->
  y ~ A ∈ᵃ ⌊ rename_var_in_aworklist y x Γ ⌋ᵃ.
Proof with solve_false.
  intros. eapply rename_var_in_aworklist_var_bind_same with (x':=x) (x:=x) in H1; eauto.
  destruct_eq_atom. auto.  
Qed.


Lemma rename_var_in_aworklist_var_bind_same_neq : forall Γ x x' y A,
  ⊢ᵃʷ Γ ->
  x' <> x ->
  y `notin` fvar_in_aworklist' Γ ->
  x' ~ A ∈ᵃ ⌊ Γ ⌋ᵃ  ->
  x' ~ A ∈ᵃ ⌊ rename_var_in_aworklist y x Γ ⌋ᵃ.
Proof with solve_false.
  intros. eapply rename_var_in_aworklist_var_bind_same with (x':=x') (x:=x) in H1; eauto.
  destruct_eq_atom. auto.  
Qed.

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


Lemma rename_var_in_conts_rev_eq : forall x x' cs,
  x' `notin` fvar_in_conts cs ->
  subst_var_in_conts (exp_var_f x) x' (subst_var_in_conts (exp_var_f x') x cs) = cs
with rename_var_in_contd_rev_eq : forall x x' cd,
  x' `notin` fvar_in_contd cd ->
  subst_var_in_contd (exp_var_f x) x' (subst_var_in_contd (exp_var_f x') x cd) = cd.
Proof with auto using rename_var_in_exp_rev_eq.
  - clear rename_var_in_conts_rev_eq. induction cs; simpl in *; intros;
      try rewrite rename_var_in_exp_rev_eq; auto;
      try rewrite IHcs; auto;
      try rewrite rename_var_in_contd_rev_eq; auto.
  - clear rename_var_in_contd_rev_eq. induction cd; simpl in *; intros;
      try rewrite rename_var_in_exp_rev_eq; auto;
      try rewrite IHcd; auto;
      try rewrite rename_var_in_conts_rev_eq; auto.
Qed.

Lemma rename_var_in_work_rev_eq : forall x x' w,
  x' `notin` fvar_in_work w ->
  subst_var_in_work (exp_var_f x) x' (subst_var_in_work (exp_var_f x') x w) = w.
Proof.
  intros. dependent destruction w; simpl in *;
    try rewrite rename_var_in_exp_rev_eq; 
    try rewrite rename_var_in_conts_rev_eq;
    try rewrite rename_var_in_contd_rev_eq; auto.
Qed.

Lemma rename_var_in_aworklist_rev_eq : forall x x' Γ,
  x' `notin` fvar_in_aworklist' Γ ->
  rename_var_in_aworklist x x' (rename_var_in_aworklist x' x Γ) = Γ.
Proof.
  induction Γ; simpl in *; auto; intros; destruct_a_wf_wl.
  - destruct_eq_atom. 
    + rewrite IHΓ; auto.
    + rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
    rewrite rename_var_in_work_rev_eq; auto.
Qed.

Lemma apply_conts_rename_var : forall x x' cs w A,
  apply_conts cs A w ->
  apply_conts (subst_var_in_conts (exp_var_f x') x cs) A (subst_var_in_work (exp_var_f x') x w).
Proof.
  intros. induction H; simpl; try constructor.
Qed.

Lemma apply_contd_rename_var : forall x x' cd w A B,
  apply_contd cd A B w ->
  apply_contd (subst_var_in_contd (exp_var_f x') x cd) A B (subst_var_in_work (exp_var_f x') x w).
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
  | H : _ |- context [subst_var_in_contd ?cd ?x ?e]  =>
    match goal with
    | H1 : x `notin` fvar_in_contd (subst_var_in_contd cd x e) |- _ => fail 1
    | _ => assert (x `notin` fvar_in_contd (subst_var_in_contd cd x e)) by (apply subst_var_in_contd_fresh_same; auto)
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
      rewrite aworklist_subst_fvar_in_aworklist_2; eauto
  | H : aworklist_subst ?Γ ?X ?A ?Γ1 ?Γ2 |- context [fvar_in_aworklist' ?Γ1] =>
      rewrite aworklist_subst_fvar_in_aworklist_1; eauto
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

Lemma a_wf_typ_rename_var : forall Γ x x' A,
  ⊢ᵃʷ Γ ->
  x' ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ ᵗ⊢ᵃ A.
Proof.
  intros. dependent induction H1; try solve [simpl in *; eauto].
  - constructor. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - apply a_wf_typ__stvar. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - apply a_wf_typ__etvar. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X; auto.
    replace (X ~ □ ++ ⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ ) with (⌊ rename_var_in_aworklist x' x (X ~ᵃ □ ;ᵃ Γ) ⌋ᵃ) by (simpl; auto).
    apply H1; auto.
Qed.


Lemma a_mono_typ_rename_var : forall Γ x x' T,
  ⊢ᵃʷ Γ ->
  x' ∉ fvar_in_aworklist' Γ ->
  a_mono_typ (⌊ Γ ⌋ᵃ) T ->
  a_mono_typ (⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) T.
Proof.
  intros. dependent induction H1; try solve [simpl in *; eauto].
  - constructor. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - apply a_mono_typ__etvar. apply rename_var_in_aworklist_tvar_bind_same; auto.
Qed.


Lemma a_wf_exp_rename_var : forall Γ x x' e,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  a_wf_exp (⌊ Γ ⌋ᵃ) e ->
  a_wf_exp (⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) (subst_var_in_exp (exp_var_f x') x e)
with a_wf_body_rename_var : forall Γ x x' b,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  a_wf_body (⌊ Γ ⌋ᵃ) b ->
  a_wf_body (⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) (subst_var_in_body (exp_var_f x') x b).
Proof with eauto using a_wf_typ_rename_var.
  - intros. clear a_wf_exp_rename_var. dependent induction H1; simpl in *...
    + simpl. destruct_eq_atom.
      * eapply rename_var_in_aworklist_var_bind_same_eq in H1...
      * eapply rename_var_in_aworklist_var_bind_same_neq in H1...
    + inst_cofinites_for a_wf_exp__abs T:=T; intros; inst_cofinites_with x; auto.
      apply a_wf_typ_rename_var...
      replace (({exp_var_f x' ᵉ/ₑ x} e) ᵉ^ₑ exp_var_f x0) with ({exp_var_f x' ᵉ/ₑ x} (e ᵉ^ₑ exp_var_f x0)).
      replace (x0 ~ abind_var_typ T ++ ⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) with (⌊ rename_var_in_aworklist x' x (x0 ~ᵃ T ;ᵃ Γ) ⌋ᵃ)...
      * simpl. destruct_eq_atom...
      * rewrite subst_var_in_exp_open_exp_wrt_exp... simpl. destruct_eq_atom...
    + inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X; auto.
      * destruct body5. simpl.  rewrite open_body_wrt_typ_anno in *.
        dependent destruction H1. simpl. constructor...
        replace (({exp_var_f x' ᵉ/ₑ x} e) ᵉ^ₜ ` X) with ({exp_var_f x' ᵉ/ₑ x} ( e ᵉ^ₜ ` X)).
        apply lc_exp_subst_var_in_exp...
        rewrite subst_var_in_exp_open_exp_wrt_typ...
      * replace (open_body_wrt_typ ({exp_var_f x' ᵇ/ₑ x} body5) ` X) with ({exp_var_f x' ᵇ/ₑ x} (open_body_wrt_typ body5 ` X))...
        replace (X ~ □ ++ ⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) with (⌊ rename_var_in_aworklist x' x (X ~ᵃ □ ;ᵃ Γ) ⌋ᵃ)...
        rewrite subst_var_in_body_open_body_wrt_typ...
  - intros. clear a_wf_body_rename_var. dependent destruction H1. 
    simpl. constructor...
Qed.

Lemma a_wf_conts_rename_var : forall Γ x x' cs,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  a_wf_conts (⌊ Γ ⌋ᵃ) cs ->
  a_wf_conts (⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) (subst_var_in_conts (exp_var_f x') x cs)
with a_wf_contd_rename_var : forall Γ x x' cd,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  a_wf_contd (⌊ Γ ⌋ᵃ) cd ->
  a_wf_contd (⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) (subst_var_in_contd (exp_var_f x') x cd).
Proof with eauto using a_wf_typ_rename_var, a_wf_exp_rename_var.
  - intros. clear a_wf_conts_rename_var. dependent induction H1; simpl...
  - intros. clear a_wf_contd_rename_var. dependent induction H1; simpl...
Qed.


Lemma a_wf_work_rename_var : forall Γ x x' w,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  a_wf_work (⌊ Γ ⌋ᵃ) w ->
  a_wf_work (⌊ rename_var_in_aworklist x' x Γ ⌋ᵃ) (subst_var_in_work (exp_var_f x') x w).
Proof with eauto 10 using a_wf_typ_rename_var, a_wf_exp_rename_var, a_wf_conts_rename_var, a_wf_contd_rename_var.
  intros. dependent destruction H1; simpl in *...
Qed.


Lemma a_wf_wl_rename_var : forall Γ x x',
  ⊢ᵃʷ Γ ->
  x' `notin` dom (awl_to_aenv Γ) ->
  ⊢ᵃʷ (rename_var_in_aworklist x' x Γ).
Proof with eauto.
  intros. induction H; try solve [simpl in *; eauto].
  - simpl in *. destruct_eq_atom. 
    + constructor... rewrite rename_var_in_aworklist_fresh_eq; auto.
      rewrite fvar_in_aworklist_upper; eauto.
      apply a_wf_typ_rename_var; auto. rewrite fvar_in_aworklist_upper; eauto.
    + constructor... rewrite rename_var_dom_upper...
      apply a_wf_typ_rename_var; auto. rewrite fvar_in_aworklist_upper; eauto.
  - simpl in *. destruct_binds.
    assert (x' ∉ dom (⌊ Γ ⌋ᵃ)) by auto.
    apply IHa_wf_wl in H2... constructor... 
    rewrite rename_var_dom_upper; auto... 
  - simpl in *. destruct_binds.
    assert (x' ∉ dom (⌊ Γ ⌋ᵃ)) by auto.
    apply IHa_wf_wl in H2... constructor... 
    rewrite rename_var_dom_upper; auto... 
  - simpl in *. destruct_binds.
    assert (x' ∉ dom (⌊ Γ ⌋ᵃ)) by auto.
    apply IHa_wf_wl in H2... constructor... 
    rewrite rename_var_dom_upper; auto... 
  - simpl in *. constructor; auto.
    apply a_wf_work_rename_var...
    rewrite fvar_in_aworklist_upper; auto... 
Qed.


Ltac create_notin_set_var :=
  match goal with 
  | H1 : ⊢ᵃʷ ?Γ , H2 : ?x `notin` dom (⌊ ?Γ ⌋ᵃ) |- _ =>
    let Hfv := fresh "Hfv" in
    assert (Hfv: x `notin` fvar_in_aworklist' Γ) by (rewrite fvar_in_aworklist_upper; auto)
  end.


Theorem a_wl_red_rename_var : forall Γ x x',
  ⊢ᵃʷ Γ ->
  x' <> x ->
  x' `notin` (dom (awl_to_aenv Γ)) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_var_in_aworklist x' x Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto.
  intros. dependent induction H2; try solve [simpl in *; try _apply_IH_a_wl_red; eauto]; create_notin_set_var.
  - simpl.
    destruct_a_wf_wl. dependent destruction H.
    inst_cofinites_for a_wl_red__sub_alll; auto.
    + intros. simpl in *. inst_cofinites_with X.
      auto_apply; auto.
      repeat (constructor; simpl; auto).
      apply a_wf_typ_tvar_etvar_cons in H0...
      apply a_wf_typ_weaken_cons...
  - destruct_a_wf_wl.
    dependent destruction H.
    dependent destruction H1.
    simpl in *.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X...
    auto_apply; auto.
    repeat (constructor; simpl; auto).
    + apply a_wf_typ_tvar_stvar_cons...
    + apply a_wf_typ_tvar_stvar_cons...
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow1; auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + intros. eapply a_mono_typ_rename_var with (x':=x) (x:=x') in H0... 
      * rewrite rename_var_in_aworklist_rev_eq in H0...
      * apply a_wf_wl_rename_var...
      * solve_notin_rename_var.
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H9 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H7 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev...
        -- eapply aworklist_subst_wf_wl with (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto...
           repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * replace (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_var_in_aworklist x' x Γ) with
          (rename_var_in_aworklist x' x (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_var...
        repeat (constructor; simpl; auto).
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow2; auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + intros. eapply a_mono_typ_rename_var with (x':=x) (x:=x') in H9... 
      * rewrite rename_var_in_aworklist_rev_eq in H9...
      * apply a_wf_wl_rename_var...
      * solve_notin_rename_var.
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H11 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H8 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev...
        -- apply aworklist_subst_wf_wl with (Γ:=(work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto 7.
           repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * replace (work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_var_in_aworklist x' x Γ) with
          (rename_var_in_aworklist x' x (work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_var...
        repeat (constructor; simpl; auto).
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono1 with (Γ1:=(rename_var_in_aworklist x' x Γ1))
      (Γ2:=(rename_var_in_aworklist x' x Γ2)); auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + apply a_mono_typ_rename_var with (x':=x') (x:=x) in H5...
    + apply worklist_subst_rename_var with (x:=x) (x':=x') in H7 as Hws; eauto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev...
      auto_apply; auto.
      * eapply aworklist_subst_wf_wl...
      * erewrite aworklist_subst_dom_upper...
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono2 with (Γ1:=(rename_var_in_aworklist x' x Γ1))
      (Γ2:=(rename_var_in_aworklist x' x Γ2)); auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + apply a_mono_typ_rename_var with (x':=x') (x:=x) in H5...
    + apply worklist_subst_rename_var with (x:=x) (x':=x') in H7 as Hws; eauto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev.
      auto_apply.
      * eapply aworklist_subst_wf_wl...
      * erewrite aworklist_subst_dom_upper...
  - destruct_a_wf_wl. simpl in *. 
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x0.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    repeat (constructor; simpl; auto)...
    + apply a_wf_exp_var_binds_another_cons with (A1:=T)...
    + apply a_wf_typ_weaken_cons...
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absetvar.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + intros. inst_cofinites_with x0. inst_cofinites_with X1. inst_cofinites_with X2.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H11 as Hws.
      simpl in Hws. destruct_eq_atom.
      rewrite_aworklist_rename_var_rev.
      * simpl in Hws.
        replace (({exp_var_f x' ᵉ/ₑ x} e) ᵉ^ₑ exp_var_f x0) with
          (({exp_var_f x' ᵉ/ₑ x} e) ᵉ^ₑ ({exp_var_f x' ᵉ/ₑ x} exp_var_f x0)) in Hws by (simpl; destruct_eq_atom; auto).
        rewrite <- subst_var_in_exp_open_exp_wrt_exp in Hws; auto.
        rewrite rename_var_in_exp_rev_eq in Hws.
        -- apply H7 in Hws; auto.
           ++ rewrite_aworklist_rename_var.
              rewrite_aworklist_rename_var_rev...
           ++ apply aworklist_subst_wf_wl with (Γ:=(work_check (e ᵉ^ₑ exp_var_f x0) ` X2 ⫤ᵃ x0 ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto 7... 
              repeat (constructor; simpl; auto)... apply a_wf_exp_weaken_etvar_twice with (T:=T)...
           ++ rewrite aworklist_subst_dom_upper with (Γ:=(work_check (e ᵉ^ₑ exp_var_f x0) ` X2 ⫤ᵃ x0 ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        -- solve_notin_rename_var.
      * replace ((work_check (({exp_var_f x' ᵉ/ₑ x} e) ᵉ^ₑ exp_var_f x0) ` X2 ⫤ᵃ x0 ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_var_in_aworklist x' x Γ)) with 
                (rename_var_in_aworklist x' x (work_check (e ᵉ^ₑ exp_var_f x0) ` X2 ⫤ᵃ x0 ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        apply a_wf_wl_rename_var...
        repeat (constructor; simpl; auto)...
        simpl. rewrite subst_var_in_exp_open_exp_wrt_exp; simpl; destruct_eq_atom...
      * simpl.
        rewrite fvar_in_exp_open_exp_wrt_exp_upper.
        assert (x `notin` fvar_in_exp ({exp_var_f x' ᵉ/ₑ x} e)) by (apply subst_var_in_exp_fresh_same; auto).
        solve_notin_rename_var.
  - destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x0.
    destruct_eq_atom. 
    rewrite subst_var_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    repeat (constructor; simpl; auto).
    eapply a_wf_exp_var_binds_another_cons with (A1:=T); eauto.
  - simpl in *.
    destruct (x0 == x); subst; apply a_wl_red__inf_var with (A:=A).
    + destruct_a_wf_wl... apply rename_var_in_aworklist_var_bind_same_eq...  
    + auto_apply; auto. destruct_a_wf_wl. unify_binds. apply a_wf_wl_wf_bind_typ in H...
    + destruct_a_wf_wl... apply rename_var_in_aworklist_var_bind_same_neq...  
    + auto_apply; auto. destruct_a_wf_wl. unify_binds. apply a_wf_wl_wf_bind_typ in H...
  - destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__inf_tabs...
    intros. inst_cofinites_with X.
    rewrite subst_var_in_exp_open_exp_wrt_typ in *...
    rewrite open_body_wrt_typ_anno in *.
    auto_apply...
    dependent destruction H0. dependent destruction H.
    repeat (constructor; simpl; auto).
    + inst_cofinites_for a_wf_typ__all; intros.
      * apply s_in_rename with (Y:=X0) in H0...
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H0...
      * apply a_wf_typ_rename_tvar_cons with (Y:=X0) in H1...
        rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H1...
  - destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros.
    destruct_eq_atom.
    inst_cofinites_with x0. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *; auto; simpl in *.
    destruct_eq_atom.
    auto_apply; auto.
    repeat (constructor; simpl; auto)...
    apply a_wf_exp_weaken_etvar_twice with (T:=T)...
    apply a_wf_conts_weaken_cons...  apply a_wf_conts_weaken_cons...
  - destruct_a_wf_wl. dependent destruction H. simpl in *.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X.
    auto_apply; auto.
    repeat (constructor; simpl; auto).
    apply a_wf_typ_tvar_etvar_cons...
    apply a_wf_contd_weaken_cons...
  -  destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__infabs_etvar; auto.
    + apply rename_var_in_aworklist_tvar_bind_same...
    + intros. apply worklist_subst_rename_var with (x:=x') (x':=x) in H9 as Hws...
      * simpl in Hws. destruct_eq_atom.
        rewrite rename_var_in_aworklist_rev_eq in Hws...
        rewrite rename_var_in_contd_rev_eq in Hws...
        apply H6 in Hws as Hawlred; simpl; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev...
        -- destruct_a_wf_wl. 
           apply aworklist_subst_wf_wl with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto.
           repeat (constructor; simpl; auto).
           apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * replace (work_infabs (typ_arrow ` X1 ` X2) (subst_var_in_contd (exp_var_f x') x cd) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ rename_var_in_aworklist x' x Γ) with 
                 (rename_var_in_aworklist x' x (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by (simpl; destruct_eq_atom; auto).
        apply a_wf_wl_rename_var...
        repeat (constructor; simpl; auto). 
        apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
      * solve_notin_rename_var. 
  - destruct_a_wf_wl. 
    eapply a_wl_red__inftapp_all.
    auto_apply; auto.
    repeat (constructor; simpl; auto).
    apply a_wf_typ_all_open...
  - simpl in *.
    eapply apply_conts_rename_var with (x':=x') (x:=x) in H2 as Hac.
    econstructor; eauto.
    auto_apply...
    eapply a_wf_wl_apply_conts; eauto.
  - simpl in *.
    eapply apply_contd_rename_var with (x':=x') (x:=x) in H2 as Hac.
    econstructor; eauto.
    auto_apply...
    eapply a_wf_wl_apply_contd; eauto.
Qed.
