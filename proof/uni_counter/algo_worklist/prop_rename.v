Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Lia.


Require Import uni_counter.notations.
Require Import uni_counter.prop_basic.
Require Import uni_counter.decl_worklist.prop_equiv.
Require Import uni_counter.algo_worklist.def_extra.
Require Import uni_counter.algo_worklist.prop_basic.
Require Import uni_counter.ltac_utils.


Open Scope aworklist_scope.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.
#[local] Hint Rewrite dom_app dom_cons : core.


Fixpoint rename_tvar_in_aworklist (Y X:typvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ' X' b) => 
    match b with 
    | abind_var_typ A => aworklist_cons_var (rename_tvar_in_aworklist Y X Γ') X' (subst_typ_in_abind (`Y ) X b)
    | _ => aworklist_cons_var (rename_tvar_in_aworklist Y X Γ') (if X' == X then Y else X') b
    end
  | (aworklist_cons_work Γ' w) => aworklist_cons_work (rename_tvar_in_aworklist Y X Γ') (subst_typ_in_work (` Y) X w)
end.

Fixpoint rename_var_in_aworklist (y x:expvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_cons_var Γ' x' b) => 
    match b with 
    | abind_var_typ _ => aworklist_cons_var (rename_var_in_aworklist y x Γ') (if x' == x then y else x') b
    | _ => aworklist_cons_var (rename_var_in_aworklist y x Γ') x' b
    end
  | (aworklist_cons_work Γ' w) => aworklist_cons_work (rename_var_in_aworklist y x Γ') (subst_exp_in_work (exp_var_f y) x w)
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


Lemma rename_tvar_in_aworklist_var_bind_same : forall Γ x X Y A,
  ⊢ᵃʷ Γ ->
  Y ∉ ftvar_in_aworklist' Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ ->
  x ~ {` Y ᵗ/ₜ X} A ∈ᵃ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - destruct ab; simpl; 
      dependent destruction H; destruct_eq_atom; destruct_binds; auto.
  - destruct_eq_atom; dependent destruction H; auto.
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
  ftvar_in_exp e [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros. dependent induction H; try solve [simpl; fsetdec].
  - inst_cofinites_by (L `union` dom (⌊ Γ ⌋ᵃ) `union` ftvar_in_exp e).
    assert (ftvar_in_exp e [<=] ftvar_in_exp (e ᵉ^^ₑ exp_var_f x)) by apply ftvar_in_exp_open_exp_wrt_exp_lower.
    assert (x ~ abind_var_typ T ++ awl_to_aenv Γ = awl_to_aenv (x ~ᵃ T ;ᵃ Γ)) by (simpl; auto).
    eapply H1 in H3.
    simpl in *.
    fsetdec.
  - simpl.
    rewrite IHa_wf_exp1; eauto.
    rewrite IHa_wf_exp2; eauto.
    fsetdec.
  - pick fresh X. inst_cofinites_with X.
    replace (X ~ abind_tvar_empty ++ awl_to_aenv Γ) with (awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) in H0 by auto.
    simpl.
    assert (ftvar_in_exp e [<=] ftvar_in_exp (open_exp_wrt_typ e ` X)) by 
      apply ftvar_in_exp_open_exp_wrt_typ_lower.
    assert (ftvar_in_typ A [<=] ftvar_in_typ (open_typ_wrt_typ A ` X)) by 
      apply ftvar_in_typ_open_typ_wrt_typ_lower.
    specialize (H1 (X ~ᵃ □ ;ᵃ Γ) (eq_refl _)).
    simpl in *. fsetdec.
  - simpl. rewrite IHa_wf_exp; eauto.
    rewrite ftvar_in_a_wf_typ_upper; eauto.
    fsetdec.
  - simpl. rewrite IHa_wf_exp; eauto.
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

(* -- *)


(* #[local] Hint Rewrite ftvar_in_aworklist'_awl_cons_tvar ftvar_in_aworklist'_awl_app : core. *)

Lemma rename_tvar_in_typ_rev_eq : forall X Y A,
  Y ∉ ftvar_in_typ A ->
  {` X ᵗ/ₜ Y} {` Y ᵗ/ₜ X} A = A.
Proof.
  intros. induction A; simpl in *; auto;
    try rewrite IHA; try rewrite IHA1; try rewrite IHA2; auto.
  - destruct_eq_atom; simpl; destruct_eq_atom; auto.
Qed.

Lemma rename_tvar_in_exp_rev_eq : forall X Y e,
  Y ∉ ftvar_in_exp e ->
  {` X ᵉ/ₜ Y} {` Y ᵉ/ₜ X} e = e.
Proof.
  intros. induction e; simpl in *; auto;
    try rewrite IHe; try rewrite IHe1; try rewrite IHe2; auto.
  - rewrite rename_tvar_in_typ_rev_eq; auto.
  - rewrite rename_tvar_in_typ_rev_eq; auto.
Qed.

Lemma rename_tvar_in_conts_rev_eq : forall X Y cs,
  Y ∉ ftvar_in_conts cs ->
  {` X ᶜˢ/ₜ Y} {` Y ᶜˢ/ₜ X} cs = cs
with rename_tvar_in_contd_rev_eq : forall X Y cd,
  Y ∉ ftvar_in_contd cd ->
  {` X ᶜᵈ/ₜ Y} {` Y ᶜᵈ/ₜ X} cd = cd.
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

Lemma rename_tvar_in_work_rev_eq : forall X Y w,
  Y ∉ ftvar_in_work w ->
  {` X ʷ/ₜ Y} {` Y ʷ/ₜ X} w = w.
Proof.
  destruct w; intros; simpl in *;
    try repeat rewrite rename_tvar_in_typ_rev_eq; auto;
    try rewrite rename_tvar_in_exp_rev_eq; auto;
    try rewrite rename_tvar_in_conts_rev_eq; auto;
    try rewrite rename_tvar_in_contd_rev_eq; auto.
Qed.

Lemma rename_tvar_in_aworklist_rev_eq : forall X Y Γ,
  Y ∉ ftvar_in_aworklist' Γ ->
  {X ᵃʷ/ₜᵥ Y} {Y ᵃʷ/ₜᵥ X} Γ = Γ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - simpl. destruct ab; simpl; rewrite IHΓ; destruct_eq_atom; auto.
    rewrite rename_tvar_in_typ_rev_eq; auto.
  - rewrite IHΓ; auto. rewrite rename_tvar_in_work_rev_eq; auto.
Qed.

Lemma subst_typ_in_typ_rename_tvar : forall X Y A B,
  Y ∉ ftvar_in_typ A ->
  {` Y ᵗ/ₜ X} {B ᵗ/ₜ X} A = {({` Y ᵗ/ₜ X} B) ᵗ/ₜ Y} {` Y ᵗ/ₜ X} A.
Proof.
  intros. induction A; simpl; auto; try simpl in *;
    try rewrite IHA; auto;
    try rewrite IHA1; auto;
    try rewrite IHA2; auto.
  - destruct_eq_atom; simpl; destruct_eq_atom; simpl; auto.
Qed.


Lemma subst_typ_in_exp_rename_tvar : forall X Y e A,
  Y ∉ ftvar_in_exp e ->
  {` Y ᵉ/ₜ X} {A ᵉ/ₜ X} e = {({` Y ᵗ/ₜ X} A) ᵉ/ₜ Y} {` Y ᵉ/ₜ X} e.
Proof.
  - intros. induction e; simpl in *; auto.
    + rewrite IHe; auto.
    + rewrite IHe1; auto.
      rewrite IHe2; auto.
    + rewrite IHe; auto.
    + rewrite IHe; auto.
      rewrite subst_typ_in_typ_rename_tvar; auto.
    + rewrite IHe; auto.
      rewrite subst_typ_in_typ_rename_tvar; auto.
Qed.


Lemma subst_typ_in_conts_rename : forall X Y A cs,
  Y ∉ ftvar_in_conts cs ->
  {` Y ᶜˢ/ₜ X} {A ᶜˢ/ₜ X} cs = {({` Y ᵗ/ₜ X} A) ᶜˢ/ₜ Y} {` Y ᶜˢ/ₜ X} cs
with subst_typ_in_contd_rename : forall X Y A cd,
  Y ∉ ftvar_in_contd cd ->
  {` Y ᶜᵈ/ₜ X} {A ᶜᵈ/ₜ X} cd = {({` Y ᵗ/ₜ X} A) ᶜᵈ/ₜ Y} {` Y ᶜᵈ/ₜ X} cd.
Proof.
  - intros. induction cs; simpl in *;
      try repeat rewrite subst_typ_in_typ_rename_tvar; auto;
      try rewrite subst_typ_in_exp_rename_tvar; auto;
      try rewrite IHcs; auto;
      try rewrite subst_typ_in_contd_rename; auto.
  - intros. induction cd; simpl in *;
      try repeat rewrite subst_typ_in_typ_rename_tvar; auto;
      try rewrite subst_typ_in_exp_rename_tvar; auto;
      try rewrite IHcd; auto;
      try rewrite subst_typ_in_conts_rename; auto.
Qed.


Lemma subst_typ_in_work_rename : forall X Y w A,
  Y ∉ ftvar_in_work w ->
  {` Y ʷ/ₜ X} {A ʷ/ₜ X} w = {({` Y ᵗ/ₜ X} A) ʷ/ₜ Y} {` Y ʷ/ₜ X} w.
Proof.
  intros. destruct w; simpl in *;
    try repeat rewrite subst_typ_in_typ_rename_tvar; auto;
    try rewrite subst_typ_in_exp_rename_tvar; auto;
    try rewrite subst_typ_in_conts_rename; auto;
    try rewrite subst_typ_in_contd_rename; auto.
Qed.


Lemma subst_typ_in_awl_rename_eq_tvar : forall Γ X Y A,
  Y ∉ ftvar_in_aworklist' Γ ->
  {Y ᵃʷ/ₜᵥ X} {A ᵃʷ/ₜ X} Γ = {({` Y ᵗ/ₜ X} A) ᵃʷ/ₜ Y} {Y ᵃʷ/ₜᵥ X} Γ.
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - destruct ab; simpl; auto.
    + simpl. rewrite subst_typ_in_typ_rename_tvar; auto.
  - destruct ab; simpl; auto.
  - apply f_equal.
    + rewrite subst_typ_in_work_rename; auto.
Qed.

Lemma subst_typ_in_awl_rename_neq_tvar : forall Γ X1 X2 Y A,
  Y <> X2 ->
  X1 <> X2 ->
  {Y ᵃʷ/ₜᵥ X1} {A ᵃʷ/ₜ X2} Γ = {({` Y ᵗ/ₜ X1} A) ᵃʷ/ₜ X2} {Y ᵃʷ/ₜᵥ X1} Γ.
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - destruct ab; simpl; destruct_eq_atom; auto.   
      rewrite subst_typ_in_typ_subst_typ_in_typ; auto.
  - apply f_equal. rewrite subst_typ_in_work_subst_typ_in_work; auto.
Qed.

Lemma aworklist_subst_ftavr_in_aworklist : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' ({A ᵃʷ/ₜ X} Γ2 ⧺ Γ1) [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - rewrite ftvar_in_typ_subst_typ_in_typ_upper; fsetdec.
  - rewrite ftvar_in_work_subst_typ_in_work_upper; fsetdec.
  - rewrite_ftvar_in_aworklist. fsetdec. 
Qed.

Lemma aworklist_subst_ftavr_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ1 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof with auto.
  intros. induction H; simpl; try fsetdec...
  - rewrite_ftvar_in_aworklist. fsetdec. 
Qed.

Lemma aworklist_subst_ftavr_in_aworklist_2 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ2 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof with auto.
  intros. induction H; simpl; try fsetdec.
  - rewrite_ftvar_in_aworklist. fsetdec. 
Qed.

Ltac rewrite_aworklist_rename_tvar' :=
  repeat
    match goal with
    | H : context [rename_tvar_in_aworklist _ _ (awl_app _ _)] |- _ =>
      progress (repeat rewrite <- rename_tvar_in_aworklist_app in H); simpl in H; repeat (case_if in H; [ ])
    | |- context [rename_tvar_in_aworklist _ _ (awl_app _ _)] =>
      repeat rewrite <- rename_tvar_in_aworklist_app; simpl; repeat (case_if; [ ])
    end; auto.

Ltac rewrite_aworklist_rename_subst :=
  match goal with
  | H : context [rename_tvar_in_aworklist _ ?X (subst_typ_in_aworklist ?A ?X _)] |- _ =>
    rewrite subst_typ_in_awl_rename_eq_tvar in H; try solve
      [rewrite aworklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
  | H : context [rename_tvar_in_aworklist _ ?X (subst_typ_in_aworklist _ ?X0 _)] |- _ =>
    rewrite subst_typ_in_awl_rename_neq_tvar in H; auto
  end.


Lemma notin_rename_tvar_in_aworklist : forall X Y Γ,
  X <> Y ->
  X ∉ ftvar_in_aworklist' ({Y ᵃʷ/ₜᵥ X} Γ).
Proof.
  induction Γ; intros; simpl in *; auto.
  - simpl; destruct ab; simpl in *; destruct_eq_atom; auto.
    rewrite ftvar_in_typ_subst_typ_in_typ_upper; simpl; auto.
  - rewrite ftvar_in_work_subst_typ_in_work_upper; simpl; auto.
Qed.


Ltac solve_notin_rename_tvar' :=
  match goal with
  | H : _ |- context [?e1 ᵉ^^ₑ ?e2] => rewrite ftvar_in_exp_open_exp_wrt_exp_upper
  | H : _ |- context [rename_tvar_in_aworklist ?Y ?X ?Γ] =>
    (* assert True *)
    match goal with
    | H1 : X ∉ ftvar_in_aworklist' (rename_tvar_in_aworklist Y X Γ) |- _ => fail 1
    | _ =>
      assert (X ∉ ftvar_in_aworklist' (rename_tvar_in_aworklist Y X Γ)) by now apply notin_rename_tvar_in_aworklist
    end
  | H : _ |- context [subst_typ_in_conts ?Y ?X ?c] =>
    match goal with
    | H1 : (X ∉ (ftvar_in_conts (subst_typ_in_conts Y X c))) |- _ => fail 1
    | _ =>
      assert (X ∉ (ftvar_in_conts (subst_typ_in_conts Y X c))) by (simpl; apply subst_typ_in_conts_fresh_same; auto)
    end
  | H : _ |- context [subst_typ_in_contd ?Y ?X ?c] =>
    match goal with
    | H1 : (X ∉ (ftvar_in_contd (subst_typ_in_contd Y X c))) |- _ => fail 1
    | _ =>
      assert (X ∉ (ftvar_in_contd (subst_typ_in_contd Y X c))) by (simpl; apply subst_typ_in_contd_fresh_same; auto)
    end
  | H : _ |- context [subst_typ_in_exp ?Y ?X ?e] =>
    match goal with
    | H1 : (X ∉ (ftvar_in_exp (subst_typ_in_exp Y X e))) |- _ => fail 1
    | _ =>
      assert (X ∉ (ftvar_in_exp (subst_typ_in_exp Y X e))) by (simpl; apply subst_typ_in_exp_fresh_same; auto)
    end
  | H : _ |- context [subst_typ_in_typ ?Y ?X ?t] =>
    match goal with
    | H1 : (X ∉ (ftvar_in_typ (subst_typ_in_typ Y X t))) |- _ => fail 1
    | _ =>
      assert (X ∉ (ftvar_in_typ (subst_typ_in_typ Y X t))) by (simpl; apply subst_typ_in_typ_fresh_same; auto)
    end
  | H : aworklist_subst ?Γ ?Y ?A ?Γ1 ?Γ2 |- context [ftvar_in_aworklist' ?Γ2] =>
    rewrite (aworklist_subst_ftavr_in_aworklist_2 _ _ _ _ _ H); eauto
  | H : aworklist_subst ?Γ ?Y ?A ?Γ1 ?Γ2 |- context [ftvar_in_aworklist' ?Γ1] =>
    rewrite (aworklist_subst_ftavr_in_aworklist_1 _ _ _ _ _ H); eauto
  | H : _ |- _ => idtac
  end; auto.

Ltac solve_notin_rename_tvar := 
    repeat solve_notin_rename_tvar'.

Ltac preprocess_ftvar_aworklist_subst X :=
  match goal with 
  | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- _ =>
    match goal with 
    | H_1 : X ∉ ftvar_in_aworklist' Γ |- _ => fail 1
    | _ : _ |- _ => assert (X ∉ ftvar_in_aworklist' Γ) by (auto; solve_notin_rename_tvar)
    end;
    match goal with 
    | H_1 :  (X ∉ ftvar_in_typ A) |- _ => fail 1
    | _ : _ |- _ => assert (X ∉ ftvar_in_typ A) by (auto; solve_notin_rename_tvar)
    end
  end.
    

Ltac rewrite_aworklist_rename_rev' :=
  lazymatch goal with
  | H : context [rename_tvar_in_aworklist _ _ (rename_tvar_in_aworklist ?X' ?X ?Γ)] |- _ =>
    try preprocess_ftvar_aworklist_subst X';
    let H1 := fresh "H" in
    assert (H1: X' ∉ ftvar_in_aworklist' Γ) by (auto; solve_notin_rename_tvar);
    rewrite rename_tvar_in_aworklist_rev_eq in H; auto
  end.

Ltac rewrite_aworklist_rename_rev :=
  repeat rewrite_aworklist_rename_rev'.


Ltac rewrite_aworklist_rename_subst' :=
  match goal with
  | H : context [rename_tvar_in_aworklist _ ?X (subst_typ_in_aworklist ?A ?X _)] |- _ =>
    rewrite subst_typ_in_awl_rename_eq_tvar in H; try solve [apply notin_rename_tvar_in_aworklist; auto]; try solve
      [rewrite aworklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
  | H : context [rename_tvar_in_aworklist _ ?X (subst_typ_in_aworklist _ ?X0 _)] |- _ =>
    rewrite subst_typ_in_awl_rename_neq_tvar in H; auto
  end.

Ltac rewrite_aworklist_rename :=
  rewrite_aworklist_rename_tvar';
  rewrite_aworklist_rename_subst'.

(* - *)

Lemma rename_tvar_in_aworklist_fresh_eq : forall X Y Γ,
  X ∉ ftvar_in_aworklist' Γ ->
  {Y ᵃʷ/ₜᵥ X} Γ = Γ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - rewrite IHΓ;
    destruct ab; destruct_eq_atom; simpl; auto.
    rewrite subst_typ_in_typ_fresh_eq; auto.
  - rewrite IHΓ; auto.
    rewrite subst_typ_in_work_fresh_eq; auto.
Qed.


Lemma ftvar_in_typ_rename : forall A X Y,
   X `in` ftvar_in_typ A -> Y `in` ftvar_in_typ ({`Y ᵗ/ₜ X} A).
Proof.
  intros. induction A; simpl in *; auto; try fsetdec.
  - simpl in *. apply singleton_iff in H. subst.
    destruct_eq_atom. simpl. fsetdec.
Qed.

Ltac solve_a_wf_wl Γ :=
  lazymatch goal with 
  | H : ⊢ᵃʷ Γ |- _ => idtac
  | _ : _ |- _ =>   
    destruct_a_wf_wl; 
    let H1 := fresh "H" in
    assert (H1 : ⊢ᵃʷ Γ) by eauto 7
  end.


Ltac apply_IH_a_wf_wwl :=
  match goal with 
  | H : (⊢ᵃʷ ?Γ) -> ?P |- _ => 
    solve_a_wf_wl Γ
  end;
  match goal with
  | H : (⊢ᵃʷ ?Γ) -> ?P, H1 : ⊢ᵃʷ ?Γ |- _ => 
    let Hdred := fresh "IHared" in
    apply H in H1 as Hdred
  end.


Lemma rename_tvar_aworklist_subst : forall Γ X1 X2 Y A Γ1 Γ2,
  Y ∉ ftvar_in_typ A `union` ftvar_in_aworklist' Γ `union` singleton X2 ->
  aworklist_subst Γ X2 A Γ1 Γ2 ->
  aworklist_subst (rename_tvar_in_aworklist Y X1 Γ) (if X2 == X1 then Y else X2)
    ({` Y ᵗ/ₜ X1} A) ({Y ᵃʷ/ₜᵥ X1} Γ1) ({Y ᵃʷ/ₜᵥ X1} Γ2).
Proof with auto.
  intros. induction H0; try solve [simpl; eauto].
  - simpl in *. destruct (X == X1).
    + subst.
      constructor...
    + constructor...
  - simpl in *.
    destruct_eq_atom.
    + constructor... rewrite ftvar_in_typ_subst_typ_in_typ_upper...
    + constructor... rewrite subst_typ_in_typ_fresh_eq...
    + constructor... rewrite ftvar_in_typ_subst_typ_in_typ_upper...
  - simpl in *.
    destruct_eq_atom.
    + constructor... rewrite ftvar_in_typ_subst_typ_in_typ_upper...
    + constructor... rewrite subst_typ_in_typ_fresh_eq...
    + constructor... rewrite ftvar_in_typ_subst_typ_in_typ_upper...
  - simpl in *. destruct_eq_atom... 
  - simpl in *. destruct_eq_atom.
    + constructor... rewrite ftvar_in_typ_subst_typ_in_typ_upper...
    + constructor... rewrite subst_typ_in_typ_fresh_eq...
    + constructor... rewrite ftvar_in_typ_subst_typ_in_typ_upper...
  - simpl in *.
    destruct_eq_atom; rewrite_aworklist_rename_tvar';
    apply a_ws1__etvar_move; try (rewrite_ftvar_in_aworklist; auto).
    + rewrite <- ftvar_in_typ_subst_typ_in_typ_lower...
    + apply ftvar_in_typ_rename...
    + rewrite <- ftvar_in_typ_subst_typ_in_typ_lower...
Qed.


Ltac create_ftvar_in_awl_set :=
  match goal with 
  | H1 : ⊢ᵃʷ ?Γ , H2 : ?X ∉ dom (⌊ ?Γ ⌋ᵃ) |- _ =>
    let Hfv := fresh "Hfv" in
    assert (Hfv: X ∉ ftvar_in_aworklist' Γ) by (rewrite ftvar_in_a_wf_wwl_upper; auto)
  end.

Lemma rename_tvar_in_aworklist_a_mono_typ : forall Γ X Y A,
  ⊢ᵃʷ Γ ->
  Y ∉ ftvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ ᵗ⊢ᵃₘ {` Y ᵗ/ₜ X} A.
Proof.
  intros.
  dependent induction H1; simpl in *; destruct_eq_atom; auto.
  - constructor; auto.
    apply rename_tvar_in_aworklist_eq_tvar_bind_same; eauto.
  - constructor; auto.
    apply rename_tvar_in_aworklist_neq_tvar_bind_same; eauto.
  - apply a_mono_typ__etvar.
    apply rename_tvar_in_aworklist_eq_tvar_bind_same; eauto. 
  - apply a_mono_typ__etvar.
    apply rename_tvar_in_aworklist_neq_tvar_bind_same; eauto.
Qed.



Lemma rename_tvar_in_aworklist_dom_upper : forall Γ X Y,
  dom (⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) [<=] union (dom (⌊ Γ ⌋ᵃ)) (singleton Y).
Proof.
  intros. induction Γ; simpl; try fsetdec.
  destruct ab; simpl; destruct_eq_atom; simpl; fsetdec. 
Qed.


Lemma rename_tvar_in_aworklist_a_wf_typ : forall Γ X Y A,
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ) ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ ᵗ⊢ᵃ {` Y ᵗ/ₜ X} A.
Proof.
  intros. dependent induction H1; simpl in *; eauto; destruct_eq_atom; eauto.
  - constructor; auto.
    apply rename_tvar_in_aworklist_eq_tvar_bind_same; eauto.
    rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - constructor; auto.
    apply rename_tvar_in_aworklist_neq_tvar_bind_same; eauto.
    rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - apply a_wf_typ__stvar.
    apply rename_tvar_in_aworklist_eq_tvar_bind_same; eauto.
    rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - apply a_wf_typ__stvar.
    apply rename_tvar_in_aworklist_neq_tvar_bind_same; eauto.
    rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - apply a_wf_typ__etvar.
    apply rename_tvar_in_aworklist_eq_tvar_bind_same; eauto.
    rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - apply a_wf_typ__etvar.
    apply rename_tvar_in_aworklist_neq_tvar_bind_same; eauto.
    rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
      apply s_in_subst_inv; auto.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
      replace (X0 ~ □ ++ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) with (⌊ {Y ᵃʷ/ₜᵥ X} (X0 ~ᵃ □ ;ᵃ Γ) ⌋ᵃ).
      apply H1; eauto.
      simpl. destruct_eq_atom. auto.
Qed.


Lemma rename_tvar_in_aworklist_var_bind_subst : forall x A X Y Γ,
  ⊢ᵃʷ Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ ->
  x ~ {` Y ᵗ/ₜ X} A ∈ᵃ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ.
Proof with auto.
  intros. induction Γ.
  - simpl in *. inversion H0.
  - destruct_a_wf_wl; try destruct ab; destruct_binds; destruct_eq_atom; auto.
  - destruct_a_wf_wl...
Qed.


Lemma rename_tvar_in_aworklist_a_wf_exp : forall Γ X Y e,
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ)  ->
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ ᵉ⊢ᵃ {` Y ᵉ/ₜ X} e.
Proof with eauto using rename_tvar_in_aworklist_a_wf_typ.
  intros. dependent induction H1; simpl in *; auto...
  - eapply rename_tvar_in_aworklist_var_bind_subst with (Y:=Y) (X:=X) in H1...
  - inst_cofinites_for a_wf_exp__abs T:=({`Y ᵗ/ₜ X} T)...
    intros. inst_cofinites_with x.
    replace (x ~ abind_var_typ ({` Y ᵗ/ₜ X} T) ++ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) with (⌊ {Y ᵃʷ/ₜᵥ X} (x ~ᵃ T;ᵃ Γ) ⌋ᵃ).
    replace (({` Y ᵉ/ₜ X} e) ᵉ^^ₑ exp_var_f x) with ({` Y ᵉ/ₜ X} e ᵉ^^ₑ exp_var_f x).
    apply H1...
    rewrite subst_typ_in_exp_open_exp_wrt_exp...
    simpl. destruct_eq_atom...
  - inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X0...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto. 
      apply s_in_subst_inv...
    + rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2; auto.
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
      replace (X0 ~ □ ++ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) with (⌊ {Y ᵃʷ/ₜᵥ X} (X0 ~ᵃ □;ᵃ Γ) ⌋ᵃ).
      eapply H1; eauto.
      simpl. destruct_eq_atom. auto.
Qed.


#[local] Hint Immediate  a_wf_exp_weaken_etvar_twice : core.


Lemma rename_tvar_in_aworklist_a_wf_conts : forall Γ X Y cs,
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ)  ->
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ cs ->
  ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ ᶜˢ⊢ᵃ {` Y ᶜˢ/ₜ X} cs
with rename_tvar_in_aworklist_a_wf_contd : forall Γ X Y cd,
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ)  ->
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cd ->
  ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ ᶜᵈ⊢ᵃ {` Y ᶜᵈ/ₜ X} cd.
Proof with auto using rename_tvar_in_aworklist_a_wf_typ, rename_tvar_in_aworklist_a_wf_exp.
  - intros. clear rename_tvar_in_aworklist_a_wf_conts. dependent induction H1; simpl in *; auto...
  - intros. clear rename_tvar_in_aworklist_a_wf_contd. dependent induction H1; try repeat destruct_wf_arrow; simpl in *; auto...
Qed.


Lemma rename_tvar_in_aworklist_a_wf_work : forall Γ X Y w,
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ)  ->
  ⌊ Γ ⌋ᵃ ʷ⊢ᵃ w ->
  ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ ʷ⊢ᵃ {` Y ʷ/ₜ X} w.
Proof with auto 8 using rename_tvar_in_aworklist_a_wf_typ, rename_tvar_in_aworklist_a_wf_exp, rename_tvar_in_aworklist_a_wf_conts, rename_tvar_in_aworklist_a_wf_contd.
  intros. dependent destruction H1; try repeat destruct_wf_arrow; simpl... 
Qed.
  

Lemma num_occurs_in_typ_rename : forall A X X0 Y n,
  num_occurs_in_typ X A n ->
  X <> Y ->
  X0 <> X ->
  num_occurs_in_typ X ({`X0 ᵗ/ₜ Y} A) n.
Proof with eauto 6 using num_occurs_in_typ.
  intros. induction H; simpl; destruct_eq_atom; eauto...
  - inst_cofinites_for num_occurs_in_typ__all. intros. inst_cofinites_with Y0. 
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
  - econstructor...
  - econstructor...
Qed.


Lemma a_iuv_size_rename_tvar : forall Γ X Y A m, 
  ⊢ᵃʷ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  Y `notin` dom (⌊ Γ ⌋ᵃ) ->
  a_iuv_size (⌊ Γ ⌋ᵃ) A m ->
  a_iuv_size (⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) ({` Y ᵗ/ₜ X} A) m.
Proof with eauto using a_iuv_size.
  intros. dependent induction H2; simpl...
  (* TODO: may improve this duplicated fragment later *)
  - destruct_eq_atom; eauto...
    + dependent destruction H0; 
      eapply rename_tvar_in_aworklist_eq_tvar_bind_same with (X':=Y) in H0; eauto using a_iuv_size; 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
    + dependent destruction H0;
      eapply rename_tvar_in_aworklist_neq_tvar_bind_same with (X1:=X0) (X2:=X) in H0; eauto using a_iuv_size; 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - destruct_eq_atom; eauto...
    + dependent destruction H0; 
      eapply rename_tvar_in_aworklist_eq_tvar_bind_same with (X':=Y) in H0; eauto using a_iuv_size; 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
    + dependent destruction H0;
      eapply rename_tvar_in_aworklist_neq_tvar_bind_same with (X1:=X0) (X2:=X) in H0; eauto using a_iuv_size; 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - destruct_eq_atom; eauto...
    + dependent destruction H0; 
      eapply rename_tvar_in_aworklist_eq_tvar_bind_same with (X':=Y) in H0; eauto using a_iuv_size; 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
    + dependent destruction H0;
      eapply rename_tvar_in_aworklist_neq_tvar_bind_same with (X1:=X0) (X2:=X) in H0; eauto using a_iuv_size; 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - dependent destruction H0...
  - inst_cofinites_for a_iuv_size__all; intros;
    inst_cofinites_with X0.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      replace (X0 ~ □ ++ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) with (⌊ {Y ᵃʷ/ₜᵥ X} (X0 ~ᵃ □ ;ᵃ Γ) ⌋ᵃ) by (simpl; destruct_eq_atom; auto)...
      eapply H3; eauto.
      dependent destruction H0. pick fresh X1. inst_cofinites_with X1.
      eapply a_wf_typ_rename_tvar_cons with (Y:=X0) in H1. 
      rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H1...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply num_occurs_in_typ_rename...
  - dependent destruction H0...
    econstructor...
  - dependent destruction H0...
    econstructor...
Qed.


Lemma a_exp_split_size_rename_tvar : forall Γ X Y e n,
  ⊢ᵃʷ Γ ->
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  Y `notin` dom (⌊ Γ ⌋ᵃ) ->
  a_exp_split_size (⌊ Γ ⌋ᵃ) e n ->
  a_exp_split_size (⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) ({` Y ᵉ/ₜ X} e) n.
Proof with eauto using a_exp_split_size, a_iuv_size_rename_tvar.
  intros. dependent induction H2; simpl in *...
  - eapply rename_tvar_in_aworklist_var_bind_same with (X:=X) (Y:=Y) in H3 as Hbind; eauto.
    replace (exp_var_f x) with ( {`Y ᵉ/ₜ X} (exp_var_f x)) by auto.
    eapply a_iuv_size_rename_tvar in H2...
    + eapply a_wf_env_bind_a_wf_typ; eauto. apply a_wf_wwl_a_wf_env...
    + rewrite ftvar_in_a_wf_wwl_upper; eauto.
  - dependent destruction H0. 
    inst_cofinites_for a_exp_split_size__abs; intros.
    inst_cofinites_with x.
    rewrite subst_typ_in_exp_open_exp_wrt_exp_fresh2...
    rewrite_env ((⌊ {Y ᵃʷ/ₜᵥ X} (x ~ᵃ typ_bot ;ᵃ Γ) ⌋ᵃ))...
    eapply H2; eauto.
    simpl. eapply a_wf_exp_var_binds_another_cons...
  - dependent destruction H0. econstructor...
  - dependent destruction H0. inst_cofinites_for a_exp_split_size__tabs; intros.
    + inst_cofinites_with X0. dependent destruction H1.
      rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2...
      replace (X0 ~ □ ++ ⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) with (⌊ {Y ᵃʷ/ₜᵥ X} (X0 ~ᵃ □ ;ᵃ Γ) ⌋ᵃ) by (simpl; destruct_eq_atom; auto)...
    + replace (typ_all ({` Y ᵗ/ₜ X} A)) with ({` Y ᵗ/ₜ X} (typ_all A)) by auto.
      eapply a_iuv_size_rename_tvar; eauto.
      inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
      dependent destruction H1...
  - dependent destruction H0... econstructor...
  - dependent destruction H0... econstructor...
Qed.
  

Lemma rename_tvar_in_aworklist_a_wf_wwl : forall Γ X Y,
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ) ->
  ⊢ᵃʷ {Y ᵃʷ/ₜᵥ X} Γ.
Proof with eauto.
  intros. induction H; try solve [simpl in *; eauto].
  - simpl in *.  destruct_binds.
    + econstructor; auto.
      rewrite rename_tvar_in_aworklist_dom_upper. fsetdec.
      apply rename_tvar_in_aworklist_a_wf_typ...
  - simpl in *. destruct_binds; destruct_eq_atom...
    + constructor... rewrite rename_tvar_in_aworklist_fresh_eq; auto. 
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
    + constructor... rewrite rename_tvar_in_aworklist_dom_upper; auto.
  - simpl in *. destruct_binds; destruct_eq_atom...
    + constructor... rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
    + constructor... rewrite rename_tvar_in_aworklist_dom_upper; auto.
  - simpl in *. destruct_binds; destruct_eq_atom...
    + constructor... rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite ftvar_in_a_wf_wwl_upper; eauto.
    + constructor... rewrite rename_tvar_in_aworklist_dom_upper; auto.
  - simpl in *. constructor; auto.
    apply rename_tvar_in_aworklist_a_wf_work...
Qed.


Lemma apply_conts_rename_tvar : forall cs A w X Y,
  apply_conts cs A w ->
  apply_conts ({`Y ᶜˢ/ₜ X} cs) ({`Y ᵗ/ₜ X} A) ({` Y ʷ/ₜ X} w).
Proof.
  intros. induction H; simpl; try solve [simpl; eauto].
Qed.

Lemma iu_size_rename_tvar : forall A X Y,
  iu_size A = iu_size ({`Y ᵗ/ₜ X} A).
Proof.
  intros. induction A; simpl; auto.
  destruct_eq_atom; auto.
Qed.

Lemma apply_contd_rename_tvar : forall cd A B w X Y,
  apply_contd cd A B w ->
  apply_contd ({`Y ᶜᵈ/ₜ X} cd) ({`Y ᵗ/ₜ X} A) ({`Y ᵗ/ₜ X} B) ({`Y ʷ/ₜ X} w).
Proof.
  intros. induction H; simpl; try solve [simpl; eauto].
  erewrite iu_size_rename_tvar in H; eauto.
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


Lemma a_mono_typ_false_rename : forall Γ X Y A,
  ⊢ᵃʷ Γ ->
  (a_mono_typ (⌊ Γ ⌋ᵃ) A -> False) ->
  Y ∉ ftvar_in_aworklist' Γ `union` ftvar_in_typ A `union` dom (⌊ Γ ⌋ᵃ) `union` singleton X ->
  a_mono_typ (⌊ {Y ᵃʷ/ₜᵥ X} Γ ⌋ᵃ) ({` Y ᵗ/ₜ X} A) -> False.
Proof with eauto.
  intros.
  apply rename_tvar_in_aworklist_a_mono_typ with (Y:=X) (X:=Y) in H2...
  - simpl in H2. rewrite rename_tvar_in_aworklist_rev_eq in H2...
    rewrite rename_tvar_in_typ_rev_eq in H2...  
  - apply rename_tvar_in_aworklist_a_wf_wwl...
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

(* Lemma iuv_size_rename_tvar : forall A X Y n,
  iuv_size A = iuv_size ({`Y ᵗ/ₜ X} A).
Proof.
  intros. induction A; simpl; auto.
  destruct_eq_atom; auto.
Qed. *)


Theorem rename_tvar_in_a_wf_wwl_a_wl_red : forall Γ X Y,
  X <> Y ->
  ⊢ᵃʷ Γ ->
  Y ∉ dom (⌊ Γ ⌋ᵃ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  {Y ᵃʷ/ₜᵥ X} Γ ⟶ᵃʷ⁎⋅.
Proof with eauto.
  intros. dependent induction H2; try solve [simpl in *; try apply_IH_a_wf_wwl; eauto]; create_ftvar_in_awl_set.
  - simpl in *. destruct (X0 == X); apply_IH_a_wf_wwl...
  - simpl.
    destruct_a_wf_wl. dependent destruction H0.
    inst_cofinites_for a_wl_red__sub_alll.
    + apply neq_all_rename...
    + apply neq_intersection_rename...
    + apply neq_union_rename...
    + intros. simpl in *. inst_cofinites_with X0.
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
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
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
    destruct_eq_atom.
    auto_apply.
    + repeat (constructor; simpl; auto).
      * apply a_wf_typ_tvar_stvar_cons...
      * apply a_wf_typ_tvar_stvar_cons...
    + repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    destruct (X0 == X);
    inst_cofinites_for a_wl_red__sub_arrow1...
    + subst. apply rename_tvar_in_aworklist_eq_tvar_bind_same; auto...
      destruct_a_wf_wl; auto.
    + destruct_a_wf_wl. 
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *. subst.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=Y) in H8 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        apply H5 in Hws as Hawlred; simpl; auto.
        -- clear Hws. simpl in *. 
           rewrite_aworklist_rename; simpl; eauto. simpl in *. destruct_eq_atom. auto.
           rewrite_aworklist_rename_rev.
        -- eapply aworklist_subst_wf_wwl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with 
            (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); eauto. 
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_neq_tvar_bind_same; auto...
      destruct_a_wf_wl; auto.
    + destruct_a_wf_wl.
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=X0) in H8 as Hws.
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
        -- eapply aworklist_subst_wf_wwl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub ` X0 (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * solve_notin_rename_tvar; auto.
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__sub_arrow2...
    + apply rename_tvar_in_aworklist_eq_tvar_bind_same; auto...
    + destruct_a_wf_wl. 
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *. subst.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=Y) in H9 as Hws.
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
        -- eapply aworklist_subst_wf_wwl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)... 
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_neq_tvar_bind_same; auto...
    + destruct_a_wf_wl. 
      fold_subst. apply a_mono_typ_false_rename; simpl; eauto.
    + intros. simpl in *.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=X0) in H9 as Hws.
      * simpl in Hws. destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H7 in Hws as Hawlred; simpl; auto.
        -- clear Hws. 
           rewrite_aworklist_rename; simpl; eauto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wwl in Hws; simpl; eauto 7.
           ++ destruct_a_wf_wl. repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub (typ_arrow A1 A2) ` X0 ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * solve_notin_rename_tvar; auto. 
  - simpl in *. destruct_a_wf_wl.
    eapply rename_tvar_aworklist_subst with (Y:=Y) (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
    apply a_wl_red__sub_etvarmono1 with (Γ1:={Y ᵃʷ/ₜᵥ X} Γ1) (Γ2:={Y ᵃʷ/ₜᵥ X} Γ2)...
    + apply rename_tvar_in_aworklist_eq_tvar_bind_same; eauto...
    + apply rename_tvar_in_aworklist_a_mono_typ...
    + rewrite subst_typ_in_typ_fresh_eq...
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply aworklist_subst_wf_wwl; eauto.
      rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
    + apply rename_tvar_in_aworklist_neq_tvar_bind_same... 
    + apply rename_tvar_in_aworklist_a_mono_typ...
    + rewrite ftvar_in_typ_subst_typ_in_typ_upper...
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply aworklist_subst_wf_wwl; eauto.
      * rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
  - simpl in *. destruct_a_wf_wl.
    eapply rename_tvar_aworklist_subst with (Y:=Y) (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
    apply a_wl_red__sub_etvarmono2 with (Γ1:={Y ᵃʷ/ₜᵥ X} Γ1) (Γ2:={Y ᵃʷ/ₜᵥ X} Γ2)...
    + apply rename_tvar_in_aworklist_eq_tvar_bind_same; auto...
    + apply rename_tvar_in_aworklist_a_mono_typ...
    + rewrite subst_typ_in_typ_fresh_eq...
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply aworklist_subst_wf_wwl; eauto.
      rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
    + apply rename_tvar_in_aworklist_neq_tvar_bind_same; auto...
    + apply rename_tvar_in_aworklist_a_mono_typ...
    + rewrite ftvar_in_typ_subst_typ_in_typ_upper... 
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply aworklist_subst_wf_wwl; eauto.
      * rewrite aworklist_subst_dom_upper with (Γ:=Γ)...
  - simpl in *. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x.
    rewrite subst_typ_in_exp_open_exp_wrt_exp in H5...
    auto_apply.
    + repeat (constructor; simpl; auto).
      -- apply a_wf_exp_var_binds_another_cons with (A1:=T)... 
      -- apply a_wf_typ_weaken_cons...
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *; destruct_a_wf_wl; destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__chk_absetvar. 
    + apply rename_tvar_in_aworklist_eq_tvar_bind_same; auto...
    + intros.
      inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=Y) in H11 as Hws.
      simpl in Hws. destruct_eq_atom.
      * rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        simpl in Hws.
        replace (exp_var_f x) with (subst_typ_in_exp (` Y) X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_typ_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        -- eapply H7 in Hws as Hawlred; simpl in *; auto.
           ++ assert (X ∉ (ftvar_in_exp (subst_typ_in_exp ` Y X e ᵉ^^ₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
              clear Hws. destruct_eq_atom.
              rewrite_aworklist_rename; simpl; auto.
              rewrite_aworklist_rename_rev. 
              simpl in Hawlred. destruct_eq_atom. auto.
           ++ eapply aworklist_subst_wf_wwl in Hws; simpl in *; eauto 9.  
              ** repeat (constructor; simpl; eauto). eapply a_wf_exp_weaken_etvar_twice with (T:=T)...
           ++ rewrite aworklist_subst_dom_upper with (Γ:=(work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))... 
        -- solve_notin_rename_tvar; auto.
      * simpl. solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_neq_tvar_bind_same; auto...
    + intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.  
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=X0) in H11 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        replace (exp_var_f x) with (subst_typ_in_exp (` Y) X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_typ_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        -- eapply H7 in Hws as Hawlred; simpl; auto.
           ++ assert (X ∉ (ftvar_in_exp (({` Y ᵉ/ₜ X} e) ᵉ^^ₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
              clear Hws. destruct_eq_atom.
              rewrite_aworklist_rename; simpl; auto.
              rewrite_aworklist_rename_rev.
              simpl in Hawlred. destruct_eq_atom. auto.
           ++ eapply aworklist_subst_wf_wwl in Hws; simpl; eauto 9.
              repeat (constructor; simpl; eauto).
           ++ rewrite aworklist_subst_dom_upper with (Γ:=(work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        -- rewrite ftvar_in_exp_open_exp_wrt_exp_upper; auto.
      * simpl; solve_notin_rename_tvar; auto.
  - simpl in *.
    destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x.
    rewrite subst_typ_in_exp_open_exp_wrt_exp in H6...
    apply H6.
    + repeat (constructor; simpl; auto).
      apply a_wf_exp_var_binds_another_cons with (A1:=T)...
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    dependent destruction H0.
    apply a_wf_wwl_a_wf_env in H1 as Hwfenv. apply a_wf_env_bind_a_wf_typ in H3 as Hwft...
    assert (⊢ᵃʷ (work_applys cs A ⫤ᵃ Γ)) by now destruct_a_wf_wl; eauto.
    eapply a_wl_red__inf_var with (A:=({` Y ᵗ/ₜ X} A))...
    apply rename_tvar_in_aworklist_var_bind_subst...
  - simpl in *.
    destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__inf_tabs...
    intros. inst_cofinites_with X0 (keep).
    rewrite subst_typ_in_exp_open_exp_wrt_typ in H8...
    simpl in H8.
    rewrite <- subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H8...
    destruct_eq_atom...
    auto_apply...
    + dependent destruction H5. 
      repeat (constructor; simpl; auto).
      inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X1; auto.
      * dependent destruction H10...
  - simpl in *. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_typ_in_exp_open_exp_wrt_exp in H6...
    auto_apply...
    + repeat (constructor; simpl; auto). auto...
      rewrite_env (nil ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ).
      apply a_wf_conts_weaken...
  - simpl in *. destruct_a_wf_wl.
    eapply a_exp_split_size_rename_tvar with (X:=X) (Y:=Y) in H4; eauto.
    econstructor; eauto.
    eapply IHa_wl_red; eauto.
  - simpl in *. destruct_a_wf_wl. dependent destruction H0.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X0.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
    destruct_eq_atom.
    auto_apply.
    + repeat (constructor; simpl; auto).
      * apply a_wf_typ_tvar_etvar_cons...
      * apply a_wf_contd_weaken_cons... 
    + auto. 
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst; inst_cofinites_for a_wl_red__infabs_etvar; auto.
    + apply rename_tvar_in_aworklist_eq_tvar_bind_same; auto...
    + intros.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=Y) in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_contd_rev_eq in Hws; auto.
        assert (X ∉ (ftvar_in_contd ({` Y ᶜᵈ/ₜ X} cd))) by (solve_notin_rename_tvar; auto).
        apply H6 in Hws as Hawlred; simpl; auto.
        -- clear Hws. destruct_eq_atom.
           rewrite_aworklist_rename; simpl; auto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wwl with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; eauto 8.
           repeat (constructor; simpl; auto). 
           apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))... 
      * simpl; solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_neq_tvar_bind_same; auto...
    + intros.
      apply rename_tvar_aworklist_subst with (Y:=X) (X1:=Y) (X2:=X0) in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_contd_rev_eq in Hws; auto.
        assert (X ∉ (ftvar_in_contd ({` Y ᶜᵈ/ₜ X} cd))) by now solve_notin_rename_tvar.
        apply H6 in Hws as Hawlred; simpl; auto.
        -- clear Hws. destruct_eq_atom. rewrite_aworklist_rename; simpl; auto.
           rewrite_aworklist_rename_rev.
           simpl in Hawlred. destruct_eq_atom. auto.
        -- eapply aworklist_subst_wf_wwl with (Γ:= (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ); simpl; eauto 8.
           repeat (constructor; simpl; auto). 
           apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))... 
      * simpl; solve_notin_rename_tvar; auto...
  - simpl in *. destruct_a_wf_wl.
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_typ_in_typ_open_typ_wrt_typ...
    auto_apply...
    + repeat (constructor; simpl; auto).
      eapply a_wf_typ_all_open...
  - simpl in *.
    eapply apply_conts_rename_tvar with (X:=X) (Y:=Y) in H2 as Hac...
    eapply a_wl_red__applys...
    auto_apply...
    eapply a_wf_wwl_apply_conts in H0...
  - simpl in *.
    eapply apply_contd_rename_tvar with (X:=X) (Y:=Y) in H2 as Hac...
    eapply a_wl_red__applyd...
    auto_apply...
    eapply a_wf_wwl_apply_contd in H0... 
Qed.


Print Assumptions rename_tvar_in_a_wf_wwl_a_wl_red.


Theorem rename_tvar_in_a_wf_twl_a_wl_red : forall Γ X Y,
  X <> Y ->
  ⊢ᵃʷₜ Γ ->
  Y `notin` dom (⌊ Γ ⌋ᵃ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  {Y ᵃʷ/ₜᵥ X} Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros. eapply rename_tvar_in_a_wf_wwl_a_wl_red; eauto.
  apply a_wf_twl_a_wf_wwl; auto.
Qed.


Theorem rename_tvar_in_a_wf_wl_a_wl_red : forall Γ X Y,
  X <> Y ->
  ⊢ᵃʷₛ Γ ->
  Y `notin` dom (⌊ Γ ⌋ᵃ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  {Y ᵃʷ/ₜᵥ X} Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros. eapply rename_tvar_in_a_wf_wwl_a_wl_red; eauto.
  apply a_wf_wl_a_wf_wwl; auto.
Qed.


Lemma rename_var_dom_upper : forall Γ x y,
  dom (⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ) [<=] dom (⌊ Γ ⌋ᵃ) `union` singleton y.
Proof.
  intros. induction Γ; simpl; try fsetdec.
  destruct ab; destruct_eq_atom; simpl; try fsetdec.
Qed.


Lemma fvar_in_aworklist'_awl_app : forall Γ1 Γ2,
  fvar_in_aworklist' (Γ2 ⧺ Γ1) [=] fvar_in_aworklist' Γ2 `union` fvar_in_aworklist' Γ1.
Proof.
  induction Γ2; simpl; try fsetdec; destruct ab; simpl; try fsetdec.  
Qed.

Lemma awl_app_rename_var_comm : forall Γ1 Γ2 x y,
  ({y ᵃʷ/ₑᵥ x} Γ2) ⧺ ({y ᵃʷ/ₑᵥ x} Γ1) =
  {y ᵃʷ/ₑᵥ x} (Γ2 ⧺ Γ1).
Proof.
  intros. induction Γ2; simpl in *; auto. 
  - destruct ab; auto; simpl; rewrite IHΓ2; auto.
  - simpl; rewrite IHΓ2; auto.
Qed.

Lemma aworklist_subst_rename_var : forall Γ x y X A Γ1 Γ2,
  y ∉ fvar_in_aworklist' Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  aworklist_subst ({y ᵃʷ/ₑᵥ x} Γ) X A ({y ᵃʷ/ₑᵥ x} Γ1) ({y ᵃʷ/ₑᵥ x} Γ2).
Proof.
  intros. induction H0; try solve [simpl in *; destruct_a_wf_wl; constructor; auto].
  simpl.
  rewrite <- awl_app_rename_var_comm... simpl.
  constructor; auto.
  replace ({y ᵃʷ/ₑᵥ x} Γ2 ⧺ X ~ᵃ ⬒;ᵃ Y ~ᵃ ⬒;ᵃ {y ᵃʷ/ₑᵥ x} Γ1) with ({y ᵃʷ/ₑᵥ x} (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1)).
  apply IHaworklist_subst. 
  - simpl in *. rewrite fvar_in_aworklist'_awl_app in *. simpl in *. solve_notin.
  - rewrite <- awl_app_rename_var_comm... simpl. auto.
Qed.


Lemma fvar_in_wf_exp_upper : forall Γ e,
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  fvar_in_exp e [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros. dependent induction H; try solve [simpl; fsetdec].
  - simpl. apply binds_In in H... fsetdec.
  - inst_cofinites_by (L `union` dom (⌊ Γ ⌋ᵃ) `union` fvar_in_exp e).
    assert (fvar_in_exp e [<=] fvar_in_exp (e ᵉ^^ₑ exp_var_f x)) by apply fvar_in_exp_open_exp_wrt_exp_lower.
    assert (x ~ abind_var_typ T ++ awl_to_aenv Γ = awl_to_aenv (x ~ᵃ T ;ᵃ Γ)) by (simpl; auto).
    eapply H1 in H3.
    simpl in *.
    fsetdec.
  - simpl.
    rewrite IHa_wf_exp1; eauto.
    rewrite IHa_wf_exp2; eauto.
    fsetdec.
  - pick fresh X. inst_cofinites_with X.
    replace (X ~ abind_tvar_empty ++ awl_to_aenv Γ) with (awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) in H0 by auto.
    simpl.
    assert (fvar_in_exp e [<=] fvar_in_exp (open_exp_wrt_typ e ` X)) by 
      apply fvar_in_exp_open_exp_wrt_typ_lower.
    specialize (H1 (X ~ᵃ □ ;ᵃ Γ) (eq_refl _)).
    simpl in *. fsetdec.
  - simpl. rewrite IHa_wf_exp; eauto. fsetdec.
  - simpl. rewrite IHa_wf_exp; eauto. fsetdec.
Qed.


Lemma fvar_in_wf_conts_upper : forall Γ cs,
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ cs ->
  fvar_in_conts cs [<=] dom (⌊ Γ ⌋ᵃ)
with fvar_in_wf_contd_upper : forall Γ cd,
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cd ->
  fvar_in_contd cd [<=] dom (⌊ Γ ⌋ᵃ).
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
  ⌊ Γ ⌋ᵃ ʷ⊢ᵃ w ->
  fvar_in_work w [<=] dom (⌊ Γ ⌋ᵃ).
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
  fvar_in_aworklist' Γ [<=] dom (⌊ Γ ⌋ᵃ).
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
  
Lemma rename_var_in_aworklist_fresh_eq : forall x y Γ,
  x ∉ fvar_in_aworklist' Γ ->
  {y ᵃʷ/ₑᵥ x} Γ = Γ.
Proof.
  intros. induction Γ; simpl in *; auto.
  - rewrite IHΓ; auto; destruct ab; 
    destruct_eq_atom; auto.
  - rewrite IHΓ; auto.
    rewrite subst_exp_in_work_fresh_eq; auto.
Qed.


Lemma subst_typ_in_exp_rename_var : forall x y X e A,
  y ∉ fvar_in_exp e ->
  {exp_var_f y ᵉ/ₑ x} {A ᵉ/ₜ X} e = {A ᵉ/ₜ X} {exp_var_f y ᵉ/ₑ x} e.
Proof with eauto.
  intros. induction e; simpl in *; auto...
  - destruct_eq_atom; simpl; auto. 
  - rewrite IHe...
  - rewrite IHe1...
    rewrite IHe2...
  - rewrite IHe...
  - rewrite IHe...
  - rewrite IHe...
Qed.

Lemma subst_typ_in_conts_rename_var : forall x y X A cs,
  y ∉ fvar_in_conts cs ->
  {exp_var_f y ᶜˢ/ₑ x} {A ᶜˢ/ₜ X} cs = {A ᶜˢ/ₜ X} {exp_var_f y ᶜˢ/ₑ x} cs
with subst_typ_in_contd_rename_var : forall x y X A cd,
  y ∉ fvar_in_contd cd ->
  {exp_var_f y ᶜᵈ/ₑ x} {A ᶜᵈ/ₜ X} cd = {A ᶜᵈ/ₜ X} {exp_var_f y ᶜᵈ/ₑ x} cd.
Proof.
  - intros. induction cs; simpl in *;
    try rewrite subst_typ_in_exp_rename_var; auto;
    try rewrite IHcs; auto;
    try rewrite subst_typ_in_contd_rename_var; auto...
  - intros. induction cd; simpl in *;
    try repeat rewrite subst_typ_in_exp_rename_var; auto;
    try rewrite IHcd; auto;
    try rewrite subst_typ_in_conts_rename_var; auto.
Qed.

Lemma subst_typ_in_work_rename_var : forall x y X w A,
  y ∉ fvar_in_work w ->
  {exp_var_f y ʷ/ₑ x} {A ʷ/ₜ X} w = {A ʷ/ₜ X} {exp_var_f y ʷ/ₑ x} w.
Proof.
  intros. induction w; simpl in *; auto;
    try rewrite subst_typ_in_exp_rename_var; auto;
    try rewrite subst_typ_in_conts_rename_var; auto;
    try rewrite subst_typ_in_contd_rename_var; auto.
Qed.

Lemma subst_exp_in_awl_rename_tvar_comm : forall Γ x y X A,
  y ∉ fvar_in_aworklist' Γ ->
  ({y ᵃʷ/ₑᵥ x} ({A ᵃʷ/ₜ X} Γ)) =
  {A ᵃʷ/ₜ X} {y ᵃʷ/ₑᵥ x} Γ.
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - destruct ab; destruct_eq_atom; auto.
  - destruct ab; destruct_eq_atom; auto.
  - rewrite subst_typ_in_work_rename_var; auto.
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

Lemma rename_var_in_aworklist_tvar_bind_same : forall Γ x y X b,
  ⊢ᵃʷ Γ ->
  (~ exists A, b = abind_var_typ A) ->
  y ∉ fvar_in_aworklist' Γ ->
  binds X b (⌊ Γ ⌋ᵃ) ->
  binds X b (⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ).
Proof.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H; destruct_eq_atom; destruct_binds; auto. solve_false.
  - dependent destruction H; destruct_binds; auto.
Qed.

Lemma rename_var_in_aworklist_var_bind_same : forall Γ x x' y A,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  binds x' (abind_var_typ A) (⌊ Γ ⌋ᵃ) ->
  binds (if x' == x then y else x') (abind_var_typ A) (awl_to_aenv ({y ᵃʷ/ₑᵥ x} Γ)).
Proof.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H; destruct_eq_atom; destruct_binds; auto.
  - dependent destruction H; destruct_binds; auto.
Qed.

Lemma rename_var_in_aworklist_eq_var_bind_same : forall Γ x y A,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ ->
  y ~ A ∈ᵃ ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ.
Proof.
  intros. eapply rename_var_in_aworklist_var_bind_same with (x':=x) (x:=x) in H1; eauto.
  destruct_eq_atom. auto.  
Qed.

Lemma rename_var_in_aworklist_neq_var_bind_same : forall Γ x x' y A,
  ⊢ᵃʷ Γ ->
  x' <> x ->
  y ∉ fvar_in_aworklist' Γ ->
  x' ~ A ∈ᵃ ⌊ Γ ⌋ᵃ  ->
  x' ~ A ∈ᵃ ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ.
Proof.
  intros. eapply rename_var_in_aworklist_var_bind_same with (x':=x') (x:=x) in H1; eauto.
  destruct_eq_atom. auto.  
Qed.

Lemma notin_rename_var_in_aworklist : forall x y Γ,
  x <> y ->
  x ∉ fvar_in_aworklist' ({y ᵃʷ/ₑᵥ x} Γ).
Proof.
  induction Γ; intros; simpl in *; auto.
  - destruct_eq_atom; destruct ab; auto.
  - simpl. rewrite fvar_in_work_subst_exp_in_work_upper; simpl; auto.
Qed.

Lemma rename_var_in_exp_rev_eq : forall x y e,
  y ∉ fvar_in_exp e ->
  {exp_var_f x ᵉ/ₑ y} {exp_var_f y ᵉ/ₑ x} e = e.
Proof.
  intros. induction e; simpl in *; auto;
  try rewrite IHe; try rewrite IHe1; try rewrite IHe2; auto.
  - destruct_eq_atom.
    + simpl. destruct_eq_atom; auto.
    + simpl. destruct_eq_atom; auto.
Qed.


Lemma rename_var_in_conts_rev_eq : forall x y cs,
  y ∉ fvar_in_conts cs ->
  {exp_var_f x ᶜˢ/ₑ y} {exp_var_f y ᶜˢ/ₑ x} cs = cs
with rename_var_in_contd_rev_eq : forall x y cd,
  y ∉ fvar_in_contd cd ->
  {exp_var_f x ᶜᵈ/ₑ y} {exp_var_f y ᶜᵈ/ₑ x} cd = cd.
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

Lemma rename_var_in_work_rev_eq : forall x y w,
  y ∉ fvar_in_work w ->
  {exp_var_f x ʷ/ₑ y} {exp_var_f y ʷ/ₑ x} w = w.
Proof.
  intros. dependent destruction w; simpl in *;
    try rewrite rename_var_in_exp_rev_eq; 
    try rewrite rename_var_in_conts_rev_eq;
    try rewrite rename_var_in_contd_rev_eq; auto.
Qed.

Lemma rename_var_in_aworklist_rev_eq : forall x y Γ,
  y ∉ fvar_in_aworklist' Γ ->
  {x ᵃʷ/ₑᵥ y} {y ᵃʷ/ₑᵥ x} Γ = Γ.
Proof.
  induction Γ; simpl in *; auto; intros; destruct_a_wf_wl.
  - destruct ab;  destruct_eq_atom; simpl; rewrite IHΓ; auto.
    destruct_eq_atom; auto.
    destruct_eq_atom; auto.
  - rewrite IHΓ; auto.
    rewrite rename_var_in_work_rev_eq; auto.
Qed.

Lemma rename_var_apply_conts : forall x y cs w A,
  apply_conts cs A w ->
  apply_conts ({exp_var_f y ᶜˢ/ₑ x} cs) A ({exp_var_f y ʷ/ₑ x} w).
Proof.
  intros. induction H; simpl; try constructor.
Qed.

Lemma rename_var_apply_contd : forall x y cd w A B,
  apply_contd cd A B w ->
  apply_contd ({exp_var_f y ᶜᵈ/ₑ x} cd) A B ({exp_var_f y ʷ/ₑ x} w).
Proof.
  intros. induction H; simpl; try constructor; auto.
Qed.

Ltac solve_notin_rename_var' :=
  match goal with
  | H : context [(dom (awl_to_aenv ?Γ))] |- context [fvar_in_aworklist' ?Γ] =>
    rewrite fvar_in_aworklist_upper; auto
  | H : _ |- context [open_exp_wrt_exp ?e1 ?e2] =>
    rewrite fvar_in_exp_open_exp_wrt_exp_upper; auto
  | H : _ |- context [subst_exp_in_exp ?e1 ?x ?e2]  =>
    match goal with
    | H1 : x ∉ fvar_in_exp (subst_exp_in_exp e1 x e2) |- _ => fail 1
    | _ => assert (x ∉ fvar_in_exp (subst_exp_in_exp e1 x e2)) by (apply subst_exp_in_exp_fresh_same; auto)
    end
  | H : _ |- context [subst_exp_in_contd ?cd ?x ?e]  =>
    match goal with
    | H1 : x ∉ fvar_in_contd (subst_exp_in_contd cd x e) |- _ => fail 1
    | _ => assert (x ∉ fvar_in_contd (subst_exp_in_contd cd x e)) by (apply subst_exp_in_contd_fresh_same; auto)
    end
  | H : _ |- context [rename_var_in_aworklist ?x' ?x ?Γ] =>
    (* assert True *)
    match goal with
    | H1 : x ∉ fvar_in_aworklist' (rename_var_in_aworklist x' x Γ) |- _ => fail 1
    | _ =>
      assert (x ∉ fvar_in_aworklist' (rename_var_in_aworklist x' x Γ)) by
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
  | H : context [rename_var_in_aworklist _ _ (subst_typ_in_aworklist _ _ _)] |- _ =>
      rewrite subst_exp_in_awl_rename_tvar_comm in H; auto;
      solve_notin_rename_var
  end.

Ltac rewrite_aworklist_rename_var :=
  repeat rewrite_aworklist_rename_var'.

Lemma rename_var_a_wf_typ : forall Γ x y A,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ ᵗ⊢ᵃ A.
Proof.
  intros. dependent induction H1; try solve [simpl in *; eauto].
  - constructor. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - apply a_wf_typ__stvar. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - apply a_wf_typ__etvar. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X; auto.
    replace (X ~ □ ++ ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ) with (⌊ {y ᵃʷ/ₑᵥ x} (X ~ᵃ □ ;ᵃ Γ) ⌋ᵃ) by (simpl; auto).
    apply H1; auto.
Qed.


Lemma rename_var_a_mono_typ : forall Γ x y T,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ T ->
  ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ ᵗ⊢ᵃₘ T.
Proof.
  intros. dependent induction H1; try solve [simpl in *; eauto].
  - constructor. apply rename_var_in_aworklist_tvar_bind_same; auto.
  - apply a_mono_typ__etvar. apply rename_var_in_aworklist_tvar_bind_same; auto.
Qed.


Lemma rename_var_a_wf_exp : forall Γ x y e,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ ᵉ⊢ᵃ {exp_var_f y ᵉ/ₑ x} e.
Proof with eauto using rename_var_a_wf_typ.
  intros. dependent induction H1; simpl in *...
  - simpl. destruct_eq_atom.
    + eapply rename_var_in_aworklist_eq_var_bind_same in H1...
    + eapply rename_var_in_aworklist_neq_var_bind_same in H1...
  - inst_cofinites_for a_wf_exp__abs T:=T; intros; inst_cofinites_with x; auto.
    apply rename_var_a_wf_typ...
    replace (({exp_var_f y ᵉ/ₑ x} e) ᵉ^^ₑ exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} (e ᵉ^^ₑ exp_var_f x0)).
    replace (x0 ~ abind_var_typ T ++ ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ) with (⌊ {y ᵃʷ/ₑᵥ x} (x0 ~ᵃ T;ᵃ Γ) ⌋ᵃ)...
    + simpl. destruct_eq_atom...
    + rewrite subst_exp_in_exp_open_exp_wrt_exp... simpl. destruct_eq_atom...
  - inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X; auto.
    simpl in *.
    rewrite <- subst_exp_in_exp_open_exp_wrt_typ; eauto.
    rewrite_env (⌊ {y ᵃʷ/ₑᵥ x} ( X ~ᵃ □ ;ᵃ Γ )⌋ᵃ)...
Qed.


Lemma rename_var_a_wf_conts : forall Γ x y cs,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ cs ->
  ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ ᶜˢ⊢ᵃ {exp_var_f y ᶜˢ/ₑ x} cs
with rename_var_a_wf_contd : forall Γ x y cd,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cd ->
  ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ ᶜᵈ⊢ᵃ {exp_var_f y ᶜᵈ/ₑ x} cd.
Proof with eauto using rename_var_a_wf_typ, rename_var_a_wf_exp.
  - intros. clear rename_var_a_wf_conts. dependent induction H1; simpl...
  - intros. clear rename_var_a_wf_contd. dependent induction H1; simpl...
Qed.


Lemma rename_var_a_wf_work : forall Γ x y w,
  ⊢ᵃʷ Γ ->
  y ∉ fvar_in_aworklist' Γ ->
  ⌊ Γ ⌋ᵃ ʷ⊢ᵃ w ->
  ⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ ʷ⊢ᵃ {exp_var_f y ʷ/ₑ x} w.
Proof with eauto 10 using rename_var_a_wf_typ, rename_var_a_wf_exp, rename_var_a_wf_conts, rename_var_a_wf_contd.
  intros. dependent destruction H1; simpl in *...
Qed.


Lemma rename_var_a_wf_wwl : forall Γ x y,
  ⊢ᵃʷ Γ ->
  y ∉ dom (⌊ Γ ⌋ᵃ) ->
  ⊢ᵃʷ {y ᵃʷ/ₑᵥ x} Γ.
Proof with eauto.
  intros. induction H; try solve [simpl in *; eauto].
  - simpl in *. destruct_eq_atom. 
    + constructor... rewrite rename_var_in_aworklist_fresh_eq; auto.
      rewrite fvar_in_aworklist_upper; eauto.
      apply rename_var_a_wf_typ; auto. rewrite fvar_in_aworklist_upper; eauto.
    + constructor... rewrite rename_var_dom_upper...
      apply rename_var_a_wf_typ; auto. rewrite fvar_in_aworklist_upper; eauto.
  - simpl in *. destruct_binds.
    assert (y ∉ dom (⌊ Γ ⌋ᵃ)) by auto.
    apply IHa_wf_wwl in H2... constructor... 
    rewrite rename_var_dom_upper; auto... 
  - simpl in *. destruct_binds.
    assert (y ∉ dom (⌊ Γ ⌋ᵃ)) by auto.
    apply IHa_wf_wwl in H2... constructor... 
    rewrite rename_var_dom_upper; auto... 
  - simpl in *. destruct_binds.
    assert (y ∉ dom (⌊ Γ ⌋ᵃ)) by auto.
    apply IHa_wf_wwl in H2... constructor... 
    rewrite rename_var_dom_upper; auto... 
  - simpl in *. constructor; auto.
    apply rename_var_a_wf_work...
    rewrite fvar_in_aworklist_upper; auto... 
Qed.


Ltac create_fvar_in_awl_set :=
  match goal with 
  | H1 : ⊢ᵃʷ ?Γ , H2 : ?x ∉ dom (⌊ ?Γ ⌋ᵃ) |- _ =>
    let Hfv := fresh "Hfv" in
    assert (Hfv: x ∉ fvar_in_aworklist' Γ) by (rewrite fvar_in_aworklist_upper; auto)
  end.

Lemma a_exp_split_size_rename_var : forall Γ x y e n,
  ⊢ᵃʷ Γ ->
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  y `notin` dom ( ⌊ Γ ⌋ᵃ ) ->
  a_exp_split_size (⌊ Γ ⌋ᵃ) e n -> 
  a_exp_split_size (⌊ {y ᵃʷ/ₑᵥ x} Γ ⌋ᵃ) ({exp_var_f y ᵉ/ₑ x} e) n.
Proof.
  intros.
Admitted.

Theorem rename_var_in_a_wf_wwl_a_wl_red : forall Γ x y,
  ⊢ᵃʷ Γ ->
  y <> x ->
  y ∉ dom (⌊ Γ ⌋ᵃ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  {y ᵃʷ/ₑᵥ x} Γ ⟶ᵃʷ⁎⋅.
Proof with eauto.
  intros. dependent induction H2; try solve [simpl in *; try apply_IH_a_wf_wwl; eauto]; create_fvar_in_awl_set.
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
    + intros. eapply rename_var_a_mono_typ with (y:=x) (x:=y) in H0... 
      * rewrite rename_var_in_aworklist_rev_eq in H0...
      * apply rename_var_a_wf_wwl...
      * solve_notin_rename_var.
    + intros.
      apply aworklist_subst_rename_var with (x:=y) (y:=x) in H9 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H7 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev...
        -- eapply aworklist_subst_wf_wwl with (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto...
           repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow2; auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + intros. eapply rename_var_a_mono_typ with (y:=x) (x:=y) in H9... 
      * rewrite rename_var_in_aworklist_rev_eq in H9...
      * apply rename_var_a_wf_wwl...
      * solve_notin_rename_var.
    + intros.
      apply aworklist_subst_rename_var with (x:=y) (y:=x) in H11 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H8 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev...
        -- apply aworklist_subst_wf_wwl with (Γ:=(work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto 7.
           repeat (constructor; simpl; auto).
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono1 with (Γ1:=({y ᵃʷ/ₑᵥ x} Γ1))
      (Γ2:=({y ᵃʷ/ₑᵥ x} Γ2)); auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + apply rename_var_a_mono_typ with (y:=y) (x:=x) in H5...
    + apply aworklist_subst_rename_var with (x:=x) (y:=y) in H7 as Hws; eauto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev...
      auto_apply; auto.
      * eapply aworklist_subst_wf_wwl...
      * erewrite aworklist_subst_dom_upper...
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono2 with (Γ1:=({y ᵃʷ/ₑᵥ x} Γ1))
      (Γ2:=({y ᵃʷ/ₑᵥ x} Γ2)); auto.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + apply rename_var_a_mono_typ with (y:=y) (x:=x) in H5...
    + apply aworklist_subst_rename_var with (x:=x) (y:=y) in H7 as Hws; eauto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev.
      auto_apply.
      * eapply aworklist_subst_wf_wwl...
      * erewrite aworklist_subst_dom_upper...
  - destruct_a_wf_wl. simpl in *. 
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x0.
    destruct_eq_atom.
    rewrite subst_exp_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    repeat (constructor; simpl; auto)...
    + apply a_wf_exp_var_binds_another_cons with (A1:=T)...
    + apply a_wf_typ_weaken_cons...
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absetvar.
    + apply rename_var_in_aworklist_tvar_bind_same... 
    + intros. inst_cofinites_with x0. inst_cofinites_with X1. inst_cofinites_with X2.
      apply aworklist_subst_rename_var with (x:=y) (y:=x) in H11 as Hws.
      simpl in Hws. destruct_eq_atom.
      rewrite_aworklist_rename_var_rev.
      * simpl in Hws.
        replace (({exp_var_f y ᵉ/ₑ x} e) ᵉ^^ₑ exp_var_f x0) with
          (({exp_var_f y ᵉ/ₑ x} e) ᵉ^^ₑ ({exp_var_f y ᵉ/ₑ x} exp_var_f x0)) in Hws by (simpl; destruct_eq_atom; auto).
        rewrite <- subst_exp_in_exp_open_exp_wrt_exp in Hws; auto.
        rewrite rename_var_in_exp_rev_eq in Hws.
        -- apply H7 in Hws; auto.
           ++ rewrite_aworklist_rename_var.
              rewrite_aworklist_rename_var_rev...
           ++ apply aworklist_subst_wf_wwl with (Γ:=(work_check (e ᵉ^^ₑ exp_var_f x0) ` X2 ⫤ᵃ x0 ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto 7... 
              repeat (constructor; simpl; auto)... apply a_wf_exp_weaken_etvar_twice with (T:=T)...
           ++ rewrite aworklist_subst_dom_upper with (Γ:=(work_check (e ᵉ^^ₑ exp_var_f x0) ` X2 ⫤ᵃ x0 ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
        -- solve_notin_rename_var.
      * simpl. solve_notin_rename_var.
  - destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x0.
    destruct_eq_atom. 
    rewrite subst_exp_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    repeat (constructor; simpl; auto).
    eapply a_wf_exp_var_binds_another_cons with (A1:=T); eauto.
  - simpl in *.
    destruct (x0 == x); subst; apply a_wl_red__inf_var with (A:=A).
    + destruct_a_wf_wl... apply rename_var_in_aworklist_eq_var_bind_same...  
    + auto_apply; auto. destruct_a_wf_wl. unify_binds. apply a_wf_wwl_a_wf_env in H1 as Hwfenv. apply a_wf_env_bind_a_wf_typ in H...
    + destruct_a_wf_wl... apply rename_var_in_aworklist_neq_var_bind_same...  
    + auto_apply; auto. destruct_a_wf_wl. unify_binds. apply a_wf_wwl_a_wf_env in H1 as Hwfenv. apply a_wf_env_bind_a_wf_typ in H...
  - destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__inf_tabs...
    intros. inst_cofinites_with X (keep).
    rewrite subst_exp_in_exp_open_exp_wrt_typ in *...
    auto_apply...
    dependent destruction H5.
    repeat (constructor; simpl; auto).
    + inst_cofinites_for a_wf_typ__all; intros; auto.
      inst_cofinites_with X0; auto. dependent destruction H10...
  - destruct_a_wf_wl. simpl in *.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros.
    destruct_eq_atom.
    inst_cofinites_with x0. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_exp_in_exp_open_exp_wrt_exp in *; auto; simpl in *.
    destruct_eq_atom.
    auto_apply; auto.
    repeat (constructor; simpl; auto)...
    apply a_wf_exp_weaken_etvar_twice with (T:=T)...
    apply a_wf_conts_weaken_cons...  apply a_wf_conts_weaken_cons...
  - simpl in *. destruct_a_wf_wl.
    apply a_exp_split_size_rename_var with (x:=x) (y:=y) in H5...
    econstructor; eauto.
    eapply IHa_wl_red; eauto.
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
    + intros. apply aworklist_subst_rename_var with (x:=y) (y:=x) in H9 as Hws...
      * simpl in Hws. destruct_eq_atom.
        rewrite rename_var_in_aworklist_rev_eq in Hws...
        rewrite rename_var_in_contd_rev_eq in Hws...
        apply H6 in Hws as Hawlred; simpl; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev...
        -- destruct_a_wf_wl. 
           apply aworklist_subst_wf_wwl with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl; auto.
           repeat (constructor; simpl; auto).
           apply a_wf_contd_weaken_cons... apply a_wf_contd_weaken_cons...
        -- rewrite aworklist_subst_dom_upper with (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ))...
      * solve_notin_rename_var. 
  - destruct_a_wf_wl. 
    eapply a_wl_red__inftapp_all.
    auto_apply; auto.
    repeat (constructor; simpl; auto).
    apply a_wf_typ_all_open...
  - simpl in *.
    eapply rename_var_apply_conts with (y:=y) (x:=x) in H2 as Hac.
    econstructor; eauto.
    auto_apply...
    eapply a_wf_wwl_apply_conts; eauto.
  - simpl in *.
    eapply rename_var_apply_contd with (y:=y) (x:=x) in H2 as Hac.
    econstructor; eauto.
    auto_apply...
    eapply a_wf_wwl_apply_contd; eauto.
Qed.


Theorem rename_var_in_a_wf_twl_a_wl_red : forall Γ x y,
  ⊢ᵃʷₜ Γ ->
  y <> x ->
  y `notin` dom (⌊ Γ ⌋ᵃ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  {y ᵃʷ/ₑᵥ x} Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros. eapply rename_var_in_a_wf_wwl_a_wl_red; eauto.
  apply a_wf_twl_a_wf_wwl; auto.
Qed.

Theorem rename_var_in_a_wf_wl_a_wl_red : forall Γ x y,
  ⊢ᵃʷₛ Γ ->
  y <> x ->
  y `notin` dom (⌊ Γ ⌋ᵃ) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  {y ᵃʷ/ₑᵥ x} Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros. eapply rename_var_in_a_wf_wwl_a_wl_red; eauto.
  apply a_wf_wl_a_wf_wwl; auto.
Qed.  
