Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import ltac_utils.


Open Scope aworklist_scope.
Open Scope abind_scope.


Lemma a_wf_wl_a_wf_env : forall Γ,
  ⊢ᵃʷ Γ ->
  a_wf_env (awl_to_aenv Γ).
Proof.
  introv HW. induction* HW.
  all: cbn; econstructor; eauto.
Qed.

Lemma a_wf_env_uniq : forall Σ,
  a_wf_env Σ ->
  uniq Σ.
Proof.
  intros. induction H; auto.
Qed.

Lemma a_wf_typ_lc : forall Σ A,
  a_wf_typ Σ A ->
  lc_typ A.
Proof.
  intros. induction H; auto.
Qed.


Lemma a_mono_typ_lc : forall Σ A,
  a_mono_typ Σ A ->
  lc_typ A.
Proof.
  intros. induction H; auto.
Qed.

#[global] Hint Resolve a_wf_typ_lc a_mono_typ_lc : core.

Lemma a_mono_typ_in_s_in : forall Σ A X,
  a_mono_typ Σ A ->
  X `in` ftvar_in_typ A ->
  s_in X A.
Proof.
  intros. induction H; simpl in *; auto.
  - fsetdec. 
  - apply singleton_iff in H0. subst. constructor.
  - apply singleton_iff in H0. subst. constructor.
  - apply union_iff in H0. destruct H0.
    + apply s_in__arrow1; auto. eapply a_mono_typ_lc; eauto.
    + apply s_in__arrow2; auto. eapply a_mono_typ_lc; eauto.
Qed.


Theorem a_mono_typ_wf : forall Σ A,
  a_mono_typ Σ A -> a_wf_typ Σ A.
Proof.
  intros. induction H; auto.
Qed.


Lemma a_wf_typ_weaken: forall Σ1 Σ2 Σ3 A,
  a_wf_typ (Σ3 ++ Σ1) A ->
  a_wf_typ (Σ3 ++ Σ2 ++ Σ1) A.
Proof.
  introv H. dependent induction H; eauto.
  - pick fresh X0 and apply a_wf_typ__all.
    + forwards*: H X0.
    + forwards*: H X0. forwards*: H0 X0.
      forwards*: H1 X0  Σ1 (X0 ~ abind_tvar_empty ++ Σ3); auto.
Qed.

Lemma a_wf_typ_weaken_app: forall Σ1 Σ2 A,
  a_wf_typ Σ1 A ->
  a_wf_typ (Σ2 ++ Σ1) A.
Proof.
  intros. rewrite_env (nil ++ Σ2 ++ Σ1).
  apply a_wf_typ_weaken; auto.
Qed.

Corollary a_wf_typ_weaken_cons: forall Σ X t A,
  a_wf_typ Σ A ->
  a_wf_typ ((X, t) :: Σ) A.
Proof with simpl in *; try solve_notin.
  intros. simpl.
  rewrite_env (nil ++ (X ~ t) ++ Σ).
  apply a_wf_typ_weaken; auto...
Qed.


Lemma a_wf_exp_weaken: forall Σ1 Σ2 Σ3 e,
  a_wf_exp (Σ3 ++ Σ1) e ->
  a_wf_exp (Σ3 ++ Σ2 ++ Σ1) e
with a_wf_body_weaken : forall Σ1 Σ2 Σ3 b,
  a_wf_body (Σ3 ++ Σ1) b ->
  a_wf_body (Σ3 ++ Σ2 ++ Σ1) b.
Proof with eauto using a_wf_typ_weaken.
  - intros. clear a_wf_exp_weaken. dependent induction H...
    + intros. apply a_wf_exp__abs with (T:=T)
      (L:=union L (union (dom Σ2) (union (dom Σ1) (union (dom Σ3) (ftvar_in_typ T)))))...
      intros. rewrite_env ((x ~ abind_var_typ T ++ Σ3) ++ Σ2 ++ Σ1).
      apply H1...
    + intros. inst_cofinites_for a_wf_exp__tabs... intros.
      inst_cofinites_with X.
      rewrite_env ((X ~ abind_tvar_empty ++ Σ3) ++ Σ2 ++ Σ1).
      apply a_wf_body_weaken...
  - intros. dependent destruction H; constructor...
Qed.

Lemma a_wf_conts_weaken: forall Σ1 Σ2 Σ3 cs,
  a_wf_conts (Σ3 ++ Σ1) cs ->
  a_wf_conts (Σ3 ++ Σ2 ++ Σ1) cs
with a_wf_contd_weaken : forall Σ1 Σ2 Σ3 cd,
  a_wf_contd (Σ3 ++ Σ1) cd ->
  a_wf_contd (Σ3 ++ Σ2 ++ Σ1) cd.
Proof with eauto using a_wf_typ_weaken, a_wf_exp_weaken.
  - intros. dependent induction H; constructor...
  - intros. dependent induction H; constructor...
Qed.

Lemma a_wf_conts_weaken_cons : forall Σ X b cs,
  a_wf_conts Σ cs ->
  a_wf_conts ((X, b) :: Σ) cs.
Proof.
  intros. 
  rewrite_env (nil ++ (X ~ b) ++ Σ).
  apply a_wf_conts_weaken; auto.
Qed.

Lemma a_wf_contd_weaken_cons : forall Σ X b cd,
  a_wf_contd Σ cd ->
  a_wf_contd ((X, b) :: Σ) cd.
Proof.
  intros. 
  rewrite_env (nil ++ (X ~ b) ++ Σ).
  apply a_wf_contd_weaken; auto.
Qed.

Lemma a_wf_work_weaken: forall Σ1 Σ2 Σ3 w,
  a_wf_work (Σ3 ++ Σ1) w ->
  a_wf_work (Σ3 ++ Σ2 ++ Σ1) w.
Proof with eauto using a_wf_typ_weaken, a_wf_exp_weaken, a_wf_conts_weaken, a_wf_contd_weaken.
  intros. dependent destruction H...
  constructor...
Qed.

Lemma a_wf_typ_strengthen: forall Σ1 Σ2 A X b,
  a_wf_typ (Σ2 ++ (X, b) :: Σ1) A ->
  X `notin` ftvar_in_typ A ->
  a_wf_typ (Σ2 ++ Σ1) A.
Proof.
  intros * Hwf Hnotin. dependent induction Hwf; simpl in *; eauto.
  - apply notin_singleton_1 in Hnotin. 
    apply binds_remove_mid in H; eauto.
  - apply notin_singleton_1 in Hnotin. 
    apply binds_remove_mid in H; eauto.
  - apply notin_singleton_1 in Hnotin. 
    apply binds_remove_mid in H; eauto.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
    rewrite_env ((X0 ~ □ ++ Σ2) ++ Σ1).
    eapply H1 with (X:=X) (b:=b); eauto.
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper; eauto.
Qed.


Corollary a_wf_typ_strengthen_cons: forall Σ X A b,
  a_wf_typ ((X, b) :: Σ) A ->
  X `notin` ftvar_in_typ A ->
  a_wf_typ Σ A.
Proof.
  intros. rewrite_env (nil ++ Σ).
  eapply a_wf_typ_strengthen; eauto.
Qed.

Lemma a_wf_typ_strengthen_var: forall Σ1 Σ2 A X B,
  a_wf_typ (Σ2 ++ (X, abind_var_typ B) :: Σ1) A ->
  a_wf_typ (Σ2 ++ Σ1) A.
Proof.
  intros * Hwf. dependent induction Hwf; simpl in *; eauto.
  - apply binds_remove_mid_diff_bind in H; eauto.
    solve_false.
  - apply binds_remove_mid_diff_bind in H; eauto.
    solve_false.
  - apply binds_remove_mid_diff_bind in H; eauto.
    solve_false.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
    rewrite_env ((X0 ~ □ ++ Σ2) ++ Σ1).
    eapply H1 with (X:=X) (B:=B); eauto.
Qed.

Corollary a_wf_typ_strengthen_var_cons: forall Σ X A B,
  a_wf_typ ((X, abind_var_typ B) :: Σ) A ->
  a_wf_typ Σ A.
Proof. 
  intros. rewrite_env (nil ++ Σ).
  eapply a_wf_typ_strengthen_var; eauto.
Qed.


Lemma a_mono_typ_strengthen_mtvar : forall Σ X b T,
  b = abind_tvar_empty \/ b = abind_etvar_empty ->
  a_mono_typ ((X, b) :: Σ) T ->
  X `notin` ftvar_in_typ T ->
  a_mono_typ Σ T.
Proof.
  intros. dependent induction H0; eauto.
  - inversion H0. dependent destruction H2.
    simpl in *. solve_notin_eq X0.
    auto.
  - inversion H0. dependent destruction H2.
    simpl in *. solve_notin_eq X0.
    auto. 
  - simpl in *; eauto.
Qed.

Lemma a_mono_typ_strengthen_stvar : forall Σ X T,
  a_mono_typ ((X, abind_stvar_empty) :: Σ) T ->
  a_mono_typ Σ T.
Proof.
  intros. dependent induction H; eauto.
  - inversion H. dependent destruction H0.
    constructor; auto.
  - inversion H. dependent destruction H0.
    apply a_mono_typ__etvar; auto.
Qed.

Lemma a_mono_typ_strengthen_var : forall Σ x A T,
  a_mono_typ ((x, abind_var_typ A) :: Σ) T ->
  a_mono_typ Σ T.
Proof.
  intros. dependent induction H; eauto.
  - inversion H. dependent destruction H0.
    constructor; auto.
  - inversion H. dependent destruction H0.
    apply a_mono_typ__etvar; auto.
Qed.

Lemma a_wf_typ_var_binds_another : forall Σ1 x Σ2 A B1 B2,
  a_wf_typ (Σ2 ++ x ~ abind_var_typ B1 ++ Σ1) A ->
  a_wf_typ Σ1 B2 ->
  a_wf_typ (Σ2 ++ x ~ abind_var_typ B2 ++ Σ1) A.
Proof with eauto 5.
  intros. dependent induction H; simpl in *...
  - apply binds_remove_mid_diff_bind in H.
    constructor. apply binds_weaken_mid; auto.
    solve_false.
  - apply binds_remove_mid_diff_bind in H.
    apply a_wf_typ__stvar. apply binds_weaken_mid; auto.
    solve_false.
  - apply binds_remove_mid_diff_bind in H.
    apply a_wf_typ__etvar. apply binds_weaken_mid; auto.
    solve_false.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X; auto.
    rewrite_env ((X ~ □ ++ Σ2) ++ x ~ abind_var_typ B2 ++ Σ1); eauto.
    eapply H1 with (B1:=B1)... 
Qed.

Lemma a_wf_exp_var_binds_another : forall Σ1 x Σ2 e A1 A2,
  a_wf_exp (Σ2 ++ x ~ abind_var_typ A1 ++ Σ1) e ->
  a_wf_typ Σ1 A2 ->
  a_wf_exp (Σ2 ++ x ~ abind_var_typ A2 ++ Σ1) e
with a_wf_body_var_binds_another : forall Σ1 x Σ2 b A1 A2,
  a_wf_body (Σ2 ++ x ~ abind_var_typ A1 ++ Σ1) b ->
  a_wf_typ Σ1 A2 ->
  a_wf_body (Σ2 ++ x ~ abind_var_typ A2 ++ Σ1) b.
Proof with eauto 5 using a_wf_typ_var_binds_another.
  - intros. clear a_wf_exp_var_binds_another. dependent induction H... (* slow *)
    + destruct (x==x0).
      * subst. econstructor...
      * apply binds_remove_mid in H; auto.
        econstructor... 
    + inst_cofinites_for a_wf_exp__abs T:=T; intros; inst_cofinites_with x0; auto...
      rewrite_env ((x0 ~ abind_var_typ T ++ Σ2) ++ x ~ abind_var_typ A2 ++ Σ1); eauto.
      eapply H1 with (A1:=A1)...
    + inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X; auto...
      rewrite_env ((X ~ □ ++ Σ2) ++ x ~ abind_var_typ A2 ++ Σ1); eauto.
      eapply a_wf_body_var_binds_another with (A1:=A1)...
  - intros. clear a_wf_body_var_binds_another.
    dependent destruction H... 
Qed.

Lemma a_wf_exp_var_binds_another_cons : forall Σ1 x e A1 A2,
  a_wf_exp (x ~ abind_var_typ A1 ++ Σ1) e ->
  a_wf_typ Σ1 A2 ->
  a_wf_exp (x ~ abind_var_typ A2 ++ Σ1) e.
Proof.
  intros.
  rewrite_env (nil ++ x ~ abind_var_typ A2 ++ Σ1).
  eapply a_wf_exp_var_binds_another; eauto.
Qed.


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


Ltac destruct_in :=
  simpl in *;
  match goal with
  | H1 : ((?X, ?b) = (?X', ?b')) \/  In ?b'' ?θ |- _ =>
    let H1_1 := fresh "H" in
    let H1_2 := fresh "H" in
    inversion H1 as [H1_1 | H1_2];
    clear H1;
    try destruct_binds_eq;
    try solve [solve_notin_eq X];
    try solve [solve_notin_eq X']
  end.


Corollary a_wf_typ_tvar_stvar : forall Σ1 Σ2 X A,
  Σ2 ++ (X , □) :: Σ1 ᵗ⊢ᵃ A ->
  Σ2 ++ (X , ■) :: Σ1 ᵗ⊢ᵃ A.
Proof.
  intros. dependent induction H; eauto.
  - destruct (X0 == X).
    + subst. apply a_wf_typ__stvar; eauto.
    + apply binds_remove_mid in H; auto. constructor. apply binds_weaken_mid; auto.
  - apply binds_remove_mid_diff_bind in H.
    apply a_wf_typ__stvar... apply binds_weaken_mid; auto. solve_false.
  - apply binds_remove_mid_diff_bind in H.
    apply a_wf_typ__etvar... apply binds_weaken_mid; auto. solve_false. 
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
    rewrite_env ((X0 ~ □ ++ Σ2) ++ (X, ■) :: Σ1); eauto.
Qed.


Corollary a_wf_typ_tvar_stvar_cons : forall Σ X A,
  (X , □) :: Σ ᵗ⊢ᵃ A ->
  (X , ■) :: Σ ᵗ⊢ᵃ A.
Proof.
  intros. rewrite_env (nil ++ (X , ■) :: Σ).
  apply a_wf_typ_tvar_stvar; auto.
Qed.


Corollary a_wf_typ_tvar_etvar : forall Σ1 Σ2 X A,
  Σ2 ++ (X , □) :: Σ1 ᵗ⊢ᵃ A ->
  Σ2 ++ (X , ⬒) :: Σ1 ᵗ⊢ᵃ A.
Proof.
  intros. dependent induction H; eauto.
  - destruct (X0 == X).
    + subst. apply a_wf_typ__etvar; eauto.
    + apply binds_remove_mid in H; auto. constructor. apply binds_weaken_mid; auto.
  - apply binds_remove_mid_diff_bind in H.
    apply a_wf_typ__stvar... apply binds_weaken_mid; auto. solve_false.
  - apply binds_remove_mid_diff_bind in H.
    apply a_wf_typ__etvar... apply binds_weaken_mid; auto. solve_false. 
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
    rewrite_env ((X0 ~ □ ++ Σ2) ++ (X, ⬒) :: Σ1); eauto.
Qed.


Corollary a_wf_typ_tvar_etvar_cons : forall Σ X A,
  X ~ □ ++ Σ ᵗ⊢ᵃ A ->
  X ~ ⬒ ++ Σ ᵗ⊢ᵃ A.
Proof.
  intros. rewrite_env (nil ++ (X , ⬒) :: Σ).
  apply a_wf_typ_tvar_etvar; auto.
Qed.

Lemma ftvar_in_a_wf_typ_upper : forall Σ A, 
  a_wf_typ Σ A ->
  ftvar_in_typ A [<=] dom Σ.
Proof.
  intros. induction H; simpl; try fsetdec.
  - apply binds_In in H; fsetdec.
  - apply binds_In in H; fsetdec.
  - apply binds_In in H; fsetdec.
  - pick fresh X. 
    inst_cofinites_with X.
    assert (ftvar_in_typ A [<=] ftvar_in_typ (A ^ₜ X)) by apply ftvar_in_typ_open_typ_wrt_typ_lower.
    simpl in *.
    fsetdec.
Qed.

Lemma a_wf_typ_rename_tvar : forall Σ1 Σ2 X Y A,
  Σ2 ++ X ~ □ ++ Σ1 ᵗ⊢ᵃ A  ->
  map (subst_tvar_in_abind (typ_var_f Y) X ) Σ2 ++ Y ~ □ ++ Σ1 ᵗ⊢ᵃ { typ_var_f Y ᵗ/ₜ X } A.
Proof.
  intros. dependent induction H; simpl in *; destruct_eq_atom; auto.
  - constructor.
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (subst_tvar_in_abind ` Y X) H0; eauto.
      * apply binds_cons_iff in H0. iauto.
  - apply a_wf_typ__stvar. 
    forwards* [?|?]: binds_app_1 H.
    forwards: binds_map_2 (subst_tvar_in_abind ` Y X) H0; eauto.
    apply binds_cons_iff in H0. iauto.
  - apply a_wf_typ__etvar. 
    forwards* [?|?]: binds_app_1 H.
    forwards: binds_map_2 (subst_tvar_in_abind ` Y X) H0; eauto.
    apply binds_cons_iff in H0. iauto.  
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
      apply s_in_subst_inv; auto.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
      rewrite_env (map (subst_tvar_in_abind ` Y X) (X0 ~ □ ++ Σ2) ++ (Y, □) :: Σ1).
      apply H1; eauto.
Qed.

Corollary a_wf_typ_rename_tvar_cons : forall Σ X Y A,
  X ~ □ ++ Σ ᵗ⊢ᵃ A  ->
  Y ~ □ ++ Σ ᵗ⊢ᵃ { typ_var_f Y ᵗ/ₜ X } A.
Proof.
  intros.
  rewrite_env ((map (subst_tvar_in_abind (typ_var_f Y) X ) nil) ++ Y ~ abind_tvar_empty ++ Σ).
  apply a_wf_typ_rename_tvar; auto.
Qed.


Lemma a_wf_typ_subst : forall Σ1 X Σ2 A B,
  a_wf_env (Σ2 ++ X ~ □ ++ Σ1) ->
  Σ2 ++ X ~ □ ++ Σ1 ᵗ⊢ᵃ A ->
  Σ1 ᵗ⊢ᵃ B ->
  map (subst_tvar_in_abind B X) Σ2 ++ Σ1 ᵗ⊢ᵃ {B ᵗ/ₜ X} A.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; forwards: a_wf_env_uniq Hwfenv; try solve [simpl; auto]...
  - destruct (X0 == X).
    + subst. simpl. apply a_wf_typ_weaken_app...
      (* solve_uniq. *)
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (subst_tvar_in_abind B X) H1...
      * apply binds_cons_iff in H1. iauto.
  - destruct (X0 == X).
    + subst. simpl. apply a_wf_typ_weaken_app...
    + eapply a_wf_typ__stvar.
      forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (subst_tvar_in_abind B X) H1.
      forwards* [(?&?&?)|?]: binds_cons_uniq_1 H1...
  - destruct (X0 == X).
      + subst. simpl. apply a_wf_typ_weaken_app...
      + eapply a_wf_typ__etvar.
        forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (subst_tvar_in_abind B X) H1.
        forwards* [(?&?&?)|?]: binds_cons_uniq_1 H1...
  - simpl. inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_var...
      applys* s_in_subst_inv...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_var...
      replace ((X0, abind_tvar_empty) :: map (subst_tvar_in_abind B X) Σ2 ++ Σ1)
      with (map (subst_tvar_in_abind B X) ((X0, abind_tvar_empty) :: Σ2) ++ Σ1) by auto.
      apply H1; auto...
      econstructor...
Qed.



Lemma a_wf_typ_all_open : forall Σ A B,
  a_wf_env Σ ->
  Σ ᵗ⊢ᵃ typ_all A ->
  Σ ᵗ⊢ᵃ B ->
  Σ ᵗ⊢ᵃ A ^^ₜ B.
Proof.
  intros. dependent destruction H0.
  pick fresh X. inst_cofinites_with X.
  rewrite subst_tvar_in_typ_intro with (X1:=X) (A2:=B); auto.
  rewrite_env (map (subst_tvar_in_abind B X) nil ++ Σ).
  apply a_wf_typ_subst; auto.
  econstructor; auto.
Qed.


#[export] Hint Resolve a_mono_typ_wf a_wf_wl_a_wf_env a_wf_env_uniq : core.


Lemma a_wf_wl_a_wf_bind_typ : forall Γ x A,
  ⊢ᵃʷ Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  (awl_to_aenv Γ) ᵗ⊢ᵃ A.
Proof with eauto.
  intros. dependent induction H; eauto; 
    try (destruct_binds; apply a_wf_typ_weaken_cons; eauto).
  inversion H0.
Qed.
  
Lemma aworklist_binds_split : forall Γ X,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  exists Γ1 Γ2, (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) = Γ.
Proof.
  intros. induction H.
  - inversion H0.
  - destruct_binds.
    apply IHa_wf_wl in H4. destruct H4 as [Γ1 [Γ2 Heq]].
    exists Γ1, (x ~ᵃ A ;ᵃ Γ2).
    rewrite <- Heq. auto.
  - destruct_binds.
    apply IHa_wf_wl in H3. destruct H3 as [Γ1 [Γ2 Heq]].
    exists Γ1, (X0 ~ᵃ □ ;ᵃ Γ2).
    rewrite <- Heq. auto.
  - destruct_binds.
    apply IHa_wf_wl in H3. destruct H3 as [Γ1 [Γ2 Heq]].
    exists Γ1, (X0 ~ᵃ ■ ;ᵃ Γ2).
    rewrite <- Heq. auto.
  - destruct_binds.
    + exists Γ, aworklist_empty; auto.
    + apply IHa_wf_wl in H3. destruct H3 as [Γ1 [Γ2 Heq]].
      exists Γ1, (X0 ~ᵃ ⬒ ;ᵃ Γ2).
      rewrite <- Heq. auto.
  - simpl in H0.
    + apply IHa_wf_wl in H0. destruct H0 as [Γ1 [Γ2 Heq]].
      exists Γ1, (w ⫤ᵃ Γ2).
      rewrite <- Heq. auto.
Qed.

Ltac destruct_a_wf_wl :=
  repeat
    lazymatch goal with
    | H : a_wf_wl (aworklist_conswork ?Γ ?w) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_consvar ?Γ ?w ?b) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_constvar ?Γ ?X ?b) |- _ => dependent destruction H
    | H : a_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : a_wf_typ ?E (open_typ_wrt_typ ?A ?T) |- _ => fail
    | H : a_wf_typ ?E (?Ct ?A1 ?A2) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?b) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?e1 ?e2) |- _ => dependent destruction H
    | H : a_wf_conts ?E (?C_C _) |- _ => dependent destruction H
    | H : a_wf_conts ?E (?C_C _ _) |- _ => dependent destruction H
    | H : a_wf_conts ?E (?C_C _ _ _) |- _ => dependent destruction H
    | H : a_wf_contd ?E (?C_C _ _) |- _ => dependent destruction H
    | H : a_wf_contd ?E (?C_C _ _ _) |- _ => dependent destruction H
    end.

#[export] Hint Constructors a_wf_wl : core.
#[export] Hint Constructors a_wl_red : core.
#[export] Hint Constructors apply_contd apply_conts : core.
#[export] Hint Constructors aworklist_subst : core.

Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with
    | H : (⊢ᵃʷ ?Γ) -> ?P |- _ => destruct_a_wf_wl;
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃʷ Γ) by auto;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2
    end.



(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)

Lemma awl_to_aenv_cons: forall Γ X t,
  awl_to_aenv (aworklist_constvar Γ X t) = (X,t) :: (awl_to_aenv Γ).
Proof.
  intros. simpl. auto.
Qed.

Lemma awl_to_aenv_app : forall Γ1 Γ2,
  awl_to_aenv (awl_app Γ1 Γ2) = (awl_to_aenv Γ1) ++ (awl_to_aenv Γ2).
Proof.
  intros. induction Γ1; simpl; eauto.
  all: rewrite* IHΓ1.
Qed.

Lemma awl_to_aenv_app_2 : forall Γ1 Γ2 X t,
  awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t)) = (awl_to_aenv Γ1 ++ [(X, t)] ++ awl_to_aenv Γ2).
Proof.
  intros. rewrite awl_to_aenv_app.
  rewrite_env (awl_to_aenv Γ1 ++ [(X, t)] ++ awl_to_aenv Γ2).
  reflexivity.
Qed.

Lemma awl_to_aenv_app_3 : forall Γ1 Γ2 X t,
  (X, t) :: awl_to_aenv (awl_app Γ1 Γ2) = awl_to_aenv (awl_app (aworklist_constvar Γ1 X t) Γ2).
Proof.
  intros. simpl. auto.
Qed.

Lemma dom_aenv_app_comm : forall (Σ1 Σ2: aenv),
  dom (Σ2 ++ Σ1) [=] dom Σ2 `union` (dom Σ1).
Proof.
  intros. induction Σ2; simpl; auto.
  - fsetdec.
  - destruct a; simpl. rewrite IHΣ2. fsetdec.
Qed.


Lemma worklist_split_etvar_det : forall Γ1 Γ2 Γ'1 Γ'2 X,
  X `notin` dom (awl_to_aenv Γ'2) `union`  dom (awl_to_aenv Γ'1) ->
  (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) = (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ'1) ->
  Γ2 = Γ'2 /\ Γ1 = Γ'1.
Proof.
  intros. generalize dependent Γ1.
  generalize dependent Γ'1. generalize dependent Γ'2.
  induction Γ2; simpl in *; intros.
  - destruct Γ'2; simpl in *; try dependent destruction H0.
    + intuition.
    + solve_notin_eq X0.
  - destruct Γ'2; simpl in *; try dependent destruction H0.
    + apply IHΓ2 in x; auto. destruct x; subst; auto.
  - destruct Γ'2; simpl in *; try dependent destruction H0.
    + rewrite awl_to_aenv_app in H; simpl in *;
      rewrite dom_aenv_app_comm in H; simpl in *.
      solve_notin_eq X.
    + apply IHΓ2 in x; auto. destruct x; subst; auto.
  - destruct Γ'2; simpl in *; try dependent destruction H0.
    + apply IHΓ2 in x; auto. destruct x; subst; auto.
Qed.

Lemma a_wf_wl_tvar_notin_remaining : forall Γ1 Γ2 X b,
  ⊢ᵃʷ (awl_app Γ2 (aworklist_constvar Γ1 X b)) ->
  X `notin` dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2).
Proof.
  intros. induction Γ2; try dependent destruction H; auto.
  - simpl in *. apply IHΓ2 in H1; auto.
    rewrite awl_to_aenv_app in H.
    rewrite dom_aenv_app_comm in H. simpl in *.
    auto.
  - simpl in *. apply IHΓ2 in H0; auto.
    rewrite awl_to_aenv_app in H.
    rewrite dom_aenv_app_comm in H. simpl in *.
    auto.
  - simpl in *. apply IHΓ2 in H0; auto.
    rewrite awl_to_aenv_app in H.
    rewrite dom_aenv_app_comm in H. simpl in *. auto.
  - simpl in *. apply IHΓ2 in H0; auto.
    rewrite awl_to_aenv_app in H.
    rewrite dom_aenv_app_comm in H. simpl in *. auto.
Qed.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.

Lemma a_wf_wl_weaken_atvar: forall Γ1 Γ2 X t,
  ⊢ᵃʷ awl_app Γ1 Γ2 -> X `notin` (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
  (~ exists A, t = abind_var_typ A) -> ⊢ᵃʷ awl_app Γ1 (aworklist_constvar Γ2 X t).
Proof with eauto; try autorewrite with core using solve_notin.
  introv H HN HE. induction Γ1; simpl in *.
  - destruct* t. solve_false.
  - inverts H. forwards~: IHΓ1.
    rewrite awl_to_aenv_app in H3.
    econstructor...
    rewrite awl_to_aenv_app in *. simpl.
    rewrite_env (awl_to_aenv Γ1 ++ (X ~ t) ++ awl_to_aenv Γ2)...
    apply a_wf_typ_weaken...
  - inverts H.
    all: rewrite awl_to_aenv_app in H2; forwards~: IHΓ1; econstructor...
  - inverts H.
    econstructor...
    + rewrite awl_to_aenv_app in *. simpl.
      rewrite_env (awl_to_aenv Γ1 ++ (X ~ t) ++ awl_to_aenv Γ2)...
      apply a_wf_work_weaken...
Qed.

Corollary a_wf_wl_weaken_cons: forall Γ X b,
  ⊢ᵃʷ Γ ->
  X `notin` (dom (awl_to_aenv Γ)) ->
  (~ exists A, b = abind_var_typ A) ->
  ⊢ᵃʷ aworklist_constvar Γ X b.
Proof with  simpl; solve_notin.
  intros.
  rewrite_env (awl_app aworklist_empty Γ) in H.
  rewrite_env (awl_app aworklist_empty (aworklist_constvar Γ X b)).
  applys* a_wf_wl_weaken_atvar...
Qed.

(* -- *)

Lemma awl_rewrite_middle : forall Γ1 Γ2 X,
    (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) = ((Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ Γ1).
Proof.
  introv. induction* Γ2; simpl; rewrite* IHΓ2.
Qed.

Lemma a_wf_wl_move_etvar_back : forall  Γ1 Γ2 X Y,
    ⊢ᵃʷ (Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
    ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1).
Proof with rewrite awl_to_aenv_app, awl_to_aenv_cons in *; try solve_notin.
  introv HW.
  inverts HW as FrY HX.
  forwards FrX: a_wf_wl_tvar_notin_remaining HX.
  rewrite awl_rewrite_middle in HX.
  rewrite awl_rewrite_middle.
  applys a_wf_wl_weaken_atvar HX...
  solve_false.
Qed.



Lemma subst_tvar_in_aworklist_bind_same : forall Γ X Y A b,
  ⊢ᵃʷ Γ ->
  binds Y b (awl_to_aenv Γ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds Y b (awl_to_aenv (subst_tvar_in_aworklist A X Γ)).
Proof with solve_false.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H. destruct_eq_atom.
    + inversion H2.
      * dependent destruction H4...
      * apply binds_cons; auto.
  - dependent destruction H; destruct_eq_atom; subst; simpl;
      try solve constructor; inversion H1; try dependent destruction H3; eauto.
  - destruct_eq_atom; dependent destruction H; auto.
Qed.


Lemma aworklist_app_assoc : forall Γ1 Γ2 Γ3,
    ((Γ1 ⧺ Γ2) ⧺ Γ3) = (Γ1 ⧺ Γ2 ⧺ Γ3).
Proof with simpl; auto.
  introv. induction Γ1...
  all: try rewrite IHΓ1...
Qed.


Lemma ftvar_in_work_apply_cont_eq : forall w A cs,
  apply_conts cs A w ->
  ftvar_in_work w [=] ftvar_in_typ A `union` ftvar_in_conts cs.
Proof.
  intros. induction H; simpl; fsetdec.
Qed.

Lemma a_wf_wl_apply_conts : forall Γ w A cs,
  apply_conts cs A w ->
  a_wf_wl (work_applys cs A ⫤ᵃ Γ) ->
  a_wf_wl (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
Qed.

Lemma a_wf_wl_apply_contd : forall Γ w A B cd,
  apply_contd cd A B w ->
  a_wf_wl (work_applyd cd A B ⫤ᵃ Γ) ->
  a_wf_wl (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
Qed.


Lemma a_wf_wl_wf_bind_typ : forall Γ x A,
  ⊢ᵃʷ Γ ->
  x ~ A ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A.
Proof with solve_false.
  introv WF HB. induction* WF.
  - inverts HB.
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj. inverts H2. subst.
      1-2: applys* a_wf_typ_weaken_cons...
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj...
      applys* a_wf_typ_weaken_cons...
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj...
      applys* a_wf_typ_weaken_cons...
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj...
      applys* a_wf_typ_weaken_cons...
Qed.


Lemma tvar_notin_awl_notin_bind_typ : forall X Γ x A,
  ⊢ᵃʷ Γ ->
  X `notin` ftvar_in_aworklist' Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ A.
Proof.
  intros. induction Γ; simpl in *; auto.
  - inversion H1.
    + dependent destruction H2; auto.
    + dependent destruction H; auto.
  - inversion H1.
    + dependent destruction H2; auto.
    + dependent destruction H; auto.
  - dependent destruction H; auto.
Qed.

Ltac destruct_wf_arrow :=
  match goal with
  | [ H : a_wf_typ _ (typ_arrow _ _) |- _ ] => dependent destruction H
  end.

Lemma aworklist_subst_remove_target_tvar : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  X `notin` dom (awl_to_aenv (subst_tvar_in_aworklist A X Γ2 ⧺ Γ1)).
Proof with eauto.
  intros. induction H1; simpl in *; auto.
  - dependent destruction H...
  - destruct_binds. destruct_a_wf_wl.
    assert (X <> Y). { unfold not. intros. subst. apply binds_dom_contradiction in H3... }
    simpl. eauto. 
  - destruct_binds. destruct_a_wf_wl.   
    simpl. eauto. 
  - destruct_binds. destruct_a_wf_wl. 
    simpl. eauto. 
  - dependent destruction H... 
  - dependent destruction H...
    destruct_binds...
  - apply IHaworklist_subst...
    apply a_wf_wl_move_etvar_back...
    rewrite awl_to_aenv_app; simpl...
Qed.

#[local] Hint Rewrite dom_app dom_cons : core.
#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.


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

Lemma a_wf_env_binds_a_wf_typ : forall Σ x A,
  a_wf_env Σ ->
  x ~ A ∈ᵃ Σ ->
  Σ ᵗ⊢ᵃ A.
Proof with eauto using a_wf_typ_weaken_cons.
  intros.
  dependent induction H; try destruct_binds...
  - inversion H0.
Qed.

Lemma aworklist_subst_binds_same_avar' : forall Γ1 Γ2 X b X1 A Γ'1 Γ'2,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2 ->
  X <> X1 ->
  binds X1 b (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) ->
  binds X1 (subst_tvar_in_abind A X b) (⌊ subst_tvar_in_aworklist A X Γ'2 ⧺ Γ'1 ⌋ᵃ).
Proof.
  intros. generalize dependent Γ1. generalize dependent Γ'1. generalize dependent Γ'2. induction Γ2; intros.
  - simpl in *. dependent destruction H0; simpl; auto.
    + inversion H2. dependent destruction H0. solve_notin_eq X1.
      destruct b; simpl in *; auto. destruct_a_wf_wl.
      apply a_wf_wl_a_wf_env in H0.
      apply a_wf_env_binds_a_wf_typ in H3; auto.
      destruct_binds.
      rewrite subst_tvar_in_typ_fresh_eq; auto.
      rewrite ftvar_in_a_wf_typ_upper with (Σ:=⌊ Γ1 ⌋ᵃ); auto.
    + solve_notin_eq X.
    + solve_notin_eq X.
  - dependent destruction H.
    dependent destruction H3. 
    simpl in *. destruct_binds; eauto.
  - dependent destruction H.
    + dependent destruction H2. destruct_binds; eauto.
    + dependent destruction H2. destruct_binds; eauto.
    + dependent destruction H2.
      * rewrite awl_to_aenv_app in H. simpl in H. solve_notin_eq X0.
      * simpl in *. destruct_binds; auto.
        apply binds_cons. eauto. 
      * apply worklist_split_etvar_det in x; auto.
        -- destruct x. subst. apply IHΓ2 in H2; auto.
           apply a_wf_wl_move_etvar_back; eauto.
           simpl in H5. rewrite awl_to_aenv_app in H5. simpl in H5.
           rewrite awl_to_aenv_app. simpl. destruct_binds; eauto.
           apply in_app_iff in H7. inversion H7; auto.
           destruct_in; eauto.
        -- apply a_wf_wl_tvar_notin_remaining in H0; auto.
  - dependent destruction H.
    dependent destruction H2.
    simpl in *. eauto.
Qed.



Lemma aworklist_subst_binds_same_atvar : forall Γ X b X1 A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  X ~ ⬒ ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  b = □ \/ b = ■ \/ b = ⬒ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  X <> X1 ->
  binds X1 b (⌊ Γ ⌋ᵃ) ->
  binds X1 b (⌊ subst_tvar_in_aworklist A X Γ2 ⧺ Γ1 ⌋ᵃ).
Proof.
  intros.
  apply aworklist_binds_split in H0. destruct H0 as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    replace b with (subst_tvar_in_abind A X b); auto. 
    eapply aworklist_subst_binds_same_avar'; eauto.
    intuition; subst; auto.
  auto.
Qed.


Lemma aworklist_subst_binds_same_var : forall Γ x X B A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  X ~ ⬒ ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  x <> X ->
  binds x (abind_var_typ B) (⌊ Γ ⌋ᵃ) ->
  binds x (abind_var_typ (subst_tvar_in_typ A X B)) (⌊ subst_tvar_in_aworklist A X Γ2 ⧺ Γ1 ⌋ᵃ).
Proof.
  intros.
  apply aworklist_binds_split in H0. destruct H0 as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    replace (abind_var_typ (subst_tvar_in_typ A X B)) with (subst_tvar_in_abind A X (abind_var_typ B)); auto. 
    eapply aworklist_subst_binds_same_avar'; eauto.
    auto.
Qed.

Lemma aworklist_subst_wf_typ : forall Γ X A B Γ1 Γ2,
  X ~ ⬒ ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  X ∉ ftvar_in_typ B ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ B ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᵗ⊢ᵃ B.
Proof with (autorewrite with core in *); simpl; eauto; solve_false; try solve_notin.
  introv HB HN WF HW HS.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction WF; auto; intros.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    apply a_wf_typ__tvar.
    eapply aworklist_subst_binds_same_atvar; eauto.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    apply a_wf_typ__stvar.
    eapply aworklist_subst_binds_same_atvar; eauto.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    apply a_wf_typ__etvar.
    eapply aworklist_subst_binds_same_atvar; eauto.
  - simpl in *. constructor; eauto.
  - intros. pick fresh X0 and apply a_wf_typ__all.
    now auto. subst.
    + inst_cofinites_with X0.
      replace ((X0 ~ abind_tvar_empty ++ awl_to_aenv (awl_app (subst_tvar_in_aworklist A X Γ2) Γ1)))
        with  ((awl_to_aenv (awl_app (subst_tvar_in_aworklist A X (aworklist_constvar Γ2 X0 abind_tvar_empty)) Γ1))) by auto.
      eapply H1 with (Γ:=aworklist_constvar Γ X0 abind_tvar_empty); auto.
      applys~ binds_cons_3.
      { simpl in HN. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. solve_notin. }
  - simpl in *. constructor; eauto.
  - simpl in *. constructor; eauto.
Qed.

Lemma aworklist_subst_wf_typ_subst : forall Γ X A B Γ1 Γ2,
  X ~ ⬒ ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ B ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᵗ⊢ᵃ {A ᵗ/ₜ X} B.
Proof with (autorewrite with core in *); simpl; eauto; solve_false; try solve_notin.
  introv HB HN WFA WFB HW HS.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction WFB; simpl in *; intros; eauto.
  - destruct (X == X0); subst.
    + simpl. destruct_eq_atom. eapply aworklist_subst_wf_typ; eauto.
    + simpl. destruct_eq_atom. eapply aworklist_subst_wf_typ; eauto. 
  - destruct (X == X0); subst.
    + simpl. destruct_eq_atom. eapply aworklist_subst_wf_typ; eauto.
    + simpl. destruct_eq_atom. eapply aworklist_subst_wf_typ; eauto.
  - destruct (X == X0); subst.
    + simpl. destruct_eq_atom. eapply aworklist_subst_wf_typ; eauto.
    + simpl. destruct_eq_atom. eapply aworklist_subst_wf_typ; eauto.
  - simpl in *. pick fresh X0 and apply a_wf_typ__all.
    + inst_cofinites_with X0. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
      apply s_in_subst_inv... eauto.
    + inst_cofinites_with X0. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
      replace (X0 ~ abind_tvar_empty ++ awl_to_aenv (subst_tvar_in_aworklist A X Γ2 ⧺ Γ1)) with
      (awl_to_aenv ((subst_tvar_in_aworklist A X (aworklist_constvar Γ2 X0 abind_tvar_empty) ⧺ Γ1))) by auto.
      eapply H1 with (Γ:=aworklist_constvar Γ X0 abind_tvar_empty); eauto...
      apply a_wf_typ_weaken_cons... eauto.
Qed.

Ltac unify_binds :=
  match goal with
  | H_1 : binds ?X ?b1 ?θ, H_2 : binds ?X ?b2 ?θ |- _ =>
    let H_3 := fresh "H" in 
    apply binds_unique with (a:=b2) in H_1 as H_3; eauto; dependent destruction H_3; subst
  end.

Lemma aworklist_subst_wf_exp_subst : forall Γ X A e Γ1 Γ2,
  X ~ ⬒ ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  a_wf_exp (⌊ Γ ⌋ᵃ) e ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_wf_exp (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) (subst_tvar_in_exp A X e)
with aworklist_subst_wf_body_subst : forall Γ X A b Γ1 Γ2,
  X ~ ⬒ ∈ᵃ (⌊ Γ ⌋ᵃ) ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  a_wf_body (⌊ Γ ⌋ᵃ) b ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_wf_body (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) (subst_tvar_in_body A X b).
Proof with eauto using aworklist_subst_wf_typ_subst.
  - intros *Hbinds Hnotin Hwfa Hwfe Hwfaw Haws. clear aworklist_subst_wf_exp_subst.
    generalize dependent Γ1. generalize dependent Γ2. dependent induction Hwfe; simpl in *; intros...  (* slow *)
    + simpl in *. eapply aworklist_subst_binds_same_var in H... unfold not. intros. subst. unify_binds.
    + simpl in *. inst_cofinites_for a_wf_exp__abs T:=({A ᵗ/ₜ X} T)...
      intros. inst_cofinites_with x.
      replace ( x ~ abind_var_typ ({A ᵗ/ₜ X} T) ++ ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) with 
                (⌊ {A ᵃʷ/ₜ X} (x ~ᵃ T ;ᵃ Γ2) ⧺ Γ1 ⌋ᵃ) by (simpl; auto).
      rewrite subst_tvar_in_exp_open_exp_wrt_typ_fresh2...
      assert (aworklist_subst (x ~ᵃ T ;ᵃ Γ) X A Γ1 (x ~ᵃ T ;ᵃ Γ2))...
      eapply H1 with (Γ:=(x ~ᵃ T ;ᵃ Γ)); simpl...  
      -- apply a_wf_typ_weaken_cons...
    + simpl in *. inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X0.
      * rewrite subst_tvar_in_body_open_body_wrt_typ_fresh2...
        apply s_in_b_subst_inv...
      * replace (X0 ~ □ ++ ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) with (⌊ {A ᵃʷ/ₜ X} (X0 ~ᵃ □ ;ᵃ Γ2) ⧺ Γ1 ⌋ᵃ) by (simpl; auto).
        rewrite subst_tvar_in_body_open_body_wrt_typ_fresh2...
        assert (aworklist_subst (X0 ~ᵃ □ ;ᵃ Γ) X A Γ1 (X0 ~ᵃ □ ;ᵃ Γ2))...
        eapply aworklist_subst_wf_body_subst with (Γ:=X0 ~ᵃ □ ;ᵃ Γ); simpl; eauto.
        -- apply a_wf_typ_weaken_cons...
  - intros *Hbinds Hnotin Hwfa Hwfb Hwfaw Haws. clear aworklist_subst_wf_body_subst.
    dependent destruction Hwfb; simpl in *...
Qed.


Lemma aworklist_subst_wf_contd_subst : forall Γ X A cd Γ1 Γ2,
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  a_wf_contd (awl_to_aenv Γ) cd ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_wf_contd (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) ({A ᶜᵈ/ₜ X} cd)
with aworklist_subst_wf_conts_subst : forall Γ X A cs Γ1 Γ2,
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  a_wf_conts (awl_to_aenv Γ) cs ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_wf_conts (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) ({A ᶜˢ/ₜ X} cs).
Proof with eauto 6 using aworklist_subst_wf_typ_subst, aworklist_subst_wf_exp_subst.
- intros *Hbinds Hnotin Hwfa Hwfc Hwfaw Haws. clear aworklist_subst_wf_contd_subst.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction Hwfc; intros; simpl in *... 
  + destruct_wf_arrow... 
- intros *Hbinds Hnotin Hwfa Hwfc Hwfaw Haws. clear aworklist_subst_wf_conts_subst.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction Hwfc; intros; simpl...
Qed.

Lemma aworklist_subst_wf_work_subst : forall Γ X A w Γ1 Γ2,
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  a_wf_work (awl_to_aenv Γ) w ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_wf_work (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) ({A ʷ/ₜ X} w).
Proof with eauto 8 using aworklist_subst_wf_typ_subst, aworklist_subst_wf_exp_subst, 
              aworklist_subst_wf_conts_subst, aworklist_subst_wf_contd_subst.
  intros. dependent destruction H2; simpl...
  - destruct_wf_arrow... 
  - destruct_wf_arrow... 
  - destruct_wf_arrow... 
    destruct_wf_arrow... 
    constructor...
Qed.

Lemma aworklist_subst_mono_typ : forall Γ X A T Γ1 Γ2,
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ T ->
  a_mono_typ (awl_to_aenv Γ) T ->
  ⊢ᵃʷ Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_mono_typ (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) T.
Proof with (autorewrite with core in *); simpl; eauto; solve_false; try solve_notin.
  intros * Hbinds Hnotin Hmono Hwf Hsubst.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction Hmono; auto; intros.
  - case_eq (X==X0); intros. { subst. simpl in Hnotin. solve_notin. }
    apply a_mono_typ__tvar.
    eapply aworklist_subst_binds_same_atvar; eauto.
  - case_eq (X==X0); intros. { subst. simpl in Hnotin. solve_notin. }
    apply a_mono_typ__etvar.
    eapply aworklist_subst_binds_same_atvar; eauto.
  - simpl in *. constructor; eauto.
Qed.

Lemma a_wf_typ_reorder_aenv : forall Σ Σ' A,
  a_wf_env Σ ->
  a_wf_env Σ' ->
  (forall X b, X `in` ftvar_in_typ A -> binds X b Σ -> binds X b Σ') ->
  Σ ᵗ⊢ᵃ A ->
  Σ' ᵗ⊢ᵃ A.
Proof.
  intros * Hwfenv1 Hwfenv2 Hbinds Hwfa. apply a_wf_typ_lc in Hwfa as Hlc. generalize dependent Σ. generalize dependent Σ'. 
  induction Hlc; intros; simpl in *; try solve [dependent destruction Hwfa; eauto].
  - dependent destruction Hwfa; eauto.
    constructor; eauto 6.
  - dependent destruction Hwfa. inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X; eauto. 
    eapply H0 with (Σ:=X ~ □ ++ Σ); eauto.
    intros. rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H4. apply union_iff in H4. destruct H4.
    + simpl in H4. apply singleton_iff in H4; subst. destruct_binds. auto.
      apply binds_dom_contradiction in H6. contradiction. auto. 
    + destruct_binds. apply binds_cons; eauto.
  - dependent destruction Hwfa; eauto.
    constructor; eauto 6.
  - dependent destruction Hwfa; eauto.
    constructor; eauto 6.
Qed.


Lemma aworklist_subst_wf_wl : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  X ∉ ftvar_in_typ A ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⊢ᵃʷ ({A ᵃʷ/ₜ X} Γ2 ⧺ Γ1).
Proof with eauto using a_wf_typ_strengthen_cons, a_wf_typ_strengthen_var_cons.
  intros. induction H3...
  - dependent destruction H...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite dom_aworklist_subst with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H;
        autorewrite with core in *...
      * destruct_a_wf_wl. eapply aworklist_subst_wf_typ_subst...
      * apply IHaworklist_subst; auto.
        dependent destruction H... 
        eapply a_wf_typ_strengthen_var_cons...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite dom_aworklist_subst with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * dependent destruction H... 
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite dom_aworklist_subst with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * dependent destruction H. apply IHaworklist_subst...
  - simpl in *. constructor.
    + dependent destruction H. eapply aworklist_subst_wf_work_subst...
    + dependent destruction H... 
  - simpl in *. destruct_binds.
    + constructor.
      * destruct_a_wf_wl.
        erewrite dom_aworklist_subst with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * apply IHaworklist_subst; auto.
        dependent destruction H; auto. eapply a_wf_typ_strengthen_cons; eauto.
  - simpl in *. destruct_binds.
    + apply IHaworklist_subst...
      apply a_wf_wl_move_etvar_back...
      * autorewrite with core in *...
      * eapply a_wf_typ_reorder_aenv with (Σ:=⌊ Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ); eauto.
        apply a_wf_wl_a_wf_env. apply a_wf_wl_move_etvar_back...
        autorewrite with core in *. simpl in *. intros.
        rewrite_env (((Y, ⬒) :: ⌊ Γ2 ⌋ᵃ) ++ (X, ⬒) :: ⌊ Γ1 ⌋ᵃ) in H6.
        apply binds_app_iff in H6; destruct H6; destruct_binds; eauto.
Qed.
