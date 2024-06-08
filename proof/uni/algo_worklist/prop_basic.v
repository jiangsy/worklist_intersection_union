Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.ltac_utils.


Open Scope aworklist_scope.
Open Scope abind_scope.


Lemma a_wf_twl_a_wf_env : forall Γ,
  ⊢ᵃʷₜ Γ ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  introv HW. induction* HW.
  all: cbn; econstructor; eauto.
Qed.


Lemma a_wf_twl_weaken_app : forall Γ1 Γ2,
  ⊢ᵃʷₜ (Γ2 ⧺ Γ1) ->
  ⊢ᵃʷₜ Γ1.
Proof.
  introv HW. induction Γ2; simpl in *; auto.
  - dependent destruction HW; auto.
  - dependent destruction HW; auto.
Qed.

Lemma a_wf_twl_a_wf_wl : forall Γ,
  ⊢ᵃʷₜ Γ ->
  ⊢ᵃʷₛ Γ.
Proof.
  auto.
Qed.

Lemma a_wf_wwl_uniq : forall Γ,
  a_wf_wwl Γ ->
  uniq (⌊ Γ ⌋ᵃ).
Proof.
  intros. induction H; simpl; auto.
Qed.

Lemma a_wf_twl_a_wf_wwl : forall Γ,
  a_wf_twl Γ ->
  a_wf_wwl Γ.
Proof.
  intros. induction H; simpl; auto.
Qed.

Lemma a_wf_wl_a_wf_wwl : forall Γ,
  a_wf_wl Γ ->
  a_wf_wwl Γ.
Proof.
  intros. induction H; simpl; auto.
  apply a_wf_twl_a_wf_wwl. auto.
Qed.


#[export] Hint Resolve a_wf_twl_a_wf_wl a_wf_wwl_uniq : core.

Lemma a_wf_wwl_a_wf_env : forall Γ,
  ⊢ᵃʷ Γ ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  introv HW. induction* HW; simpl; constructor; auto.
Qed.

Lemma a_wf_wl_a_wf_env : forall Γ,
  ⊢ᵃʷₛ Γ ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  introv HW. induction* HW.
  - apply a_wf_twl_a_wf_env; auto.
  - simpl. apply a_wf_env__stvar; auto.
  - simpl. apply a_wf_env__etvar; auto.
Qed.

Lemma a_wf_wl_weaken_app : forall Γ1 Γ2,
  ⊢ᵃʷₛ (Γ2 ⧺ Γ1) ->
  ⊢ᵃʷₛ Γ1.
Proof.
  introv HW. induction Γ2; simpl in *; auto.
  - dependent destruction HW; auto.
    dependent destruction H; assert (⊢ᵃʷₛ (Γ2 ⧺ Γ1)) by auto; auto.
  - dependent destruction HW; auto.
    dependent destruction H; assert (⊢ᵃʷₛ (Γ2 ⧺ Γ1)) by auto; auto.
Qed.

Lemma a_wf_wl_weaken_cons : forall Γ X b,
  ⊢ᵃʷₛ (X ~ᵃ b ; Γ) ->
  ⊢ᵃʷₛ Γ.
Proof.
  introv HW. replace (X ~ᵃ b ; Γ) with ((X ~ᵃ b ; aworklist_empty) ⧺ Γ) in HW by auto.
  apply a_wf_wl_weaken_app in HW. auto.
Qed.


Lemma a_wf_env_uniq : forall Σ,
  ⊢ᵃ Σ  ->
  uniq Σ.
Proof.
  intros. induction H; auto.
Qed.

Lemma a_wf_typ_lc : forall Σ A,
  Σ ᵗ⊢ᵃ A ->
  lc_typ A.
Proof.
  intros. induction H; auto.
Qed.

Lemma a_mono_typ_lc : forall Σ A,
  Σ ᵗ⊢ᵃₘ A ->
  lc_typ A.
Proof.
  intros. induction H; auto.
Qed.

#[global] Hint Resolve a_wf_typ_lc a_mono_typ_lc : core.

Lemma a_mono_typ_in_s_in : forall Σ A X,
  Σ ᵗ⊢ᵃₘ A ->
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
  Σ ᵗ⊢ᵃₘ A ->
  Σ ᵗ⊢ᵃ A.
Proof.
  intros. induction H; auto.
Qed.


Lemma a_wf_typ_weaken: forall Σ1 Σ2 Σ3 A,
  Σ3 ++ Σ1 ᵗ⊢ᵃ A ->
  Σ3 ++ Σ2 ++ Σ1 ᵗ⊢ᵃ A.
Proof.
  introv H. dependent induction H; eauto.
  - pick fresh X0 and apply a_wf_typ__all.
    + forwards*: H X0.
    + forwards*: H X0. forwards*: H0 X0.
      forwards*: H1 X0  Σ1 (X0 ~ abind_tvar_empty ++ Σ3); auto.
Qed.

Lemma a_wf_typ_weaken_app: forall Σ1 Σ2 A,
  Σ1 ᵗ⊢ᵃ A ->
  Σ2 ++ Σ1 ᵗ⊢ᵃ A.
Proof.
  intros. rewrite_env (nil ++ Σ2 ++ Σ1).
  apply a_wf_typ_weaken; auto.
Qed.

Corollary a_wf_typ_weaken_cons: forall Σ X t A,
  Σ ᵗ⊢ᵃ A ->
  (X, t) :: Σ ᵗ⊢ᵃ A.
Proof with simpl in *; try solve_notin.
  intros. simpl.
  rewrite_env (nil ++ (X ~ t) ++ Σ).
  apply a_wf_typ_weaken; auto...
Qed.


Lemma a_wf_exp_weaken: forall Σ1 Σ2 Σ3 e,
  Σ3 ++ Σ1 ᵉ⊢ᵃ e ->
  Σ3 ++ Σ2 ++ Σ1 ᵉ⊢ᵃ e.
Proof with eauto using a_wf_typ_weaken.
  intros. dependent induction H...
  - intros. apply a_wf_exp__abs with (T:=T)
    (L:=union L (union (dom Σ2) (union (dom Σ1) (union (dom Σ3) (ftvar_in_typ T)))))...
    intros. rewrite_env ((x ~ abind_var_typ T ++ Σ3) ++ Σ2 ++ Σ1).
    apply H1...
  - intros. inst_cofinites_for a_wf_exp__tabs... intros.
    inst_cofinites_with X.
    rewrite_env ((X ~ abind_tvar_empty ++ Σ3) ++ Σ2 ++ Σ1).
    eapply H1...
Qed.

Lemma a_wf_conts_weaken: forall Σ1 Σ2 Σ3 cs,
  Σ3 ++ Σ1 ᶜˢ⊢ᵃ cs ->
  Σ3 ++ Σ2 ++ Σ1 ᶜˢ⊢ᵃ cs
with a_wf_contd_weaken : forall Σ1 Σ2 Σ3 cd,
  Σ3 ++ Σ1 ᶜᵈ⊢ᵃ cd ->
  Σ3 ++ Σ2 ++ Σ1 ᶜᵈ⊢ᵃ cd.
Proof with eauto using a_wf_typ_weaken, a_wf_exp_weaken.
  - intros. dependent induction H; constructor...
  - intros. dependent induction H; constructor...
Qed.

Lemma a_wf_conts_weaken_cons : forall Σ X b cs,
  Σ ᶜˢ⊢ᵃ cs ->
  (X, b) :: Σ ᶜˢ⊢ᵃ cs.
Proof.
  intros.
  rewrite_env (nil ++ (X ~ b) ++ Σ).
  apply a_wf_conts_weaken; auto.
Qed.

Lemma a_wf_contd_weaken_cons : forall Σ X b cd,
  Σ ᶜᵈ⊢ᵃ cd -> 
  (X, b) :: Σ ᶜᵈ⊢ᵃ cd.
Proof.
  intros.
  rewrite_env (nil ++ (X ~ b) ++ Σ).
  apply a_wf_contd_weaken; auto.
Qed.

Lemma a_wf_work_weaken: forall Σ1 Σ2 Σ3 w,
  Σ3 ++ Σ1 ʷ⊢ᵃ w ->
  Σ3 ++ Σ2 ++ Σ1 ʷ⊢ᵃ w.
Proof with eauto using a_wf_typ_weaken, a_wf_exp_weaken, a_wf_conts_weaken, a_wf_contd_weaken.
  intros. dependent destruction H...
  constructor...
Qed.

Lemma a_wf_typ_strengthen: forall Σ1 Σ2 A X b,
  Σ2 ++ (X, b) :: Σ1 ᵗ⊢ᵃ A ->
  X ∉ ftvar_in_typ A ->
  Σ2 ++ Σ1 ᵗ⊢ᵃ A.
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
  (X, b) :: Σ ᵗ⊢ᵃ A ->
  X ∉ ftvar_in_typ A ->
  Σ ᵗ⊢ᵃ A.
Proof.
  intros. rewrite_env (nil ++ Σ).
  eapply a_wf_typ_strengthen; eauto.
Qed.

Lemma a_wf_typ_strengthen_var: forall Σ1 Σ2 A X B,
  Σ2 ++ (X, abind_var_typ B) :: Σ1 ᵗ⊢ᵃ A ->
  Σ2 ++ Σ1 ᵗ⊢ᵃ A.
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
  (X, abind_var_typ B) :: Σ ᵗ⊢ᵃ A ->
  Σ ᵗ⊢ᵃ A.
Proof.
  intros. rewrite_env (nil ++ Σ).
  eapply a_wf_typ_strengthen_var; eauto.
Qed.


Lemma a_mono_typ_strengthen_mtvar : forall Σ X b T,
  b = □ \/ b = ⬒ ->
  (X, b) :: Σ ᵗ⊢ᵃₘ T ->
  X `notin` ftvar_in_typ T ->
  Σ ᵗ⊢ᵃₘ T.
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
  (X, ■) :: Σ ᵗ⊢ᵃₘ T ->
  Σ ᵗ⊢ᵃₘ T.
Proof.
  intros. dependent induction H; eauto.
  - inversion H. dependent destruction H0.
    constructor; auto.
  - inversion H. dependent destruction H0.
    apply a_mono_typ__etvar; auto.
Qed.

Lemma a_mono_typ_strengthen_var : forall Σ x A T,
  (x, abind_var_typ A) :: Σ ᵗ⊢ᵃₘ T ->
  Σ ᵗ⊢ᵃₘ T.
Proof.
  intros. dependent induction H; eauto.
  - inversion H. dependent destruction H0.
    constructor; auto.
  - inversion H. dependent destruction H0.
    apply a_mono_typ__etvar; auto.
Qed.

Lemma a_wf_typ_var_binds_another : forall Σ1 x Σ2 A B1 B2,
  Σ2 ++ x ~ abind_var_typ B1 ++ Σ1 ᵗ⊢ᵃ A ->
  Σ1 ᵗ⊢ᵃ B2 ->
  Σ2 ++ x ~ abind_var_typ B2 ++ Σ1 ᵗ⊢ᵃ A.
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
  Σ2 ++ x ~ abind_var_typ A1 ++ Σ1 ᵉ⊢ᵃ e ->
  Σ1 ᵗ⊢ᵃ A2 ->
  Σ2 ++ x ~ abind_var_typ A2 ++ Σ1 ᵉ⊢ᵃ e.
Proof with eauto 5 using a_wf_typ_var_binds_another.
  intros. dependent induction H... (* slow *)
  - destruct (x==x0).
    + subst. econstructor...
    + apply binds_remove_mid in H; auto.
      econstructor...
  - inst_cofinites_for a_wf_exp__abs T:=T; intros; inst_cofinites_with x0; auto...
    rewrite_env ((x0 ~ abind_var_typ T ++ Σ2) ++ x ~ abind_var_typ A2 ++ Σ1); eauto.
    eapply H1 with (A1:=A1)...
  - inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X; auto...
    rewrite_env ((X ~ □ ++ Σ2) ++ x ~ abind_var_typ A2 ++ Σ1); eauto.
    eapply H1 with (A1:=A1)...
Qed.

Lemma a_wf_exp_var_binds_another_cons : forall Σ1 x e A1 A2,
  x ~ abind_var_typ A1 ++ Σ1 ᵉ⊢ᵃ e -> 
  Σ1 ᵗ⊢ᵃ A2 ->
  x ~ abind_var_typ A2 ++ Σ1 ᵉ⊢ᵃ e.
Proof.
  intros.
  rewrite_env (nil ++ x ~ abind_var_typ A2 ++ Σ1).
  eapply a_wf_exp_var_binds_another; eauto.
Qed.

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
    assert (ftvar_in_typ A [<=] ftvar_in_typ (A ᵗ^ₜ X)) by apply ftvar_in_typ_open_typ_wrt_typ_lower.
    simpl in *.
    fsetdec.
Qed.

Lemma a_wf_typ_rename_tvar : forall Σ1 Σ2 X Y A,
  Σ2 ++ X ~ □ ++ Σ1 ᵗ⊢ᵃ A  ->
  map (subst_typ_in_abind (typ_var_f Y) X ) Σ2 ++ Y ~ □ ++ Σ1 ᵗ⊢ᵃ { typ_var_f Y ᵗ/ₜ X } A.
Proof.
  intros. dependent induction H; simpl in *; destruct_eq_atom; auto.
  - constructor.
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (subst_typ_in_abind ` Y X) H0; eauto.
      * apply binds_cons_iff in H0. iauto.
  - apply a_wf_typ__stvar.
    forwards* [?|?]: binds_app_1 H.
    forwards: binds_map_2 (subst_typ_in_abind ` Y X) H0; eauto.
    apply binds_cons_iff in H0. iauto.
  - apply a_wf_typ__etvar.
    forwards* [?|?]: binds_app_1 H.
    forwards: binds_map_2 (subst_typ_in_abind ` Y X) H0; eauto.
    apply binds_cons_iff in H0. iauto.
  - inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
      apply s_in_subst_inv; auto.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
      rewrite_env (map (subst_typ_in_abind ` Y X) (X0 ~ □ ++ Σ2) ++ (Y, □) :: Σ1).
      apply H1; eauto.
Qed.


Lemma a_wf_exp_weaken_etvar_twice : forall x X1 X2 T e Γ,
  x ~ abind_var_typ T ++ ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ᵉ^^ₑ exp_var_f x ->
  (x, abind_var_typ ` X1) :: (X2, ⬒) :: (X1, ⬒) :: ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ᵉ^^ₑ exp_var_f x.
Proof.
  intros. apply a_wf_exp_var_binds_another_cons with (A1:=T); auto.
  rewrite_env ((x ~ abind_var_typ T) ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ).
  apply a_wf_exp_weaken; auto.
Qed.


Corollary a_wf_typ_rename_tvar_cons : forall Σ X Y A,
  X ~ □ ++ Σ ᵗ⊢ᵃ A  ->
  Y ~ □ ++ Σ ᵗ⊢ᵃ { typ_var_f Y ᵗ/ₜ X } A.
Proof.
  intros.
  rewrite_env ((map (subst_typ_in_abind (typ_var_f Y) X ) nil) ++ Y ~ abind_tvar_empty ++ Σ).
  apply a_wf_typ_rename_tvar; auto.
Qed.


Lemma a_wf_typ_subst : forall Σ1 X Σ2 A B,
  uniq (Σ2 ++ X ~ □ ++ Σ1) ->
  Σ2 ++ X ~ □ ++ Σ1 ᵗ⊢ᵃ A ->
  Σ1 ᵗ⊢ᵃ B ->
  map (subst_typ_in_abind B X) Σ2 ++ Σ1 ᵗ⊢ᵃ {B ᵗ/ₜ X} A.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2.
  intros * Huniq Hwft1 Hwft2.
  inductions Hwft1; intros; try solve [simpl; auto]...
  - destruct (X0 == X).
    + subst. simpl. apply a_wf_typ_weaken_app...
      (* solve_uniq. *)
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (subst_typ_in_abind B X) H0...
      * apply binds_cons_iff in H0. iauto.
  - destruct (X0 == X).
    + subst. simpl. apply a_wf_typ_weaken_app...
    + eapply a_wf_typ__stvar.
      forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (subst_typ_in_abind B X) H0.
      forwards* [(?&?&?)|?]: binds_cons_uniq_1 H0...
  - destruct (X0 == X).
      + subst. simpl. apply a_wf_typ_weaken_app...
      + eapply a_wf_typ__etvar.
        forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (subst_typ_in_abind B X) H0.
        forwards* [(?&?&?)|?]: binds_cons_uniq_1 H0...
  - simpl. inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
      applys* s_in_subst_inv...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
      replace ((X0, abind_tvar_empty) :: map (subst_typ_in_abind B X) Σ2 ++ Σ1)
      with (map (subst_typ_in_abind B X) ((X0, abind_tvar_empty) :: Σ2) ++ Σ1) by auto.
      apply H1; eauto...
  Unshelve. all: auto.
Qed.


Lemma a_wf_typ_all_open : forall Σ A B,
  uniq Σ ->
  Σ ᵗ⊢ᵃ typ_all A ->
  Σ ᵗ⊢ᵃ B ->
  Σ ᵗ⊢ᵃ A ᵗ^^ₜ B.
Proof.
  intros. dependent destruction H0.
  pick fresh X. inst_cofinites_with X.
  rewrite subst_typ_in_typ_intro with (X1:=X) (A2:=B); auto.
  rewrite_env (map (subst_typ_in_abind B X) nil ++ Σ).
  apply a_wf_typ_subst; auto.
Qed.


#[export] Hint Resolve a_mono_typ_wf a_wf_wl_a_wf_env a_wf_twl_a_wf_env a_wf_env_uniq : core.


Lemma a_wf_env_bind_a_wf_typ : forall Σ x A,
  ⊢ᵃ Σ ->
  binds x (abind_var_typ A) Σ ->
  Σ ᵗ⊢ᵃ A.
Proof.
  intros. induction H; simpl in *; try destruct_binds; 
  eauto using a_wf_typ_weaken_cons.
  inversion H0.
Qed.

Lemma a_wf_twl_a_wf_bind_typ : forall Γ x A,
  ⊢ᵃʷₜ Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A.
Proof with eauto.
  eauto using a_wf_env_bind_a_wf_typ.
Qed.


Lemma a_wf_wl_a_wf_bind_typ : forall Γ x A,
  ⊢ᵃʷₛ Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A.
Proof with eauto.
  eauto using a_wf_env_bind_a_wf_typ.
Qed.

Lemma awl_split_etvar : forall Γ X,
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  exists Γ1 Γ2, (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) = Γ.
Proof.
  intros. induction Γ.
  - inversion H.
  - simpl in *. destruct_binds. 
    + exists Γ, aworklist_empty; auto.
    + apply IHΓ in H1. destruct H1 as [Γ1 [Γ2 Heq]].
      exists Γ1, (aworklist_cons_var Γ2 X0 ab).
      rewrite <- Heq. auto.
  - simpl in *. apply IHΓ in H.
    destruct H as [Γ1 [Γ2 Heq]].
    exists Γ1, (w ⫤ᵃ Γ2). 
    rewrite <- Heq. auto.
Qed.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

Lemma a_wf_wl_strengthen_work : forall Γ w,
  ⊢ᵃʷₜ Γ ->
  ⌊ Γ ⌋ᵃ ʷ⊢ᵃ w ->
  ⊢ᵃʷₛ (w ⫤ᵃ Γ).
Proof.
  intros. dependent destruction H0; auto.
Qed.


Ltac destruct_a_wf_wl :=
  repeat
    lazymatch goal with
    | H : a_wf_wwl (aworklist_cons_work ?Γ ?w) |- _ => dependent destruction H
    | H : a_wf_wwl (aworklist_cons_var ?Γ ?w ?b) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_cons_work ?Γ ?w) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_cons_var ?Γ ?w ?b) |- _ => dependent destruction H
    | H : a_wf_twl (aworklist_cons_work ?Γ ?w) |- _ => dependent destruction H; solve_wf_twl_sub_false
    | H : a_wf_twl (aworklist_cons_var ?Γ ?w ?b) |- _ => dependent destruction H
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
    | H : (⊢ᵃʷₛ ?Γ) -> ?P |- _ => destruct_a_wf_wl;
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃʷₛ Γ) by auto;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2
    end.


Lemma awl_to_aenv_cons: forall Γ X b,
  ⌊ X ~ᵃ b ; Γ ⌋ᵃ = (X, b) :: ⌊ Γ ⌋ᵃ.
Proof.
  intros. simpl. auto.
Qed.

Lemma awl_to_aenv_app : forall Γ1 Γ2,
  ⌊ Γ1 ⧺ Γ2 ⌋ᵃ = ⌊ Γ1 ⌋ᵃ ++ ⌊ Γ2 ⌋ᵃ.
Proof.
  intros. induction Γ1; simpl; eauto.
  all: rewrite* IHΓ1.
Qed.

Lemma awl_to_aenv_app_2 : forall Γ1 Γ2 X b,
  ⌊ Γ1 ⧺ X ~ᵃ b ; Γ2 ⌋ᵃ = ⌊ Γ1 ⌋ᵃ ++ X ~ b ++ ⌊ Γ2 ⌋ᵃ.
Proof.
  intros. rewrite awl_to_aenv_app.
  rewrite_env (awl_to_aenv Γ1 ++ X ~ b ++ awl_to_aenv Γ2).
  reflexivity.
Qed.

Lemma awl_to_aenv_app_3 : forall Γ1 Γ2 X b,
  (X, b) :: ⌊ Γ1 ⧺ Γ2 ⌋ᵃ = ⌊ (X ~ᵃ b ; Γ1) ⧺ Γ2 ⌋ᵃ.
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
  X ∉ dom (⌊ Γ'2 ⌋ᵃ) `union` dom (⌊ Γ'1 ⌋ᵃ) ->
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
    + rewrite awl_to_aenv_app in H; simpl in *;
      rewrite dom_aenv_app_comm in H; simpl in *.
      solve_notin_eq X.
    + apply IHΓ2 in x; auto. destruct x; subst; auto.
  - destruct Γ'2; simpl in *; try dependent destruction H0.
    + apply IHΓ2 in x; auto. destruct x; subst; auto.
Qed.

Lemma a_wf_env_notin_remaining : forall Σ1 Σ2 X b,
  ⊢ᵃ (Σ2 ++ (X , b) :: Σ1) ->
  X ∉ dom Σ1 `union` dom Σ2.
Proof.
  intros. apply a_wf_env_uniq in H.
  apply uniq_notin_remaining in H...
  rewrite dom_app in H; auto.
Qed.

Lemma a_wf_wwl_tvar_notin_remaining : forall Γ1 Γ2 X b,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ b; Γ1) ->
  X ∉ dom (⌊ Γ1 ⌋ᵃ) `union` dom (⌊ Γ2 ⌋ᵃ).
Proof.
  intros. apply a_wf_wwl_uniq in H. rewrite awl_to_aenv_app in H. simpl in *.
  autorewrite with core in *. 
  apply uniq_notin_remaining in H. rewrite dom_app in H; auto.
Qed.

Lemma a_wf_twl_avar_notin_remaining : forall Γ1 Γ2 X b,
  ⊢ᵃʷₜ (Γ2 ⧺ X ~ᵃ b ; Γ1) ->
  X ∉ dom (⌊ Γ1 ⌋ᵃ) `union` dom (⌊ Γ2 ⌋ᵃ).
Proof.
  intros. apply a_wf_twl_a_wf_env in H.
  apply a_wf_env_uniq in H. rewrite awl_to_aenv_app in H. simpl in *.
  autorewrite with core in *. 
  apply uniq_notin_remaining in H. rewrite dom_app in H; auto.
Qed.

Lemma a_wf_wl_avar_notin_remaining : forall Γ1 Γ2 X b,
  ⊢ᵃʷₛ (Γ2 ⧺ X ~ᵃ b ; Γ1) ->
  X ∉ dom (⌊ Γ1 ⌋ᵃ) `union` dom (⌊ Γ2 ⌋ᵃ).
Proof.
  intros. apply a_wf_wl_a_wf_env in H.
  apply a_wf_env_uniq in H. rewrite awl_to_aenv_app in H. simpl in *.
  autorewrite with core in *. 
  apply uniq_notin_remaining in H. rewrite dom_app in H; auto.
Qed.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.

Lemma a_wf_env_weaken_atvar : forall Σ1 Σ2 X b,
  (~ exists A, b = abind_var_typ A) ->
  ⊢ᵃ (Σ2 ++ Σ1) ->
  X ∉ (dom (Σ2 ++ Σ1)) ->
  ⊢ᵃ (Σ2 ++ (X , b) :: Σ1).
Proof.
  intros. induction Σ2; simpl in *; eauto.
  - destruct b; constructor; auto. solve_false.
  - destruct a. destruct a0; dependent destruction H0; constructor; auto.
    rewrite_env (Σ2 ++ (X ~ b) ++ Σ1).
    apply a_wf_typ_weaken; auto.
Qed.

Lemma a_wf_wwl_weaken_etvar: forall Γ2 Γ1 X,
  ⊢ᵃʷ (Γ2 ⧺ Γ1) -> 
  X ∉ union (dom (⌊ Γ2 ⌋ᵃ)) (dom (⌊ Γ1 ⌋ᵃ)) ->
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof with eauto; try autorewrite with core using solve_notin.
  introv H HN. induction Γ2; simpl in *...
  - inverts H.
    + forwards~: IHΓ2.
      rewrite awl_to_aenv_app in H3.
      econstructor...
      rewrite awl_to_aenv_app in *. simpl.
      rewrite_env (awl_to_aenv Γ2 ++ (X ~ ⬒) ++ awl_to_aenv Γ1)...
      apply a_wf_typ_weaken...
    + rewrite awl_to_aenv_app in H2; forwards~: IHΓ2; econstructor...
    + rewrite awl_to_aenv_app in H2; forwards~: IHΓ2; econstructor...
    + rewrite awl_to_aenv_app in H2; forwards~: IHΓ2; econstructor...
  - inverts H.
    econstructor...
    + rewrite awl_to_aenv_app in *. simpl.
      rewrite_env (awl_to_aenv Γ2 ++ (X ~ ⬒) ++ awl_to_aenv Γ1)...
      apply a_wf_work_weaken...
Qed. 

Lemma a_wf_twl_weaken_etvar: forall Γ2 Γ1 X,
  ⊢ᵃʷₜ (Γ2 ⧺ Γ1) -> 
  X ∉ union (dom (⌊ Γ2 ⌋ᵃ)) (dom (⌊ Γ1 ⌋ᵃ)) ->
  ⊢ᵃʷₜ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof with eauto; try autorewrite with core using solve_notin.
  introv H HN. induction Γ2; simpl in *...
  - inverts H.
    + forwards~: IHΓ2.
      rewrite awl_to_aenv_app in H3.
      econstructor...
      rewrite awl_to_aenv_app in *. simpl.
      rewrite_env (awl_to_aenv Γ2 ++ (X ~ ⬒) ++ awl_to_aenv Γ1)...
      apply a_wf_typ_weaken...
    + rewrite awl_to_aenv_app in H2; forwards~: IHΓ2; econstructor...
    + rewrite awl_to_aenv_app in H2; forwards~: IHΓ2; econstructor...
  - inverts H.
    econstructor...
    + rewrite awl_to_aenv_app in *. simpl.
      rewrite_env (awl_to_aenv Γ2 ++ (X ~ ⬒) ++ awl_to_aenv Γ1)...
      apply a_wf_work_weaken...
Qed. 

Lemma a_wf_wl_weaken_etvar: forall Γ2 Γ1 X,
  ⊢ᵃʷₛ (Γ2 ⧺ Γ1) -> 
  X ∉  dom (⌊ Γ2 ⌋ᵃ) `union` dom (⌊ Γ1 ⌋ᵃ) ->
  ⊢ᵃʷₛ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof with eauto; try autorewrite with core using solve_notin.
  introv H HN. induction Γ2; simpl in *.
  - apply a_wf_wl__consetvar; auto.
  - dependent destruction H.
    + constructor. replace (X0 ~ᵃ ab ; Γ2 ⧺ X ~ᵃ ⬒;ᵃ Γ1) with ((X0 ~ᵃ ab; Γ2) ⧺ X ~ᵃ ⬒;ᵃ Γ1)...
      apply a_wf_twl_weaken_etvar...
    + apply a_wf_wl__consstvar; auto...
      rewrite awl_to_aenv_app in *... 
    + apply a_wf_wl__consetvar; auto...
      rewrite awl_to_aenv_app in *...
  - dependent destruction H.
    + dependent destruction H. constructor... constructor; auto.
      assert (⊢ᵃʷₛ (Γ2 ⧺ Γ1)); auto. 
      rewrite awl_to_aenv_app in *. simpl.
      rewrite_env (awl_to_aenv Γ2 ++ (X ~ ⬒) ++ awl_to_aenv Γ1)...
      apply a_wf_work_weaken...
      eapply a_wf_twl_weaken_etvar...
    + apply a_wf_wl__conswork_sub;
      rewrite awl_to_aenv_app in *; auto;
      rewrite_env (awl_to_aenv Γ2 ++ (X ~ ⬒) ++ awl_to_aenv Γ1);
      eapply a_wf_typ_weaken...
Qed.


Corollary a_wf_wl_weaken_etvar_cons: forall Γ X,
  ⊢ᵃʷₛ Γ ->
  X ∉ (dom (⌊ Γ ⌋ᵃ)) ->
  ⊢ᵃʷₛ (X ~ᵃ ⬒ ;ᵃ Γ).
Proof with  simpl; solve_notin.
  intros.
  rewrite_env (awl_app aworklist_empty Γ) in H.
  rewrite_env (awl_app aworklist_empty (X ~ᵃ ⬒;ᵃ Γ)).
  applys* a_wf_wl_weaken_etvar...
Qed.

(* -- *)

Lemma awl_rewrite_middle : forall Γ1 Γ2 X,
  (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) = ((Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ Γ1).
Proof.
  introv. induction* Γ2; simpl; rewrite* IHΓ2.
Qed.

Lemma a_wf_env_move_etvar_back : forall  Γ1 Γ2 X Y,
  ⊢ᵃ ⌊ Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ ->
  ⊢ᵃ ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ.
Proof with rewrite awl_to_aenv_app, awl_to_aenv_cons in *; try solve_notin.
  introv HW.
  inverts HW as FrY HX.
  - rewrite awl_to_aenv_app in *. simpl in *.
    rewrite_env ((⌊ Γ2 ⌋ᵃ ++ (X ~ ⬒)) ++ (Y , ⬒) :: ⌊ Γ1 ⌋ᵃ).
    apply a_wf_env_weaken_atvar; auto. solve_false.
    rewrite_env (⌊ Γ2 ⌋ᵃ ++ (X, ⬒) :: ⌊ Γ1 ⌋ᵃ); auto.
Qed.


Lemma a_wf_wwl_move_etvar_back : forall  Γ1 Γ2 X Y,
  ⊢ᵃʷ (Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1).
Proof with rewrite awl_to_aenv_app, awl_to_aenv_cons in *; try solve_notin.
  introv HW.
  inverts HW as FrY HX.
  - forwards FrX: a_wf_wwl_tvar_notin_remaining HX.
    rewrite awl_rewrite_middle in HX.
    rewrite awl_rewrite_middle.
    applys a_wf_wwl_weaken_etvar HX...
Qed.


Lemma a_wf_twl_move_etvar_back : forall  Γ1 Γ2 X Y,
  ⊢ᵃʷₜ (Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  ⊢ᵃʷₜ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1).
Proof with rewrite awl_to_aenv_app, awl_to_aenv_cons in *; try solve_notin.
  introv HW.
  inverts HW as FrY HX.
  - forwards FrX: a_wf_twl_avar_notin_remaining HX.
    rewrite awl_rewrite_middle in HX.
    rewrite awl_rewrite_middle.
    applys a_wf_twl_weaken_etvar HX...
Qed.


Lemma a_wf_wl_move_etvar_back : forall  Γ1 Γ2 X Y,
  ⊢ᵃʷₛ (Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  ⊢ᵃʷₛ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1).
Proof with rewrite awl_to_aenv_app, awl_to_aenv_cons in *; try solve_notin.
  introv HW.
  inverts HW as FrY HX.
  - constructor. apply a_wf_twl_move_etvar_back; auto.
  - forwards FrX: a_wf_wl_avar_notin_remaining HX.
    rewrite awl_rewrite_middle in HX.
    rewrite awl_rewrite_middle.
    applys a_wf_wl_weaken_etvar HX...
Qed.


Lemma subst_typ_in_aworklist_bind_same : forall Γ X Y A b,
  uniq (⌊ Γ ⌋ᵃ) ->
  binds Y b (⌊ Γ ⌋ᵃ) ->
  (~ exists A, b = abind_var_typ A) ->
  binds Y b (⌊ {A ᵃʷ/ₜ X} Γ ⌋ᵃ).
Proof with solve_false.
  intros. induction Γ; simpl in *; auto.
  - dependent destruction H. destruct_eq_atom.
    + destruct_binds.
      * destruct b; auto. solve_false.
      * apply binds_cons; auto.
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
  ⊢ᵃʷₜ (work_applys cs A ⫤ᵃ Γ) ->
  ⊢ᵃʷₛ (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
Qed.


Lemma a_wf_wl_apply_contd : forall Γ w A B cd,
  apply_contd cd A B w ->
  ⊢ᵃʷₛ (work_applyd cd A B ⫤ᵃ Γ) ->
  ⊢ᵃʷₛ (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
  eauto 6.
Qed.


Lemma a_wf_wwl_apply_conts : forall Γ w A cs,
  apply_conts cs A w ->
  ⊢ᵃʷ (work_applys cs A ⫤ᵃ Γ) ->
  ⊢ᵃʷ (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
Qed.


Lemma a_wf_wwl_apply_contd : forall Γ w A B cd,
  apply_contd cd A B w ->
  ⊢ᵃʷ (work_applyd cd A B ⫤ᵃ Γ) ->
  ⊢ᵃʷ (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
Qed.


Ltac destruct_wf_arrow :=
  match goal with
  | [ H : a_wf_typ _ (typ_arrow _ _) |- _ ] => dependent destruction H
  end.


Lemma aworklist_subst_remove_target_tvar : forall Γ X A Γ1 Γ2,
  uniq (⌊ Γ ⌋ᵃ) ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  X `notin` dom (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ).
Proof with eauto.
  intros * Huniq Hb Haws. induction Haws; simpl in *; auto.
  - dependent destruction Huniq...
  - destruct_binds. dependent destruction Huniq.
    assert (X <> Y)... { unfold not. intros. subst. apply binds_dom_contradiction in H0... }
  - destruct_binds. dependent destruction Huniq...
  - destruct_binds. dependent destruction Huniq...
  - destruct_binds. dependent destruction Huniq...
  - apply IHHaws...
    dependent destruction Huniq. auto.
    autorewrite with core in *. rewrite_env ((⌊ Γ2 ⌋ᵃ ++ (X ~ ⬒)) ++ (Y, ⬒) :: ⌊ Γ1 ⌋ᵃ).
    apply uniq_strengthen... rewrite_env (⌊ Γ2 ⌋ᵃ ++ (X, ⬒) :: ⌊ Γ1 ⌋ᵃ)...
    rewrite awl_to_aenv_app; simpl...
Qed.


#[local] Hint Rewrite dom_app dom_cons : core.
#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.


Lemma aworklist_subst_dom_eq : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 -> dom (⌊ Γ ⌋ᵃ) [=] 
    union (dom (⌊ Γ1 ⌋ᵃ)) (union (dom (⌊ {A ᵃʷ/ₜ X} Γ2 ⌋ᵃ)) (singleton X)).
Proof with simpl in *; fsetdec.
  introv HS. induction HS.
  - simpl. auto...
  - simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
    repeat rewrite KeySetProperties.add_union_singleton.
    fsetdec.
  - simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
    repeat rewrite KeySetProperties.add_union_singleton.
    clear H H0.
    fsetdec.
  - simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
    repeat rewrite KeySetProperties.add_union_singleton.
    clear H H0.
    fsetdec.
  - simpl. rewrite IHHS. fsetdec.
  - simpl. rewrite KeySetProperties.union_add. rewrite IHHS.
    repeat rewrite KeySetProperties.add_union_singleton.
    clear H H0.
    fsetdec.
  - simpl. rewrite awl_to_aenv_app, awl_to_aenv_cons in *.
    autorewrite with core in *. rewrite <- IHHS.
    rewrite AtomSetProperties.add_union_singleton.
    clear IHHS H0 H.
    fsetdec.
Qed.


Lemma a_wf_env_binds_a_wf_typ : forall Σ x A,
  ⊢ᵃ Σ ->
  x ~ A ∈ᵃ Σ ->
  Σ ᵗ⊢ᵃ A.
Proof with eauto using a_wf_typ_weaken_cons.
  intros.
  dependent induction H; try destruct_binds...
  - inversion H0.
Qed.


Lemma aworklist_subst_target_is_etvar : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  intros. induction H; simpl; auto.
  rewrite awl_to_aenv_app in *. simpl. auto. 
Qed.


Lemma aworklist_subst_binds_same_avar' : forall Γ1 Γ2 X b X1 A Γ'1 Γ'2,
  ⊢ᵃ ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ ->
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2 ->
  X <> X1 ->
  binds X1 b (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) ->
  binds X1 (subst_typ_in_abind A X b) (⌊ {A ᵃʷ/ₜ X} Γ'2 ⧺ Γ'1 ⌋ᵃ). 
Proof.
  intros. generalize dependent Γ1. generalize dependent Γ'1. generalize dependent Γ'2. induction Γ2; intros.
  - simpl in *. dependent destruction H0; simpl; auto.
    + destruct_binds.
      destruct b; simpl in *; auto. dependent destruction H. 
      apply a_wf_env_binds_a_wf_typ in H3 as Hwf; auto.
      rewrite subst_typ_in_typ_fresh_eq; auto.
      rewrite ftvar_in_a_wf_typ_upper with (Σ:=⌊ Γ1 ⌋ᵃ); auto.
    + solve_notin_eq X.
    + solve_notin_eq X.
  - dependent destruction H.
    + dependent destruction H2. destruct_binds; eauto.  
    + dependent destruction H2. destruct_binds; eauto.
    + dependent destruction H2.
      * rewrite awl_to_aenv_app in *. simpl in *. solve_notin_eq X0.
      * simpl in *. destruct_binds; auto.
        apply binds_cons. eauto.
      * apply worklist_split_etvar_det in x; auto.
        -- destruct x. subst. apply IHΓ2 in H2; auto.
           apply a_wf_env_move_etvar_back; auto. constructor; auto.
           simpl in H5. rewrite awl_to_aenv_app in H5. simpl in H5.
           rewrite awl_to_aenv_app. simpl. destruct_binds; eauto.
           apply in_app_iff in H7. inversion H7; auto.
           destruct_in; eauto.
        -- rewrite awl_to_aenv_app in H. simpl in H. 
           apply a_wf_env_notin_remaining in H. auto. 
    + dependent destruction H3. destruct_binds; eauto.
  - simpl in *. dependent destruction H0. simpl. eauto.
Qed.


Lemma aworklist_subst_binds_same_atvar : forall Γ X b X1 A Γ1 Γ2,
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  b = □ \/ b = ■ \/ b = ⬒ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  X <> X1 ->
  binds X1 b (⌊ Γ ⌋ᵃ) ->
  binds X1 b (⌊ subst_typ_in_aworklist A X Γ2 ⧺ Γ1 ⌋ᵃ).
Proof.
  intros.
  apply aworklist_subst_target_is_etvar in H1 as Hin.
  apply awl_split_etvar in Hin. destruct Hin as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    replace b with (subst_typ_in_abind A X b); auto.
    eapply aworklist_subst_binds_same_avar'; eauto.
    intuition; subst; auto.
Qed.


Lemma aworklist_subst_binds_same_var : forall Γ x X B A Γ1 Γ2,
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  x <> X ->
  x ~ B ∈ᵃ ⌊ Γ ⌋ᵃ ->
  x ~ {A ᵗ/ₜ X} B ∈ᵃ ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ.
Proof.
  intros.
  apply aworklist_subst_target_is_etvar in H0 as Hin.
  apply awl_split_etvar in Hin. destruct Hin as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    replace (abind_var_typ (subst_typ_in_typ A X B)) with (subst_typ_in_abind A X (abind_var_typ B)); auto.
    eapply aworklist_subst_binds_same_avar'; eauto.
Qed.


Lemma aworklist_subst_wf_typ : forall Γ X A B Γ1 Γ2,
  X ∉ ftvar_in_typ B ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ B ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᵗ⊢ᵃ B.
Proof with eauto.
  introv HN WF HW HS.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction WF; auto; intros...
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
      replace ((X0 ~ abind_tvar_empty ++ awl_to_aenv (awl_app (subst_typ_in_aworklist A X Γ2) Γ1)))
        with  ((awl_to_aenv (awl_app (subst_typ_in_aworklist A X (aworklist_cons_var Γ2 X0 abind_tvar_empty)) Γ1))) by auto.
      eapply H1 with (Γ:=aworklist_cons_var Γ X0 abind_tvar_empty); simpl; auto...
      { simpl in HN. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. solve_notin. }
      constructor...
  - simpl in *...
  - simpl in *...
Qed.


Lemma aworklist_subst_wf_typ_subst : forall Γ X A B Γ1 Γ2,
  X ∉ ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ B ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᵗ⊢ᵃ {A ᵗ/ₜ X} B.
Proof with eauto.
  introv HN WFA WFB HW HS.
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
    + inst_cofinites_with X0. rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
      apply s_in_subst_inv... eauto.
    + inst_cofinites_with X0. rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto...
      replace (X0 ~ □ ++ ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ) with  (⌊ {A ᵃʷ/ₜ X} (X0 ~ᵃ □;ᵃ Γ2) ⧺ Γ1 ⌋ᵃ) by auto.
      eapply H1 with (Γ:=aworklist_cons_var Γ X0 abind_tvar_empty); simpl; eauto...
      apply a_wf_typ_weaken_cons... constructor... 
Qed.


Ltac unify_binds :=
  match goal with
  | H_1 : binds ?X ?b1 ?θ, H_2 : binds ?X ?b2 ?θ |- _ =>
    let H_3 := fresh "H" in
    apply binds_unique with (a:=b2) in H_1 as H_3; eauto; dependent destruction H_3; subst
  end.


Lemma aworklist_subst_wf_exp_subst : forall Γ X A e Γ1 Γ2,
  X ∉ ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᵉ⊢ᵃ {A ᵉ/ₜ X} e.
Proof with eauto using aworklist_subst_wf_typ_subst.
  intros * Hnotin Hwfa Hwfe Hwfaw Haws. 
  generalize dependent Γ1. generalize dependent Γ2. dependent induction Hwfe; simpl in *; intros...  (* slow *)
  - simpl in *. eapply aworklist_subst_binds_same_var in H... unfold not. intros. subst.
    apply aworklist_subst_target_is_etvar in Haws. unify_binds.
  - simpl in *. inst_cofinites_for a_wf_exp__abs T:=({A ᵗ/ₜ X} T)...
    intros. inst_cofinites_with x.
    replace ( x ~ abind_var_typ ({A ᵗ/ₜ X} T) ++ ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) with
              (⌊ {A ᵃʷ/ₜ X} (x ~ᵃ T ;ᵃ Γ2) ⧺ Γ1 ⌋ᵃ) by (simpl; auto).
    rewrite subst_typ_in_exp_open_exp_wrt_exp_fresh2...
    assert (aworklist_subst (x ~ᵃ T ;ᵃ Γ) X A Γ1 (x ~ᵃ T ;ᵃ Γ2))...
    eapply H1 with (Γ:=(x ~ᵃ T ;ᵃ Γ)); simpl...
    + apply a_wf_typ_weaken_cons...
    + constructor; eauto.
  - simpl in *. inst_cofinites_for a_wf_exp__tabs; intros; inst_cofinites_with X0.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + replace (X0 ~ □ ++ ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) with (⌊ {A ᵃʷ/ₜ X} (X0 ~ᵃ □ ;ᵃ Γ2) ⧺ Γ1 ⌋ᵃ) by (simpl; auto).
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2...
      assert (aworklist_subst (X0 ~ᵃ □ ;ᵃ Γ) X A Γ1 (X0 ~ᵃ □ ;ᵃ Γ2))...
      eapply H1 with (Γ:=X0 ~ᵃ □ ;ᵃ Γ); simpl; eauto.
      * apply a_wf_typ_weaken_cons...
      * constructor; eauto.
Qed.


Lemma aworklist_subst_wf_contd_subst : forall Γ X A cd Γ1 Γ2,
  X ∉ ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cd ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᶜᵈ⊢ᵃ {A ᶜᵈ/ₜ X} cd
with aworklist_subst_wf_conts_subst : forall Γ X A cs Γ1 Γ2,
  X ∉ ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ cs ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ ᶜˢ⊢ᵃ {A ᶜˢ/ₜ X} cs.
Proof with eauto 6 using aworklist_subst_wf_typ_subst, aworklist_subst_wf_exp_subst.
  - intros * Hnotin Hwfa Hwfc Hwfaw Haws. clear aworklist_subst_wf_contd_subst.
    generalize dependent Γ1. generalize dependent Γ2. dependent induction Hwfc; intros; simpl in *...
    + destruct_wf_arrow...
  - intros * Hnotin Hwfa Hwfc Hwfaw Haws. clear aworklist_subst_wf_conts_subst.
    generalize dependent Γ1. generalize dependent Γ2. dependent induction Hwfc; intros; simpl...
Qed.

Lemma aworklist_subst_wf_work_subst : forall Γ X A w Γ1 Γ2,
  X ∉ ftvar_in_typ A ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  a_wf_work (⌊ Γ ⌋ᵃ) w ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_wf_work (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) ({A ʷ/ₜ X} w).
Proof with eauto 8 using aworklist_subst_wf_typ_subst, aworklist_subst_wf_exp_subst,
              aworklist_subst_wf_conts_subst, aworklist_subst_wf_contd_subst.
  intros. dependent destruction H1; simpl...
  - destruct_wf_arrow...
  - destruct_wf_arrow...
  - destruct_wf_arrow...
    destruct_wf_arrow...
    constructor...
Qed.

Lemma aworklist_subst_mono_typ : forall Γ X A T Γ1 Γ2,
  X ∉ ftvar_in_typ T ->
  a_mono_typ (⌊ Γ ⌋ᵃ) T ->
  ⊢ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  a_mono_typ (⌊ {A ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⌋ᵃ) T.
Proof with (autorewrite with core in *); simpl; eauto; solve_false; try solve_notin.
  intros * Hnotin Hmono Hwf Hsubst.
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
  ⊢ᵃ Σ ->
  ⊢ᵃ Σ' ->
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
    + simpl in H4. apply singleton_iff in H4; subst. destruct_binds; auto... 
      exfalso. eauto.
    + destruct_binds. apply binds_cons; eauto.
  - dependent destruction Hwfa; eauto.
    constructor; eauto 6.
  - dependent destruction Hwfa; eauto.
    constructor; eauto 6.
Qed.


Lemma aworklist_subst_wf_wwl : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  X ∉ ftvar_in_typ A ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⊢ᵃʷ ({A ᵃʷ/ₜ X} Γ2 ⧺ Γ1).
Proof with eauto using a_wf_typ_strengthen_cons, a_wf_typ_strengthen_var_cons.
  intros. induction H2...
  - dependent destruction H...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H;
        autorewrite with core in *...
      * destruct_a_wf_wl. eapply aworklist_subst_wf_typ_subst...
        apply a_wf_wwl_a_wf_env...
      * apply IHaworklist_subst; auto.
        dependent destruction H...
        eapply a_wf_typ_strengthen_var_cons...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * dependent destruction H...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * dependent destruction H...
  - simpl in *. dependent destruction H. constructor.
    + eapply aworklist_subst_wf_work_subst...
      apply a_wf_wwl_a_wf_env...
    + apply IHaworklist_subst; auto.
  - simpl in *. destruct_binds.
    + constructor.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * apply IHaworklist_subst; auto.
        dependent destruction H; auto. eapply a_wf_typ_strengthen_cons; eauto.
  - simpl in *. destruct_binds.
    + apply IHaworklist_subst...
      apply a_wf_wwl_move_etvar_back...
      * eapply a_wf_typ_reorder_aenv with (Σ:=⌊ Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ); eauto.
        apply a_wf_wwl_a_wf_env... apply a_wf_wwl_a_wf_env... apply a_wf_wwl_move_etvar_back...
        autorewrite with core in *. simpl in *. intros.
        rewrite_env (((Y, ⬒) :: ⌊ Γ2 ⌋ᵃ) ++ (X, ⬒) :: ⌊ Γ1 ⌋ᵃ) in H6.
        apply binds_app_iff in H6; destruct H6; destruct_binds; eauto.
Qed.



Lemma aworklist_subst_wf_twl : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷₜ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  X ∉ ftvar_in_typ A ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⊢ᵃʷₜ ({A ᵃʷ/ₜ X} Γ2 ⧺ Γ1).
Proof with eauto using a_wf_typ_strengthen_cons, a_wf_typ_strengthen_var_cons.
  intros. induction H2...
  - dependent destruction H...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H;
        autorewrite with core in *...
      * destruct_a_wf_wl. eapply aworklist_subst_wf_typ_subst...
      * apply IHaworklist_subst; auto.
        dependent destruction H...
        eapply a_wf_typ_strengthen_var_cons...
  - simpl. destruct_binds.
    + constructor; auto.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * dependent destruction H...
  - inversion H. 
  - simpl in *. dependent destruction H. constructor.
    + eapply aworklist_subst_wf_work_subst...
    + intro. destruct H5 as [A1 [B1]]. destruct w; simpl in H5; inversion H5.
      eauto.
    + apply IHaworklist_subst; auto.
  - simpl in *. destruct_binds.
    + constructor.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * apply IHaworklist_subst; auto.
        dependent destruction H; auto. eapply a_wf_typ_strengthen_cons; eauto.
  - simpl in *. destruct_binds.
    + apply IHaworklist_subst...
      apply a_wf_twl_move_etvar_back...
      * eapply a_wf_typ_reorder_aenv with (Σ:=⌊ Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ); eauto.
        apply a_wf_wl_a_wf_env. apply a_wf_wl_move_etvar_back...
        autorewrite with core in *. simpl in *. intros.
        rewrite_env (((Y, ⬒) :: ⌊ Γ2 ⌋ᵃ) ++ (X, ⬒) :: ⌊ Γ1 ⌋ᵃ) in H6.
        apply binds_app_iff in H6; destruct H6; destruct_binds; eauto.
Qed.


Lemma aworklist_subst_wf_wl : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷₛ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A ->
  X ∉ ftvar_in_typ A ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⊢ᵃʷₛ ({A ᵃʷ/ₜ X} Γ2 ⧺ Γ1).
Proof with eauto using a_wf_typ_strengthen_cons, a_wf_typ_strengthen_var_cons.
  intros. induction H2...
  - dependent destruction H...
    econstructor... eapply aworklist_subst_wf_twl; eauto.
  - dependent destruction H.
    constructor. eapply aworklist_subst_wf_twl; eauto.
  - dependent destruction H.
    constructor. eapply aworklist_subst_wf_twl; eauto.
  - simpl. destruct_binds.
    + apply a_wf_wl__consstvar; eauto. 
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * apply IHaworklist_subst... 
        eapply a_wf_wl_weaken_cons; eauto.
  - dependent destruction H.
    + constructor. eapply aworklist_subst_wf_twl; eauto. 
    + simpl. apply a_wf_wl__conswork_sub; auto.
      eapply aworklist_subst_wf_typ_subst with (Γ:=Γ); eauto.
      eapply aworklist_subst_wf_typ_subst with (Γ:=Γ); eauto.
  - dependent destruction H.
    + constructor. eapply aworklist_subst_wf_twl; eauto. 
    + simpl in *. apply a_wf_wl__consetvar.
      * destruct_a_wf_wl.
        erewrite aworklist_subst_dom_eq with (X:=X) (A:=A) (Γ1:=Γ1) (Γ2:=Γ2) in H...
        autorewrite with core in *...
      * destruct_binds. apply IHaworklist_subst; auto...
  - dependent destruction H.
    + constructor. eapply aworklist_subst_wf_twl; eauto.
    + apply IHaworklist_subst...
      apply a_wf_wl_move_etvar_back...
      * eapply a_wf_typ_reorder_aenv with (Σ:=⌊ Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ); eauto.
        apply a_wf_wl_a_wf_env. apply a_wf_wl_move_etvar_back...
        autorewrite with core in *. simpl in *. intros.
        rewrite_env (((Y, ⬒) :: ⌊ Γ2 ⌋ᵃ) ++ (X, ⬒) :: ⌊ Γ1 ⌋ᵃ) in H7.
        apply binds_app_iff in H7; destruct H7; destruct_binds; eauto.
Qed.


Open Scope aworklist_scope.

#[local] Hint Rewrite awl_to_aenv_cons awl_to_aenv_app: core.
#[local] Hint Rewrite dom_app dom_cons : core.


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
