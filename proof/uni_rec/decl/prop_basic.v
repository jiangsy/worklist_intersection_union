Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import uni_rec.notations.
Require Export uni_rec.prop_basic.
Require Import uni_rec.ltac_utils.

Open Scope dbind_scope.

Lemma d_wf_typ_lc_typ : forall Ψ A,
  Ψ ᵗ⊢ᵈ A -> lc_typ A.
Proof.
  intros; induction H; auto.
Qed.

Lemma d_mono_typ_d_wf_typ : forall Ψ T,
  Ψ ᵗ⊢ᵈₘ T -> Ψ ᵗ⊢ᵈ T.
Proof.
  intros. induction H; auto.
Qed.

Lemma d_mono_typ_lc : forall Ψ T,
  Ψ ᵗ⊢ᵈₘ T  -> lc_typ T.
Proof.
  intros; induction H; auto.
Qed.

#[global] Hint Resolve d_wf_typ_lc_typ d_mono_typ_lc : core.

Lemma d_mono_typ_d_wneq_all : forall Ψ A,
  d_mono_typ Ψ A ->
  d_wneq_all Ψ A.  
Proof.
  intros. induction H; eauto.
Qed.

Lemma d_wf_typ_stvar_tvar : forall Ψ1 Ψ2 X A,
  Ψ2 ++ (X ~ ■) ++ Ψ1 ᵗ⊢ᵈ A ->
  Ψ2 ++ (X ~ □) ++ Ψ1 ᵗ⊢ᵈ A.
Proof with eauto.
  intros Ψ1 Ψ2 X A H...
  dependent induction H...
  - apply binds_remove_mid_diff_bind in H...
    solve_false.
  - destruct (X0 == X). 
    + subst. eapply d_wf_typ__tvar...
    + apply binds_remove_mid in H...
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0...
    + rewrite_env ((X0 ~ □ ++ Ψ2) ++ (X, □) :: Ψ1).
      apply H1; eauto.
Qed.

Lemma d_wf_typ_tvar_stvar : forall Ψ1 Ψ2 X A,
  Ψ2 ++ (X ~ □) ++ Ψ1 ᵗ⊢ᵈ A ->
  Ψ2 ++ (X ~ ■) ++ Ψ1 ᵗ⊢ᵈ A.
Proof with eauto.
  intros Ψ1 Ψ2 X A H...
  dependent induction H...
  - destruct (X0 == X). 
    + subst. eapply d_wf_typ__stvar...
    + apply binds_remove_mid in H...
  - apply binds_remove_mid_diff_bind in H...
    solve_false.
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0...
    + rewrite_env ((X0 ~ □ ++ Ψ2) ++ (X, ■) :: Ψ1).
      apply H1; eauto.
Qed.

Corollary d_wf_typ_stvar_tvar_cons : forall Ψ X A,
  X ~ ■ ++ Ψ ᵗ⊢ᵈ A ->
  X ~ □ ++ Ψ ᵗ⊢ᵈ A.
Proof.
  intros.
  rewrite_env (nil ++ X ~ dbind_tvar_empty ++ Ψ).
  apply d_wf_typ_stvar_tvar; eauto.
Qed.

Corollary d_wf_typ_tvar_stvar_cons : forall Ψ X A,
  X ~ □ ++ Ψ ᵗ⊢ᵈ A ->
  X ~ ■ ++ Ψ ᵗ⊢ᵈ A.
Proof.
  intros.
  rewrite_env (nil ++ X ~ dbind_stvar_empty ++ Ψ).
  apply d_wf_typ_tvar_stvar; auto.
Qed.

Lemma d_wf_typ_open_inv : forall Ψ A B X,
  lc_typ B ->
  Ψ ᵗ⊢ᵈ {B ᵗ/ₜ X} A ->
  X ~ □ ∈ᵈ Ψ ->
  Ψ ᵗ⊢ᵈ A.
Proof with auto.
  intros. dependent induction H0; auto; try destruct A; simpl in *; 
    try solve [inversion x]; destruct_eq_atom; try inversion x; subst; try solve [constructor; auto; eauto 3].
  - eapply d_wf_typ__all with (L:=L `union` singleton X `union` ftvar_in_typ B); intros;
    inst_cofinites_with X0.
    * rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H2; auto.
      eapply s_in_subst; eauto.
    * eapply H1 with (X:=X) (B:=B); auto.
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; auto.
Qed.

Hint Constructors d_wf_typ: core.
Hint Constructors d_wf_env: core.

Lemma d_wf_typ_weaken : forall Ψ1 Ψ2 Ψ3 A,
  Ψ3 ++ Ψ1 ᵗ⊢ᵈ A ->
  Ψ3 ++ Ψ2 ++ Ψ1 ᵗ⊢ᵈ A.
Proof.
  intros.
  dependent induction H; auto.
  - eapply d_wf_typ__all with (L:=L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1));
    intros; inst_cofinites_with X.
    + auto.
    + rewrite_env ((X ~ dbind_tvar_empty ++ Ψ3) ++ Ψ2 ++ Ψ1).
      eapply H1; eauto.
Qed.

Corollary d_wf_typ_weaken_cons : forall Ψ X b A,
  Ψ ᵗ⊢ᵈ A ->
  ((X ~ b) ++ Ψ) ᵗ⊢ᵈ A.
Proof.
  intros.
  replace (X ~ b ++ Ψ) with (nil ++ X ~ b ++ Ψ) by auto.
  apply d_wf_typ_weaken; auto.
Qed.

Corollary d_wf_typ_weaken_app: forall Ψ1 Ψ2 A,
  Ψ1 ᵗ⊢ᵈ A ->
  Ψ2 ++ Ψ1 ᵗ⊢ᵈ A.
Proof.
  intros.
  rewrite_env (nil ++ Ψ2 ++ Ψ1).
  applys* d_wf_typ_weaken.
Qed.

Lemma d_wf_tenv_uniq: forall Ψ,
  ⊢ᵈₜ Ψ -> uniq Ψ.
Proof.
  intros.
  induction H; auto.
Qed.

Lemma d_wf_env_uniq: forall Ψ,
  ⊢ᵈ Ψ -> uniq Ψ.
Proof.
  intros.
  induction H; auto.
  apply d_wf_tenv_uniq; auto.
Qed.

#[export] Hint Resolve d_wf_env_uniq d_wf_tenv_uniq : core.

Lemma d_wf_tenv_strengthen_cons : forall a Ψ,
  ⊢ᵈₜ a :: Ψ -> ⊢ᵈₜ Ψ.
Proof with auto.
  intros * H.
  inverts* H.
Qed.

Lemma d_wf_env_strengthen_cons : forall a Ψ,
  ⊢ᵈ a :: Ψ -> ⊢ᵈ Ψ.
Proof with auto.
  intros * H.
  inverts* H.
  inversion H0; auto.
Qed.

Lemma d_wf_tenv_strengthen_app : forall Ψ1 Ψ2,
  ⊢ᵈₜ Ψ2 ++ Ψ1 -> ⊢ᵈₜ Ψ1.
Proof with auto.
  intros * H. induction Ψ2; auto. 
    dependent destruction H; auto.
Qed.

Lemma d_wf_env_strengthen_app : forall Ψ1 Ψ2,
  ⊢ᵈ Ψ2 ++ Ψ1 -> ⊢ᵈ Ψ1.
Proof with auto.
  intros * H. induction Ψ2; auto. 
    dependent destruction H; auto.
  inversion H; auto.
Qed.

#[local] Hint Resolve d_wf_typ_weaken_cons : core.

Lemma d_wf_tenv_binds_d_wf_typ : forall Ψ x A,
  ⊢ᵈₜ Ψ ->
  x ~ A ∈ᵈ Ψ ->
  Ψ ᵗ⊢ᵈ A.
Proof.
  intros.
  dependent induction H.
  - inversion H0.
  - simpl in H1. inversion H1.
    + inversion H2.
    + auto.
  - inversion H2.
    + dependent destruction H3. auto.
    + simpl in *. apply IHd_wf_tenv in H3.
      apply d_wf_typ_weaken_cons; auto.
Qed.

Lemma d_wf_env_binds_d_wf_typ : forall Ψ x A,
  ⊢ᵈ Ψ ->
  x ~ A ∈ᵈ Ψ ->
  Ψ ᵗ⊢ᵈ A.
Proof.
  intros.
  dependent induction H.
  - eapply d_wf_tenv_binds_d_wf_typ; eauto. 
  - simpl in H1. inversion H1.
    + inversion H2.
    + auto.
Qed.

Lemma subst_typ_in_denv_dtvar_binds_same : forall Ψ1 Ψ2 X Y A b b',
  (~ exists B, b = dbind_typ B) ->  
  (~ exists B', b' = dbind_typ B') ->  
  binds Y b (Ψ2 ++ X ~ b' ++ Ψ1) ->
  Y <> X ->
  binds Y b (map (subst_typ_in_dbind A X) Ψ2 ++ Ψ1).
Proof.
  intros.
  apply binds_app_iff in H1; eauto. 
  destruct H1.
  - apply binds_app_iff. left. apply binds_map with (f:=(subst_typ_in_dbind A X)) in H1; 
    destruct b; destruct b'; auto; solve_false.
  - inversion H1.
    + dependent destruction H3. contradiction.
    + apply binds_app_iff. auto.
Qed.
     
#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

Lemma d_wf_typ_subst_tvar : forall Ψ1 X Ψ2 A B,
  uniq (Ψ2 ++ X ~ □ ++ Ψ1) ->
  Ψ2 ++ X ~ □ ++ Ψ1 ᵗ⊢ᵈ A ->
  Ψ1 ᵗ⊢ᵈ B ->
  map (subst_typ_in_dbind B X) Ψ2  ++ Ψ1 ᵗ⊢ᵈ {B ᵗ/ₜ X} A.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; try solve [simpl; auto]...
  - destruct (X0 == X).
    + subst. simpl. applys* d_wf_typ_weaken_app.
      (* solve_uniq. *)
    + constructor. eapply subst_typ_in_denv_dtvar_binds_same with (b':=□)...
  - destruct (X0 == X).
    + apply d_wf_typ_weaken_app. auto.
    + eapply d_wf_typ__stvar.  
      eapply subst_typ_in_denv_dtvar_binds_same with (b':=□)...
  - simpl. inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
      applys* s_in_subst_inv...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
      replace ((X0, dbind_tvar_empty) :: map (subst_typ_in_dbind B X) Ψ2 ++ Ψ1)
      with (map (subst_typ_in_dbind B X) ((X0, dbind_tvar_empty) :: Ψ2) ++ Ψ1) by auto.
      apply H1; auto...
  Unshelve. all: auto.
Qed.

Lemma d_wf_typ_all_open : forall Ψ A B,
  uniq Ψ ->
  Ψ ᵗ⊢ᵈ typ_all A ->
  Ψ ᵗ⊢ᵈ B ->
  Ψ ᵗ⊢ᵈ A ᵗ^^ₜ B.
Proof.
  intros.
  inversion H0.
  inst_cofinites_by (L `union` ftvar_in_typ A `union` dom Ψ) using_name X.
  rewrite_env (map (subst_typ_in_dbind B X) nil ++ Ψ).
  erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
  apply d_wf_typ_subst_tvar; eauto.
Qed.

Lemma d_wf_typ_subst_stvar : forall Ψ1 X Ψ2 A B,
  uniq (Ψ2 ++ X ~ ■ ++ Ψ1) ->
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈ A ->
  Ψ1 ᵗ⊢ᵈ B ->
  map (subst_typ_in_dbind B X) Ψ2 ++ Ψ1 ᵗ⊢ᵈ {B ᵗ/ₜ X} A.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2, binds_app_1, binds_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; try solve [simpl; auto]...
  - destruct (X0 == X); subst...
    + apply d_wf_typ_weaken_app. auto.
    + eapply d_wf_typ__tvar... eapply subst_typ_in_denv_dtvar_binds_same with (b':= ■)... 
  - destruct (X0 == X); subst...
    + subst. simpl. applys* d_wf_typ_weaken_app.
      (* solve_uniq. *)
    + eapply d_wf_typ__stvar. eapply subst_typ_in_denv_dtvar_binds_same with (b':= ■)... 
  - simpl. inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
      applys* s_in_subst_inv.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_var...
      replace ((X0, dbind_tvar_empty) :: map (subst_typ_in_dbind B X) Ψ2 ++ Ψ1)
      with (map (subst_typ_in_dbind B X) ((X0, dbind_tvar_empty) :: Ψ2) ++ Ψ1) by auto.
      apply H1; auto...
  Unshelve. all: auto.
Qed.

Lemma ftvar_in_d_wf_typ_upper : forall Ψ A,
  d_wf_typ Ψ A ->
  ftvar_in_typ A [<=] dom Ψ.
Proof.
  intros; dependent induction H; try solve [simpl; fsetdec].
  - simpl. apply binds_In in H. fsetdec.
  - simpl. apply binds_In in H. fsetdec.
  - pick fresh X.
    inst_cofinites_with X.
    assert ((ftvar_in_typ A) [<=] (ftvar_in_typ (A ᵗ^ₜ X))) by apply ftvar_in_typ_open_typ_wrt_typ_lower.
    simpl in *.
    fsetdec.
Qed.

Corollary d_wf_typ_later_tvar_notin : forall X Ψ A,
  uniq ((X, □) :: Ψ) ->
  Ψ ᵗ⊢ᵈ A ->
  X ∉ ftvar_in_typ A.
Proof.
  intros. dependent destruction H. 
  rewrite ftvar_in_d_wf_typ_upper; eauto.
Qed.

Lemma d_wf_exp_lc_exp : forall Ψ e,
  d_wf_exp Ψ e -> 
  lc_exp e.
Proof with eauto using d_wf_typ_lc_typ.
  intros. dependent induction H...
Qed.

#[export] Hint Resolve d_wf_exp_lc_exp d_mono_typ_lc : core.

Lemma bind_typ_subst : forall Ψ2 X Ψ1 x A B,
  ⊢ᵈ Ψ2 ++ (X, dbind_tvar_empty) :: Ψ1 ->
  x ~ A ∈ᵈ (Ψ2 ++ (X, dbind_tvar_empty) :: Ψ1) ->
  Ψ1 ᵗ⊢ᵈ B ->
  x ~ ({B ᵗ/ₜ X} A) ∈ᵈ (map (subst_typ_in_dbind B X) Ψ2 ++ Ψ1).
Proof.
  intros. induction Ψ2; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (Ψ1 ᵗ⊢ᵈ A).
      {  eapply d_wf_env_binds_d_wf_typ; eauto. eapply d_wf_env_strengthen_cons; eauto. }
      rewrite subst_typ_in_typ_fresh_eq; auto.
      eapply d_wf_typ_later_tvar_notin; eauto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      apply IHΨ2; auto.
      eapply d_wf_env_strengthen_cons; eauto.
Qed.

Lemma d_mono_typ_weaken_app: forall Ψ1 Ψ2 T,
  Ψ1 ᵗ⊢ᵈₘ T -> 
  Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ T.
Proof.
  intros. induction* H.
Qed.

Lemma d_mono_typ_weaken : forall Ψ1 Ψ2 Ψ3 T,
  Ψ3 ++ Ψ1 ᵗ⊢ᵈₘ T -> 
  Ψ3 ++ Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ T.
Proof.
  intros.
  dependent induction H; auto.
Qed.

Lemma d_mono_typ_subst_mono_mono : forall Ψ1 Ψ2 T1 T2 X,
  Ψ2 ++ X ~ □ ++ Ψ1 ᵗ⊢ᵈₘ T1 ->
  Ψ1 ᵗ⊢ᵈₘ T2 ->
  map (subst_typ_in_dbind T2 X) Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ {T2 ᵗ/ₜ X} T1.
Proof with eauto using d_mono_typ_weaken_app; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction T1; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       inverts H.
       forwards* [?|?]: binds_app_1 H3. forwards*: binds_map_2 (subst_typ_in_dbind T2 X) H.
       forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
  }
  all: simpl; dependent destruction H; auto.
Qed.

Ltac unify_binds :=
  match goal with
  | H_1 : binds ?X ?b1 ?θ, H_2 : binds ?X ?b2 ?θ |- _ =>
    let H_3 := fresh "H" in 
    apply binds_unique with (a:=b2) in H_1 as H_3; eauto; dependent destruction H_3; subst
  end.

Lemma d_mono_typ_no_stvar : forall Ψ1 Ψ2 A X,
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈₘ A ->
  uniq (Ψ2 ++ X ~ ■ ++ Ψ1) ->
  X ∉ ftvar_in_typ A.
Proof with eauto using d_mono_typ_weaken_app; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction A; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       - inverts H.
         assert (X ~ ■ ∈ᵈ (Ψ2 ++ (X, ■) :: Ψ1 )) by eauto. unify_binds.
  }
  all: simpl; dependent destruction H; auto.
Qed.

Lemma d_mono_typ_strengthen : forall Ψ1 Ψ2 X b T,
  Ψ2 ++ (X, b) :: Ψ1 ᵗ⊢ᵈₘ T ->
  X ∉ ftvar_in_typ T ->
  Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ T.
Proof.
  intros. dependent induction H; eauto.
  - destruct b; simpl in *. 
    + apply binds_remove_mid in H; auto.
    + apply binds_remove_mid in H; auto.
    + apply binds_remove_mid in H; auto.
  - simpl in *. eauto.  
Qed.

Lemma d_mono_typ_strengthen_cons : forall Ψ X b T,
  (X, b) :: Ψ ᵗ⊢ᵈₘ T ->
  X ∉ ftvar_in_typ T ->
  Ψ ᵗ⊢ᵈₘ T.
Proof.
  intros. rewrite_env (nil ++ Ψ).
  eapply d_mono_typ_strengthen; eauto.
Qed.

Lemma d_mono_typ_strengthen_stvar : forall Ψ1 Ψ2 T X,
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈₘ T  ->
  Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ T.
Proof with eauto using d_mono_typ_weaken_app; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction T; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       - inverts H. forwards* [?|?]: binds_app_1 H2.
         forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
       - inverts H. forwards* [?|?]: binds_app_1 H2.
         forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
  }
  all: simpl; dependent destruction H; auto.
Qed.

Lemma d_mono_typ_stvar_tvar : forall Ψ1 Ψ2 T X,
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈₘ T ->
  Ψ2 ++ X ~ □ ++ Ψ1 ᵗ⊢ᵈₘ T.
Proof.
  intros. apply d_mono_typ_strengthen_stvar in H.
  apply d_mono_typ_weaken; auto.
Qed.

Lemma d_mono_typ_subst_stvar : forall Ψ1 Ψ2 A T X,
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈₘ A ->
  uniq (Ψ2 ++ X ~ ■ ++ Ψ1) ->
  Ψ1 ᵗ⊢ᵈ T ->
  map (subst_typ_in_dbind T X) Ψ2 ++ Ψ1 ᵗ⊢ᵈₘ {T ᵗ/ₜ X} A.
Proof with eauto using d_mono_typ_weaken_app; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction A; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       - inverts H.
         assert (X ~ ■ ∈ᵈ (Ψ2 ++ (X, ■) :: Ψ1)) by eauto.
         unify_binds.
       - inverts H.
         forwards* [?|?]: binds_app_1 H4... forwards*: binds_map_2 (subst_typ_in_dbind T X) H.
       forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
  }
  all: simpl; dependent destruction H; auto.
Qed.

Lemma d_sub_d_wf : forall Ψ A B,
  Ψ ⊢ A <: B -> 
  ⊢ᵈ Ψ /\ Ψ ᵗ⊢ᵈ A /\ Ψ ᵗ⊢ᵈ B.
Proof with auto.
  intros.
  induction H; try solve [intuition].
  - split.
    inst_cofinites_by L. intuition... eapply d_wf_env_strengthen_app; eauto. 
    split; eapply d_wf_typ__all with (L:=L `union` ftvar_in_typ A `union` ftvar_in_typ B); intros; inst_cofinites_with X; auto...
    eapply d_wf_typ_stvar_tvar_cons; intuition.
    eapply d_wf_typ_stvar_tvar_cons; intuition.
  - split; try solve [intuition].
    split; try solve [intuition].
    + eapply d_wf_typ__all with (L:=L `union` ftvar_in_typ A `union` dom Ψ).
      * intros. inst_cofinites_with X. auto.
      * intros. inst_cofinites_with X.
        destruct IHd_sub. auto.
        eapply d_wf_typ_open_inv with (X:=X) (B:=T); auto.
        -- eapply d_mono_typ_lc; eauto.
        -- replace (X ~ dbind_tvar_empty ++ Ψ) with (nil ++ X ~ dbind_tvar_empty ++ Ψ) by auto.
           apply d_wf_typ_weaken. simpl. rewrite  subst_typ_in_typ_open_typ_wrt_typ.
           ++ simpl. destruct_eq_atom. rewrite subst_typ_in_typ_fresh_eq; intuition.
           ++ eapply d_mono_typ_lc; eauto.
           (* ++ auto. *)
Qed.

Lemma d_sub_d_wf_env : forall Ψ A B,
    Ψ ⊢ A <: B -> ⊢ᵈ Ψ.
Proof.
  intros. forwards*: d_sub_d_wf H.
Qed.

Lemma d_sub_d_wf_typ1 : forall Ψ A B,
    Ψ ⊢ A <: B -> Ψ ᵗ⊢ᵈ A.
Proof.
  intros. forwards*: d_sub_d_wf H.
Qed.

Lemma d_sub_d_wf_typ2 : forall Ψ A B,
    Ψ ⊢ A <: B -> Ψ ᵗ⊢ᵈ B.
Proof.
  intros. forwards*: d_sub_d_wf H.
Qed.

Lemma d_infabs_d_wf : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  ⊢ᵈₜ Ψ /\ Ψ ᵗ⊢ᵈ A /\ Ψ ᵗ⊢ᵈ B /\ Ψ ᵗ⊢ᵈ C.
Proof.
  intros. induction H; intuition.
Qed.

Lemma d_infabs_d_wf_env : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  ⊢ᵈₜ Ψ.
Proof.
  intros. forwards*: d_infabs_d_wf H.
Qed.

Lemma d_infabs_d_wf_typ1 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ᵗ⊢ᵈ A.
Proof.
  intros. forwards*: d_infabs_d_wf H.
Qed.

Lemma d_infabs_d_wf_typ2 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ᵗ⊢ᵈ B.
Proof.
  intros. forwards*: d_infabs_d_wf H.
Qed.

Lemma d_infabs_d_wf_typ3 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ᵗ⊢ᵈ C.
Proof.
  intros. forwards*: d_infabs_d_wf H.
Qed.

Lemma d_inftapp_d_wf : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  ⊢ᵈₜ Ψ /\ Ψ ᵗ⊢ᵈ A /\ Ψ ᵗ⊢ᵈ B /\ Ψ ᵗ⊢ᵈ C.
Proof.
  intros. induction H; intuition.
  apply d_wf_typ_all_open; auto.
Qed.

Lemma d_inftapp_d_wf_env : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  ⊢ᵈₜ Ψ.
Proof.
  intros. forwards*: d_inftapp_d_wf H.
Qed.

Lemma d_inftapp_d_wf_typ1 : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ᵗ⊢ᵈ A.
Proof.
  intros. forwards*: d_inftapp_d_wf H.
Qed.

Lemma d_inftapp_d_wf_typ2 : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ᵗ⊢ᵈ B.
Proof.
  intros. forwards*: d_inftapp_d_wf H.
Qed.

Lemma d_inftapp_d_wf_typ3 : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ᵗ⊢ᵈ C.
Proof.
  intros. forwards*: d_inftapp_d_wf H.
Qed.

Lemma d_wf_typ_strengthen : forall Ψ1 Ψ2 X A b,
  uniq (Ψ2 ++ X ~ b ++ Ψ1) ->
  Ψ2 ++ X ~ b ++ Ψ1 ᵗ⊢ᵈ A ->
  X ∉ ftvar_in_typ A ->
  Ψ2 ++ Ψ1 ᵗ⊢ᵈ A.
Proof with eauto.
  intros * Huniq H. intros.
  dependent induction H; simpl in *; eauto.
  - induction Ψ2.
    + inversion H. dependent destruction H1.
      simpl in H0. apply notin_singleton_1 in H0. contradiction.
      auto.
    + destruct a. inversion H.
      * dependent destruction H1. auto.
      * simpl. apply d_wf_typ_weaken_cons. apply IHΨ2; auto.
        dependent destruction Huniq...
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - induction Ψ2.
    + inversion H. dependent destruction H1.
      * simpl in H0. apply notin_singleton_1 in H0. contradiction.
      * auto.
    + destruct a. inversion H.
      * dependent destruction H1. auto.
      * simpl. apply d_wf_typ_weaken_cons; auto. apply IHΨ2; auto.
        dependent destruction Huniq...
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - simpl in *.
    apply d_wf_typ__all with (L:=L `union` singleton X `union` dom Ψ1 `union` dom Ψ2); intros; inst_cofinites_with X0.
    + auto.
    + replace (X0 ~ dbind_tvar_empty ++ Ψ2 ++ Ψ1) with ((X0 ~ dbind_tvar_empty ++ Ψ2)++ Ψ1) by auto. eapply H1 with (X:=X) (b:=b); auto.
      * rewrite_env (X0 ~ dbind_tvar_empty ++ (Ψ2 ++ (X, b) :: Ψ1)). econstructor...
      * rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
Qed.

Lemma d_wf_typ_var_notin : forall Ψ x A B,
  uniq Ψ ->
  Ψ ᵗ⊢ᵈ A ->
  x ~ B ∈ᵈ Ψ -> 
  x ∉ ftvar_in_typ A.
Proof with auto using d_wf_env_uniq. 
  intros. induction H0; auto...
  - unfold not. intros. simpl in *. apply singleton_iff in H2. subst. 
    unify_binds. 
  - unfold not. intros. simpl in *. apply singleton_iff in H2. subst. 
    unify_binds. 
  - pick fresh X0. inst_cofinites_with X0.
    simpl. 
    rewrite <- ftvar_in_typ_open_typ_wrt_typ_lower in H3.
    auto.
Qed.

Lemma d_wf_typ_strengthen_var : forall Ψ1 Ψ2 x A B,
  uniq (Ψ2 ++ x ~ (dbind_typ B) ++ Ψ1) ->
  Ψ2 ++ x ~ (dbind_typ B) ++ Ψ1 ᵗ⊢ᵈ A ->
  Ψ2 ++ Ψ1 ᵗ⊢ᵈ A.
Proof with eauto.
  intros.
  eapply d_wf_typ_strengthen...
  eapply d_wf_typ_var_notin...
Qed.

Corollary d_wf_typ_strengthen_var_cons : forall Ψ x A B,
  uniq (x ~ (dbind_typ B) ++ Ψ) ->
  (x, dbind_typ B) :: Ψ ᵗ⊢ᵈ A ->
  Ψ ᵗ⊢ᵈ A.
Proof.
  intros. rewrite_env (nil ++ Ψ).
  eapply d_wf_typ_strengthen_var; eauto.
Qed.

Lemma d_chk_inf_wf : forall Ψ e A mode,
  d_chk_inf Ψ e mode A ->
  ⊢ᵈₜ Ψ /\ Ψ ᵗ⊢ᵈ A /\ d_wf_exp Ψ e.
Proof with eauto.
  intros. induction H; try solve [intuition].
  - intuition...
    apply d_wf_tenv_binds_d_wf_typ in H0...
  - intuition. apply d_infabs_d_wf_typ3 in H0...
  - intuition. apply d_infabs_d_wf_typ3 in H0...
  - repeat split.
    + inst_cofinites_by L. intuition. dependent destruction H2...
    + apply d_mono_typ_d_wf_typ... 
    + inst_cofinites_for d_wf_exp__abs T:=A.
      * inst_cofinites_by L. intuition. dependent destruction H2...
      * intros. inst_cofinites_with x. intuition. 
  - repeat split.
    + inst_cofinites_by L. intuition. dependent destruction H2... 
    + inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X; intuition.
    + inst_cofinites_for d_wf_exp__tabs.
      * intros. inst_cofinites_with X. auto. 
      * intros. inst_cofinites_with X. intuition.
  - intuition. eapply d_inftapp_d_wf_typ3...
  - repeat split. 
    + inst_cofinites_by L. intuition. dependent destruction H1...
    + inst_cofinites_by L. intuition. 
    + inst_cofinites_for d_wf_exp__abs T:=typ_bot...  
      intros. inst_cofinites_with x. intuition.
  - repeat split.
    + inst_cofinites_by L. intuition. dependent destruction H2...
    + inst_cofinites_by L. intuition. dependent destruction H2...
      constructor...
      eapply d_wf_typ_strengthen_var_cons...
    + inst_cofinites_for d_wf_exp__abs T:=A1... intros. 
      inst_cofinites_with x. intuition.
  - intuition. eapply d_sub_d_wf_typ2...
Qed.

Lemma d_chk_inf_wf_env : forall Ψ e A mode,
  d_chk_inf Ψ e mode A ->
  ⊢ᵈₜ Ψ.
Proof.
  intros. forwards*: d_chk_inf_wf H.
Qed.

Lemma d_chk_inf_wf_typ : forall Ψ e A mode,
  d_chk_inf Ψ e mode A ->
  Ψ ᵗ⊢ᵈ A.
Proof.
  intros. forwards*: d_chk_inf_wf H.
Qed.

Lemma d_wf_tenv_subst_tvar_typ : forall Ψ1 X Ψ2 A,
  ⊢ᵈₜ Ψ2 ++ X ~ □ ++ Ψ1 ->
  Ψ1 ᵗ⊢ᵈ A ->
  ⊢ᵈₜ (map (subst_typ_in_dbind A X) Ψ2 ++ Ψ1).
Proof with eauto using d_wf_typ_subst_tvar.
  intros * HE HA.
  induction Ψ2; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, d) :: (Ψ2 ++ X ~ □ ++ Ψ1)) in HE.
    forwards HE': d_wf_tenv_strengthen_cons HE.
    forwards~ IH: IHΨ2.
    rewrite_env ([(a, subst_typ_in_dbind A X d)]
                   ++ (map (subst_typ_in_dbind A X) Ψ2 ++ Ψ1)).
    dependent destruction HE...
    + econstructor...
Qed.

(* Properties of d_wf_env *)
Lemma d_wf_env_subst_tvar : forall Ψ1 X Ψ2 A,
  ⊢ᵈ Ψ2 ++ X ~ □ ++ Ψ1 ->
  Ψ1 ᵗ⊢ᵈ A ->
  ⊢ᵈ (map (subst_typ_in_dbind A X) Ψ2 ++ Ψ1).
Proof with eauto using d_wf_typ_subst_tvar.
  intros * HE HA.
  induction Ψ2; intros; simpl.
  - eapply d_wf_env_strengthen_app; eauto. 
  - destruct a. rewrite_env ((a, d) :: (Ψ2 ++ X ~ □ ++ Ψ1)) in HE.
    dependent destruction HE.
    + rewrite_env (map (subst_typ_in_dbind A X) ((a, d) :: Ψ2) ++ Ψ1).
      constructor; eapply d_wf_tenv_subst_tvar_typ; auto.
    + simpl. apply d_wf_env__stvar; auto.
Qed.

Lemma d_wf_tenv_stvar_false : forall Ψ1 Ψ2 X,
  ⊢ᵈₜ Ψ2 ++ (X , ■) :: Ψ1 -> False.
Proof.
  intros. induction Ψ2; auto.
  - inversion H.
  - simpl in *. apply d_wf_tenv_strengthen_cons in H; auto.
Qed.

Lemma d_wf_env_subst_stvar : forall Ψ1 X Ψ2 A,
  ⊢ᵈ Ψ2 ++ X ~ ■ ++ Ψ1 ->
  Ψ1 ᵗ⊢ᵈ A ->
  ⊢ᵈ (map (subst_typ_in_dbind A X) Ψ2 ++ Ψ1).
Proof with eauto using d_wf_typ_subst_tvar.
  intros * HE HT.
  induction Ψ2; intros; simpl.
  - eapply d_wf_env_strengthen_app; eauto. 
  - destruct a. destruct d; dependent destruction HE; simpl in *; auto.
    + exfalso. rewrite_env (((a, □) :: Ψ2) ++ (X, ■) :: Ψ1) in H. eapply d_wf_tenv_stvar_false; eauto.
    + inversion H.
    + apply d_wf_env__stvar; auto.
    + exfalso. rewrite_env (((a, dbind_typ A0) :: Ψ2) ++ (X, ■) :: Ψ1) in H. eapply d_wf_tenv_stvar_false; eauto.
Qed.

Corollary d_wf_tenv_weaken_tvar : forall Ψ1 Ψ2 X,
  ⊢ᵈₜ Ψ2 ++ Ψ1 ->
  X ∉ dom (Ψ2 ++ Ψ1) ->
  ⊢ᵈₜ Ψ2 ++ X ~ □ ++ Ψ1.
Proof with eauto.
  intros * HE HT. induction Ψ2; intros.
  - econstructor...
  - rewrite_env (a :: (Ψ2 ++ X ~ □ ++ Ψ1)). destruct a. destruct d.
    1: rewrite_env ((a, □) :: (Ψ2 ++ Ψ1)) in HE.
    2: rewrite_env ((a, ■) :: (Ψ2 ++ Ψ1)) in HE.
    3: rewrite_env ((a, dbind_typ A) :: (Ψ2 ++ Ψ1)) in HE.
    all: forwards HE': d_wf_tenv_strengthen_cons HE; inverts HE.
    all: econstructor; try solve_notin.
    applys d_wf_typ_weaken...
Qed.

Inductive all_stvar : list (atom * dbind) -> Prop :=
  | all_stvar_nil : all_stvar nil
  | all_stvar_cons : forall X Ψ,
      all_stvar Ψ ->
      all_stvar (X ~ ■ ++ Ψ).

Corollary d_wf_env_weaken_stvar : forall Ψ1 Ψ2 X,
  ⊢ᵈ Ψ2 ++ Ψ1 ->
  all_stvar Ψ2 -> 
  X ∉ dom (Ψ2 ++ Ψ1) ->
  ⊢ᵈ Ψ2 ++ X ~ ■ ++ Ψ1.
Proof with eauto.
  intros * HE HS HT. induction Ψ2; intros.
  - apply d_wf_env__stvar...
  - rewrite_env (a :: (Ψ2 ++ X ~ ■ ++ Ψ1)). destruct a. destruct d.
    + inversion HS.
    + simpl in *. dependent destruction HS. apply d_wf_env__stvar; eauto.
      apply IHΨ2; auto. apply d_wf_env_strengthen_cons in HE... dependent destruction HE.
      * dependent destruction H; auto.
      * auto.
    + inversion HS.
Qed.

Lemma subst_typ_in_typ_refl_eq : forall X A,
  {` X ᵗ/ₜ X} A = A.
Proof with (try progress case_if); subst; simpl; eauto.
  intros. induction A; simpl...
  all: try rewrite IHA; try rewrite IHA1; try rewrite IHA2...
Qed.

Lemma subst_typ_in_dbind_refl_eq : forall X b,
  subst_typ_in_dbind (` X) X b = b.
Proof with subst; try rewrite subst_typ_in_typ_refl_eq; simpl; eauto.
  intros. destruct b...
  induction* A...
Qed.

Lemma map_subst_typ_in_dbind_refl_eq : forall X Ψ,
  map (subst_typ_in_dbind (` X) X) Ψ = Ψ.
Proof with subst; try rewrite subst_typ_in_typ_refl_eq; simpl; eauto.
  intros. induction Ψ... destruct a...
  rewrite subst_typ_in_dbind_refl_eq. rewrite* IHΨ.
Qed.

Lemma map_subst_typ_in_dbind_dom_eq : forall T X Ψ,
  dom (map (subst_typ_in_dbind T X) Ψ) = dom Ψ.
Proof with simpl; eauto.
  intros *. induction* Ψ.
  - destruct a. destruct d...
    all: rewrite IHΨ...
Qed.

Lemma d_wf_typ_rename_dtvar : forall Ψ1 Ψ2 X Y A b,
  b = □ \/ b = ■ ->
  Ψ2 ++ X ~ b ++ Ψ1 ᵗ⊢ᵈ A  ->
  map (subst_typ_in_dbind (typ_var_f Y) X ) Ψ2 ++ Y ~ b ++ Ψ1 ᵗ⊢ᵈ { typ_var_f Y ᵗ/ₜ X } A.
Proof with try solve_notin; simpl in *; eauto.
  intros * Hb HT.
  case_eq (X==Y); intros.
  1: { subst. rewrite* map_subst_typ_in_dbind_refl_eq. rewrite subst_typ_in_typ_refl_eq... }
  clear H.
  inductions HT...
  - case_if...
    + subst. inversion Hb; subst. apply d_wf_typ__tvar... apply d_wf_typ__stvar...
    + apply binds_remove_mid in H...
      apply binds_app_iff in H. inversion H...
      * eapply binds_map_2  with (f:=(subst_typ_in_dbind ` Y X) ) in H0. simpl in *...
  - case_if...
    + subst. inversion Hb; subst. apply d_wf_typ__tvar... apply d_wf_typ__stvar...
    + apply binds_remove_mid in H...
      apply binds_app_iff in H. inversion H...
      * eapply binds_map_2  with (f:=(subst_typ_in_dbind ` Y X) ) in H0. simpl in *...
  - eapply d_wf_typ__all with (L:=L `union` singleton X); intros; inst_cofinites_with X0.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
      apply s_in_subst_inv; auto.
    + intros.
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
      rewrite_env (map (subst_typ_in_dbind ` Y X) (X0 ~ □ ++ Ψ2) ++ (Y, b) :: Ψ1).
      auto.
Qed.

Lemma d_wf_typ_rename_stvar : forall Ψ1 Ψ2 X Y A,
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈ A  ->
  map (subst_typ_in_dbind (typ_var_f Y) X ) Ψ2 ++ Y ~ ■ ++ Ψ1 ᵗ⊢ᵈ { typ_var_f Y ᵗ/ₜ X } A.
Proof with try solve_notin; simpl in *; eauto.
  intros. eapply d_wf_typ_rename_dtvar; eauto.
Qed.

Lemma d_wf_typ_rename_tvar : forall Ψ1 Ψ2 X Y A,
  Ψ2 ++ X ~ □ ++ Ψ1 ᵗ⊢ᵈ A  ->
  map (subst_typ_in_dbind (typ_var_f Y) X ) Ψ2 ++ Y ~ □ ++ Ψ1 ᵗ⊢ᵈ { typ_var_f Y ᵗ/ₜ X } A.
Proof with try solve_notin; simpl in *; eauto.
  intros. eapply d_wf_typ_rename_dtvar; eauto.
Qed.

Lemma d_wf_typ_rename_stvar_cons : forall Ψ X Y A,
  X ~ ■ ++ Ψ ᵗ⊢ᵈ A  ->
  Y ~ ■ ++ Ψ ᵗ⊢ᵈ { typ_var_f Y ᵗ/ₜ X } A.
Proof with try solve_notin; simpl in *; eauto.
  intros. rewrite_env (map (subst_typ_in_dbind (typ_var_f Y) X ) nil ++ Y ~ ■ ++ Ψ). 
  eapply d_wf_typ_rename_stvar; eauto.
Qed.

Lemma d_wf_typ_rename_tvar_cons : forall Ψ X Y A,
  X ~ □ ++ Ψ ᵗ⊢ᵈ A  ->
  Y ~ □ ++ Ψ ᵗ⊢ᵈ { typ_var_f Y ᵗ/ₜ X } A.
Proof with try solve_notin; simpl in *; eauto.
  intros. rewrite_env (map (subst_typ_in_dbind (typ_var_f Y) X ) nil ++ Y ~ □ ++ Ψ).
  eapply d_wf_typ_rename_tvar; eauto.
Qed.

Lemma d_wf_tenv_rename_tvar : forall Ψ1 Ψ2 X Y,
  ⊢ᵈₜ (Ψ2 ++ (X, □) :: Ψ1) ->
  Y ∉ dom (Ψ2 ++ (X, □) :: Ψ1) ->
  ⊢ᵈₜ (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, □) :: Ψ1).
Proof with eauto using d_wf_typ_rename_tvar.
  intros. induction Ψ2; simpl in *; auto. 
  - dependent destruction H; constructor...
  - dependent destruction H; try solve [constructor; eauto].
    + simpl. constructor...
      eapply d_wf_typ_rename_dtvar; eauto... 
Qed.

Lemma d_wf_tenv_rename_tvar_cons : forall Ψ X Y,
  ⊢ᵈₜ (X, □) :: Ψ ->
  Y ∉ dom ((X, □) :: Ψ) ->
  ⊢ᵈₜ (Y, □) :: Ψ. 
Proof with eauto using d_wf_typ_rename_tvar.
  intros. rewrite_env ((map (subst_typ_in_dbind `Y X) nil ++ (Y, □) :: Ψ)).
  apply d_wf_tenv_rename_tvar; eauto.
Qed.

Lemma d_wf_env_rename_dtvar : forall Ψ1 Ψ2 X Y b,
  b = □ \/ b = ■  ->
  ⊢ᵈ (Ψ2 ++ (X, b) :: Ψ1) ->
  Y ∉ dom (Ψ2 ++ (X, b) :: Ψ1) ->
  ⊢ᵈ (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, b) :: Ψ1).
Proof with eauto using d_wf_typ_rename_tvar.
  intros. induction Ψ2; simpl in *; auto. 
  - destruct H; subst.
    + dependent destruction H0. constructor. eapply d_wf_tenv_rename_tvar_cons; eauto.
    + apply d_wf_env__stvar; auto. apply d_wf_env_strengthen_cons in H0; auto.
  - destruct a; destruct d; simpl.
    + dependent destruction H0. constructor. destruct H; subst.
      * rewrite_env (map (subst_typ_in_dbind ` Y X) ((a, □) :: Ψ2) ++ (Y, □) :: Ψ1).
        apply d_wf_tenv_rename_tvar; eauto.
      * rewrite_env (((a, □) :: Ψ2) ++ (X, ■) :: Ψ1) in H0. 
        apply d_wf_tenv_stvar_false in H0. contradiction.
    + dependent destruction H0.
      * inversion H0.
      * apply d_wf_env__stvar. auto. auto.
    + dependent destruction H0. destruct H; subst.
      * constructor. rewrite_env (map (subst_typ_in_dbind ` Y X) ((a, dbind_typ A) :: Ψ2) ++ (Y, □) :: Ψ1).
        apply d_wf_tenv_rename_tvar; eauto.
      * rewrite_env (((a, dbind_typ A) :: Ψ2) ++ (X, ■) :: Ψ1) in H0. 
        apply d_wf_tenv_stvar_false in H0. contradiction.
Qed.

Corollary d_wf_env_rename_stvar : forall Ψ1 X Ψ2 Y,
  ⊢ᵈ Ψ2 ++ X ~ ■ ++ Ψ1 ->
  Y ∉ dom (Ψ2 ++ Ψ1) ->
  ⊢ᵈ map (subst_typ_in_dbind (typ_var_f Y) X) Ψ2 ++ Y ~ ■ ++ Ψ1.
Proof.
  intros. destruct (X == Y).
  - subst. auto. rewrite map_subst_typ_in_dbind_refl_eq; auto.
  - eapply d_wf_env_rename_dtvar; auto.
Qed.

Lemma d_mono_typ_rename_dtvar : forall Ψ1 Ψ2 X X' b T,
  uniq (Ψ2 ++ X ~ b ++ Ψ1) -> 
  X' ∉ (dom (Ψ2 ++ Ψ1)) ->
  b = □ \/ b = ■ ->
  d_mono_typ (Ψ2 ++ X ~ b ++ Ψ1) T ->
  d_mono_typ (map (subst_typ_in_dbind ` X' X) Ψ2 ++ (X', b) :: Ψ1) ({`X' ᵗ/ₜ X} T).
Proof with simpl in *; eauto.
  intros. dependent induction H2...
  - destruct (X0 == X).
    + subst. econstructor...
      apply binds_mid_eq in H2...
    + econstructor. 
      apply binds_remove_mid in H2...
      rewrite_env (map (subst_typ_in_dbind ` X' X) Ψ2 ++ (X' ~ b) ++ Ψ1).
      apply binds_weaken...
      apply binds_app_iff in H2. destruct H2...
      * apply binds_map_2 with (f:=subst_typ_in_dbind ` X' X) in H2...
Qed.

Lemma d_mono_typ_rename_tvar : forall Ψ1 Ψ2 X X' T,
  uniq (Ψ2 ++ X ~ □ ++ Ψ1) -> 
  X' ∉ (dom (Ψ2 ++ Ψ1)) ->
  d_mono_typ (Ψ2 ++ X ~ □ ++ Ψ1) T ->
  d_mono_typ (map (subst_typ_in_dbind ` X' X) Ψ2 ++ (X', □) :: Ψ1) ({`X' ᵗ/ₜ X} T).
Proof with simpl in *; eauto.
  intros. apply d_mono_typ_rename_dtvar...
Qed.

Lemma d_mono_typ_rename_stvar : forall Ψ1 Ψ2 X X' T,
  uniq (Ψ2 ++ X ~ ■ ++ Ψ1) -> 
  X' ∉ (dom (Ψ2 ++ Ψ1)) ->
  d_mono_typ (Ψ2 ++ X ~ ■ ++ Ψ1) T ->
  d_mono_typ (map (subst_typ_in_dbind ` X' X) Ψ2 ++ (X', ■) :: Ψ1) ({`X' ᵗ/ₜ X} T).
Proof with simpl in *; eauto.
  intros. apply d_mono_typ_rename_dtvar...
Qed.

Lemma lc_typ_open_stvar_subst_mono : forall A Ψ T X,
  lc_typ (A ᵗ^^ₜ T) -> d_mono_typ Ψ T -> lc_typ (A ᵗ^ₜ X).
Proof with try solve_notin; try solve_by_invert; simpl in *; eauto.
  intros * HD HM.
  inductions HD.
  all: destruct A; destruct T; unfold open_typ_wrt_typ in *; inverts x; subst; simpl in *...
  all: try destruct (lt_eq_lt_dec n 0); try case_if; try solve [inverts~ x].
  all: eauto...
  all: eapply lc_typ_all; intro Y;
      forwards: H Y; unfold open_typ_wrt_typ;
      rewrite open_typ_wrt_typ_twice; rewrite open_typ_wrt_typ_twice in H1;
    try applys H0; try rewrite open_typ_wrt_typ_twice...
Qed.

Lemma s_in_subst_mono_inv : forall A T Ψ X Y,
  s_in X (A ᵗ^^ₜ T) -> 
  d_mono_typ Ψ T -> 
  X ∉ ftvar_in_typ T -> 
  s_in X (A ᵗ^ₜ Y).
Proof with try solve_notin; try solve_by_invert; simpl in *; eauto using lc_typ_open_stvar_subst_mono.
  intros * HD HM HN.
  inductions HD.
  all: destruct A; destruct T; unfold open_typ_wrt_typ in *; simpl in *; inverts x; subst;
    try destruct (lt_eq_lt_dec n 0); try case_if; try solve [inverts~ x];
    try solve [inverts H0; solve_notin]...
  all: try solve [inverts H1; inverts HM;
                  try solve [forwards*: IHHD (typ_var_b 0) T1];
                  try solve [forwards*: IHHD (typ_var_b 0) T2]].
  all: try solve [
           pick fresh Z and apply s_in__all; inst_cofinites_with Z;
           rewrite open_typ_wrt_typ_twice in H0;
           [ forwards*: H0 | ];
           unfold open_typ_wrt_typ; try rewrite open_typ_wrt_typ_twice;
           eauto using lc_typ_open_stvar_subst_mono ].
  all: try solve [
           inverts H0; inverts HM;
                  forwards*: IHHD1 (typ_var_b 0) T1;
                  forwards*: IHHD2 (typ_var_b 0) T2 ].
Qed.

Lemma d_wf_typ_open_mono_inv : forall Ψ1 Ψ2 A T X,
  Ψ1 ++ Ψ2 ᵗ⊢ᵈ A ᵗ^^ₜ T -> 
  d_mono_typ (Ψ1 ++ Ψ2) T -> 
  X ∉ (dom Ψ2) -> 
  Ψ1 ++ X ~ □ ++ Ψ2 ᵗ⊢ᵈ A ᵗ^ₜ X.
Proof with try solve_notin; simpl in *; eauto.
  intros * HT HD HN.
  inductions HT...

  all: destruct A; destruct T;
      lazymatch goal with
      | n : nat, Hx: _ = ↑ ?n ᵗ^^ₜ _ |- _ =>
        try solve [
            induction n; unfold open_typ_wrt_typ in *; simpl in *; try solve_by_invert Hx; eauto]
      | n : nat, Hx: _ = ↑ (S ?n) ᵗ^^ₜ _ |- _ =>
        try solve [
            induction n; unfold open_typ_wrt_typ in Hx; simpl in Hx; inverts Hx]
      | Hx:` _ = ` _ ᵗ^^ₜ _ |- _ =>
          try solve [
              unfold open_typ_wrt_typ in *; simpl in *; inverts x;
              rewrite_env (Ψ1 ++ [(X, □)] ++ Ψ2); applys* d_wf_typ_weaken;
              eauto using d_wf_typ_weaken]
      (* | Hx: dtyp_svar _ = dtyp_svar _ ᵗ^^ₜ _ |- _ => *)
      (*     try solve [ *)
      (*         unfold open_typ_wrt_typ in *; simpl in *; inverts x; *)
      (*         rewrite_env (Ψ1 ++ [(SY, □)] ++ Ψ2); applys* d_wf_typ_weaken; *)
      (*         eauto using d_wf_typ_weaken] *)
      | Hx: _ = _ ᵗ^^ₜ _ |- _ =>
          try solve [unfold open_typ_wrt_typ in Hx; simpl in x; inverts x];
          try solve [unfold open_typ_wrt_typ; simpl; eauto];
          try solve [unfold open_typ_wrt_typ in *; simpl in *; inverts* x]
      end.
 all: try solve [
    pick fresh Y and apply d_wf_typ__all;
      unfold open_typ_wrt_typ in *; rewrite open_typ_wrt_typ_twice in *;
      inverts* x;
      [ (forwards H': H Y;
       try rewrite open_typ_wrt_typ_twice in H';
       try applys* s_in_subst_mono_inv H'; eauto) |
        (match goal with
        HD: d_mono_typ _ ?T |- _ => assert (HE:
               open_typ_wrt_typ_rec 0 ` Y (open_typ_wrt_typ_rec 1 T A)
               = open_typ_wrt_typ_rec 0 T (open_typ_wrt_typ_rec 0 ` Y A) )
          by rewrite* open_typ_wrt_typ_twice;
                                    forwards*: H1 Y ((Y, □) :: Ψ1) Ψ2 HE;
                                    rewrite_env ( Y ~ □ ++ (Ψ1 ++ Ψ2));
                                    eauto using d_mono_typ_weaken_app
      end) ]
      ].
Qed.

Lemma d_wf_typ_var_binds_another : forall Ψ1 x Ψ2 A1 B1 B2,
  Ψ2 ++ x ~ dbind_typ B1 ++ Ψ1 ᵗ⊢ᵈ A1 ->
  Ψ1 ᵗ⊢ᵈ B2 ->
  Ψ2 ++ x ~ dbind_typ B2 ++ Ψ1 ᵗ⊢ᵈ A1.
Proof with auto using d_wf_typ_weaken_cons.
  intros.
  dependent induction H; eauto.
  - induction Ψ2; simpl. auto.
    + simpl in H. inversion H. inversion H1.
      eauto.
    + destruct a. destruct d.
      inversion H.
        dependent destruction H1. econstructor; eauto.
        apply d_wf_typ_weaken_cons; auto.
      inversion H. inversion H1.
        apply d_wf_typ_weaken_cons; auto.
      inversion H. inversion H1.
        apply d_wf_typ_weaken_cons; auto.
  - induction Ψ2; simpl. auto.
    + simpl in H. inversion H. inversion H1.
      eauto.
    + destruct a. destruct d.
      inversion H.
        dependent destruction H1.
        apply d_wf_typ_weaken_cons; auto.
      inversion H. inversion H1.
        eauto...
        apply d_wf_typ_weaken_cons; auto.
      inversion H. inversion H1.
        apply d_wf_typ_weaken_cons; auto.
  - eapply d_wf_typ__all with (L:=L); intros; inst_cofinites_with X.
    auto.
    rewrite_env ((X ~ □ ++ Ψ2) ++ x ~ dbind_typ B2 ++ Ψ1).
    eapply H1; simpl; eauto.
Qed.

Lemma d_wf_expvar_weaken_cons : forall (Ψ : denv) (X : atom) (b : dbind) (x : expvar),
    d_wf_exp Ψ (exp_var_f x) -> d_wf_exp (X ~ b ++ Ψ) (exp_var_f x).
Proof.
  intros * H. inverts* H.
Qed.

Lemma d_wf_exp_var_binds_another : forall Ψ1 x Ψ2 e A1 A2,
  d_wf_exp (Ψ2 ++ x ~ dbind_typ A1 ++ Ψ1) e ->
  Ψ1 ᵗ⊢ᵈ A2 ->
  d_wf_exp (Ψ2 ++ x ~ dbind_typ A2 ++ Ψ1) e.
Proof with eauto using d_wf_typ_var_binds_another.
  intros. dependent induction H; auto.
  - induction Ψ2; simpl. auto.
    + simpl in H. inversion H. dependent destruction H1.
      now eauto.
      forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto.
    + rewrite_env (a::(Ψ2 ++ x ~ dbind_typ A1 ++ Ψ1)) in H. destruct a.
      forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto.
      forwards*: IHΨ2. applys* d_wf_expvar_weaken_cons.
  - pick fresh Y and apply d_wf_exp__abs. applys* d_wf_typ_var_binds_another.
    inst_cofinites_with Y.
    forwards: H1. rewrite_env ( (Y ~ dbind_typ T ++ Ψ2) ++ x ~ dbind_typ A1 ++ Ψ1)...
    all: eauto.
  - eauto.
  - pick fresh Y and apply d_wf_exp__tabs; eauto; 
    inst_cofinites_with Y; rewrite_env ( (Y ~ □ ++ Ψ2) ++ x ~ dbind_typ A2 ++ Ψ1).
    eapply H1 with (A1:=A1)...
  - econstructor. eapply d_wf_typ_var_binds_another; eauto.
    eauto.
  - econstructor. eapply d_wf_typ_var_binds_another; eauto.
    eauto.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma d_wf_exp_var_binds_another_cons : forall Ψ1 x e A1 A2,
  d_wf_exp (x ~ dbind_typ A1 ++ Ψ1) e ->
  Ψ1 ᵗ⊢ᵈ A2 ->
  d_wf_exp (x ~ dbind_typ A2 ++ Ψ1) e.
Proof.
  intros.
  rewrite_env (nil ++ x ~ dbind_typ A2 ++ Ψ1).
  eapply d_wf_exp_var_binds_another; eauto.
Qed.
