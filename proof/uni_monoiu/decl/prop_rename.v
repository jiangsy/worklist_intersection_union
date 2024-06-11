Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import uni_monoiu.notations.
Require Import uni_monoiu.decl.prop_basic.
Require Import uni_monoiu.ltac_utils.

Lemma d_wf_typ_rename_var : forall Ψ1 Ψ2 x y A B,
  (Ψ2 ++ (x , dbind_typ B) :: Ψ1) ᵗ⊢ᵈ A ->
  y ∉ dom (Ψ2 ++ (x , dbind_typ B) :: Ψ1) ->
  (Ψ2 ++ (y , dbind_typ B) :: Ψ1) ᵗ⊢ᵈ A.
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
  (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ᵗ⊢ᵈₘ T ->
  y ∉ dom (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ->
  (Ψ2 ++ (y , dbind_typ A) :: Ψ1) ᵗ⊢ᵈₘ T.
Proof with auto.
  intros. dependent induction H; eauto.
  - econstructor; eauto.
    apply binds_remove_mid_diff_bind in H...
    apply binds_weaken_mid...
    solve_false.
Qed.

Lemma d_wf_tenv_rename_var : forall Ψ1 Ψ2 x y A,
  ⊢ᵈₜ Ψ2 ++ (x , dbind_typ A) :: Ψ1 ->
  y ∉ dom (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ->
  ⊢ᵈₜ Ψ2  ++ (y , dbind_typ A) :: Ψ1.
Proof with eauto.
  intros. induction Ψ2. 
  - dependent destruction H... constructor...
  - dependent destruction H; try solve [constructor; eauto].
    + simpl. constructor...
      eapply d_wf_typ_rename_var with (x:=x); eauto.
Qed.

Lemma d_wf_env_rename_var : forall Ψ1 Ψ2 x y A,
  ⊢ᵈ Ψ2 ++ (x , dbind_typ A) :: Ψ1 ->
  y ∉ dom (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ->
  ⊢ᵈ Ψ2  ++ (y , dbind_typ A) :: Ψ1.
Proof with eauto.
  intros. induction Ψ2. 
  - dependent destruction H... constructor... eapply d_wf_tenv_rename_var...
  - dependent destruction H; try solve [constructor; eauto].
    dependent destruction H; simpl; constructor.
    + rewrite_env (((X, □) :: Ψ2) ++ (y, dbind_typ A) :: Ψ1). eapply d_wf_tenv_rename_var; eauto.
      constructor; auto.
    + rewrite_env (((x0, dbind_typ A0) :: Ψ2) ++ (y, dbind_typ A) :: Ψ1). eapply d_wf_tenv_rename_var; eauto.
      constructor; auto.
Qed.

Lemma d_wneq_all_rename_var : forall Ψ1 Ψ2 x y A B,
  d_wneq_all (Ψ2 ++ (x , dbind_typ B) :: Ψ1) A ->
  y ∉ dom (Ψ2 ++ (x , dbind_typ A) :: Ψ1) ->
  d_wneq_all (Ψ2 ++ (y , dbind_typ B) :: Ψ1) A.
Proof with auto.
  intros. dependent induction H; eauto.
  - econstructor; eauto.
    apply binds_remove_mid_diff_bind in H...
    apply binds_weaken_mid...
    solve_false.
Qed.

Lemma subst_exp_in_exp_refl : forall x e,
  {exp_var_f x ᵉ/ₑ x} e = e.
Proof.
  - intros. dependent induction e; simpl; auto.
    + destruct_eq_atom; eauto.
    + rewrite IHe; auto.
    + rewrite IHe1. rewrite IHe2. auto.
    + rewrite IHe; auto. 
    + rewrite IHe. auto.
    + rewrite IHe. auto.
Qed.

Theorem d_sub_rename_var : forall Ψ1 Ψ2 x y A B C,  
  Ψ2 ++ (x, dbind_typ C) :: Ψ1 ⊢ A <: B ->
  y ∉ (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  Ψ2 ++ (y, dbind_typ C) :: Ψ1 ⊢ A <: B.
Proof with eauto using d_wf_typ_rename_var, d_wf_env_rename_var, d_mono_typ_rename_var, d_wneq_all_rename_var.
  intros. dependent induction H; eauto...
  - inst_cofinites_for d_sub__all...
    intros. inst_cofinites_with X.
    rewrite_env ((X ~ ■ ++ Ψ2) ++ (y, dbind_typ C) :: Ψ1)...
    eapply H2... eauto.
Qed.

Theorem d_infabs_rename_var : forall Ψ1 Ψ2 x y A B C D, 
  d_infabs (Ψ2 ++ (x , dbind_typ D) :: Ψ1) A B C ->
  y ∉ (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_infabs (Ψ2 ++ (y, dbind_typ D) :: Ψ1) A B C.
Proof with eauto 4 using d_wf_typ_rename_var, d_wf_tenv_rename_var, d_mono_typ_rename_var.
  intros. dependent induction H...
  - constructor...
  - eapply d_infabs__all with (T:=T)...
Qed.

Theorem d_inftapp_rename_var : forall Ψ1 Ψ2 x y A B C D, 
  d_inftapp (Ψ2 ++ (x , dbind_typ D) :: Ψ1) A B C ->
  y ∉ (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_inftapp (Ψ2 ++ (y, dbind_typ D) :: Ψ1) A B C.
Proof with eauto using d_wf_typ_rename_var, d_wf_tenv_rename_var, d_mono_typ_rename_var.
  intros. dependent induction H...
Qed.

Theorem d_chk_inf_rename_var' : forall Ψ1 Ψ2 x y e A B mode, 
  d_chk_inf (Ψ2 ++ (x , dbind_typ B) :: Ψ1) e mode A ->
  y ∉ (dom (Ψ2 ++ (x, dbind_typ B) :: Ψ1)) ->
  d_chk_inf (Ψ2 ++ (y, dbind_typ B) :: Ψ1) ({exp_var_f y ᵉ/ₑ x} e) mode A.
Proof with eauto using d_wf_typ_rename_var, d_wf_tenv_rename_var, d_sub_rename_var, d_infabs_rename_var, d_inftapp_rename_var.
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
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} exp_var_f x0) by (apply subst_exp_in_exp_fresh_eq; eauto).
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ dbind_typ A ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__inf_tabs...
    intros. inst_cofinites_with X.
    rewrite <- subst_exp_in_exp_open_exp_wrt_typ...
    rewrite_env ((X ~ □ ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__chk_abstop...
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} exp_var_f x0) by (apply subst_exp_in_exp_fresh_eq; eauto).
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ dbind_typ typ_bot ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__chk_abs...
    intros. inst_cofinites_with x0.
    replace (exp_var_f x0) with ({exp_var_f y ᵉ/ₑ x} exp_var_f x0) by (apply subst_exp_in_exp_fresh_eq; eauto).
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ dbind_typ A1 ++ Ψ2) ++ (y, dbind_typ B) :: Ψ1)...
Qed.

Theorem d_chk_inf_rename_var : forall Ψ1 Ψ2 x y e A B mode, 
  d_chk_inf (Ψ2 ++ (x ,dbind_typ B) :: Ψ1) e mode A ->
  y ∉ (dom (Ψ2 ++ Ψ1)) ->
  d_chk_inf (Ψ2 ++ (y, dbind_typ B):: Ψ1) ({exp_var_f y ᵉ/ₑ x} e) mode A.
Proof with eauto.
  intros. destruct (x == y); subst.
  - rewrite subst_exp_in_exp_refl...
  - assert (y ∉ (dom (Ψ2 ++ x ~ (dbind_typ B) ++ Ψ1))) by auto.
    eapply d_chk_inf_rename_var'...
Qed.

Theorem d_chk_inf_rename_var_cons : forall Ψ x y e A B mode, 
  d_chk_inf ((x ,dbind_typ B) :: Ψ) e mode A ->
  y ∉ (dom Ψ) ->
  d_chk_inf ((y, dbind_typ B):: Ψ) ({exp_var_f y ᵉ/ₑ x} e) mode A.
Proof.
  intros. rewrite_env (nil ++ y ~ (dbind_typ B) ++ Ψ).
  eapply  d_chk_inf_rename_var; eauto.
Qed.

Lemma d_wf_typ_rename_dtvar : forall Ψ1 Ψ2 X Y b A,
  b = □ \/ b = ■ ->
  (Ψ2 ++ (X, b) :: Ψ1) ᵗ⊢ᵈ A ->
  Y ∉ dom (Ψ2 ++ (X, b) :: Ψ1) ->
  (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, b) :: Ψ1) ᵗ⊢ᵈ {`Y ᵗ/ₜ X} A.
Proof with auto.
  intros. dependent induction H0; eauto; simpl in *; destruct_eq_atom...
  - destruct H...
  - apply binds_remove_mid in H0...  
    apply binds_app_iff in H0. inversion H0...
    apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H2...
  - destruct H...
  - apply binds_remove_mid in H0...  
    apply binds_app_iff in H0. inversion H0...
    apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H2...
  - subst. inst_cofinites_for d_wf_typ__all;
    intros; inst_cofinites_with X0; 
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
    eapply s_in_subst_inv...
    rewrite_env (map (subst_typ_in_dbind ` Y X) (X0 ~ □ ++ Ψ2) ++ (Y, b) :: Ψ1)...
Qed.

Lemma d_mono_typ_rename_tvar : forall Ψ1 Ψ2 X Y T b,
  b = □ \/ b = ■  ->
  uniq (Ψ2 ++ (X, b) :: Ψ1) ->
  (Ψ2 ++ (X, b) :: Ψ1) ᵗ⊢ᵈₘ T ->
  Y ∉ dom (Ψ2 ++ (X, b) :: Ψ1) ->
  (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, b) :: Ψ1) ᵗ⊢ᵈₘ {`Y ᵗ/ₜ X} T.
Proof with auto.
  intros. dependent induction H1; eauto; simpl in *;  destruct_eq_atom...
  - destruct H...
    + subst. assert (X ~ ■ ∈ᵈ (Ψ2 ++ (X, ■) :: Ψ1))...
      unify_binds...
  - apply binds_remove_mid in H1... 
    apply binds_app_iff in H1. inversion H1...
    apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H3...
Qed.

Lemma d_wneq_all_rename_dtvar : forall Ψ1 Ψ2 X Y A b,
  b = □ \/ b = ■  ->
  uniq (Ψ2 ++ (X, b) :: Ψ1) ->
  d_wneq_all (Ψ2 ++ (X, b) :: Ψ1) A ->
  Y ∉ dom (Ψ2 ++ (X, b) :: Ψ1) ->
  d_wneq_all (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, b) :: Ψ1) ({`Y ᵗ/ₜ X} A).
Proof with auto using lc_typ_subst.
  intros. dependent induction H1; eauto; simpl in *; destruct_eq_atom...
  - destruct H...
    + subst. assert (X ~ ■ ∈ᵈ (Ψ2 ++ (X, ■) :: Ψ1))...
      unify_binds...
  - apply binds_remove_mid in H1... 
    apply binds_app_iff in H1. inversion H1...
    apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H3...
Qed.

Theorem d_sub_rename_dtvar : forall Ψ1 Ψ2 X Y b A B, 
  b = □ \/ b = ■  ->
  Ψ2 ++ (X, b) :: Ψ1 ⊢ A <: B ->
  Y ∉ (dom (Ψ2 ++ (X, b) :: Ψ1)) ->
  map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, b) :: Ψ1 ⊢ {`Y ᵗ/ₜ X} A <:  {`Y ᵗ/ₜ X} B.
Proof with eauto using d_wf_typ_rename_dtvar, d_mono_typ_rename_tvar, d_wneq_all_rename_dtvar, d_wf_env_rename_dtvar.
  intros. dependent induction H0; simpl in *...
  - destruct_eq_atom.
    + destruct H; constructor...
    + dependent destruction H0. 
      * apply binds_remove_mid in H...  
        apply binds_app_iff in H. inversion H...
        apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H3...
        constructor...
      * apply binds_remove_mid in H...  
        apply binds_app_iff in H. inversion H...
        apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H3...
        constructor...
  - inst_cofinites_for d_sub__all; intros; repeat rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
    + eapply s_in_subst_inv...
    + eapply s_in_subst_inv...
    + rewrite_env (map (subst_typ_in_dbind ` Y X) ((X0 ~ ■) ++ Ψ2) ++ (Y, b) :: Ψ1 )...
  - inst_cofinites_for d_sub__alll T:=({`Y ᵗ/ₜ X} T)...
    + eapply d_wneq_all_rename_dtvar...  apply d_wf_env_uniq. eapply d_sub_d_wf_env...
    + intros... rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      eapply s_in_subst_inv...
    + apply d_mono_typ_rename_tvar... apply d_wf_env_uniq. eapply d_sub_d_wf_env...
    + rewrite <- subst_typ_in_typ_open_typ_wrt_typ...
Qed.

Lemma subst_typ_in_exp_refl_eq : forall X e,
  subst_typ_in_exp (`X) X e = e.
Proof with auto.
  - intros. 
    dependent induction e; simpl; auto.
    + rewrite IHe...
    + rewrite IHe1... rewrite IHe2...
    + rewrite IHe... 
    + rewrite subst_typ_in_typ_refl_eq. rewrite IHe. auto.
    + rewrite subst_typ_in_typ_refl_eq. rewrite IHe. auto.
Qed.

Theorem d_sub_rename_dtvar_cons : forall Ψ X Y A B b,
  b = □ \/ b = ■ ->
  (X, b) :: Ψ ⊢ A <: B ->
  Y ∉ dom Ψ ->
  (Y, b):: Ψ ⊢ {` Y ᵗ/ₜ X} A <: {` Y ᵗ/ₜ X} B.
Proof.
  intros. destruct (X == Y).
  - subst. repeat rewrite subst_typ_in_typ_refl_eq; auto.
  - intros. rewrite_env (map (subst_typ_in_dbind `Y X) nil ++ (Y, b) :: Ψ).
    apply d_sub_rename_dtvar; eauto.
Qed.

Theorem d_infabs_rename_tvar : forall Ψ1 Ψ2 X Y A B C, 
  d_infabs (Ψ2 ++ (X, □) :: Ψ1) A B C ->
  Y ∉ (dom (Ψ2 ++ (X, □) :: Ψ1)) ->
  d_infabs (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, □) :: Ψ1) ({`Y ᵗ/ₜ X} A) ({`Y ᵗ/ₜ X} B) ({`Y ᵗ/ₜ X} C).
Proof with eauto using d_mono_typ_rename_tvar, d_wf_typ_rename_dtvar, d_wf_tenv_rename_tvar.
  intros. dependent induction H; simpl in *; eauto...
  - econstructor...
  - eapply d_infabs__all with (T:={`Y ᵗ/ₜ X} T)...
    + eapply d_mono_typ_rename_tvar... apply d_wf_tenv_uniq. eapply d_infabs_d_wf...
    + replace (typ_all ({` Y ᵗ/ₜ X} A)) with ({` Y ᵗ/ₜ X} (typ_all A)) by auto...
    + rewrite <- subst_typ_in_typ_open_typ_wrt_typ...
Qed.

Theorem d_inftapp_rename_tvar : forall Ψ1 Ψ2 X Y A B C, 
  d_inftapp (Ψ2 ++ (X, □) :: Ψ1) A B C ->
  Y ∉ (dom (Ψ2 ++ (X, □) :: Ψ1)) ->
  d_inftapp (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, □) :: Ψ1) ({`Y ᵗ/ₜ X} A) ({`Y ᵗ/ₜ X} B) ({`Y ᵗ/ₜ X} C).
Proof with eauto using d_wf_typ_rename_dtvar, d_wf_tenv_rename_tvar.
  intros. dependent induction H; simpl in *; eauto...
  - rewrite subst_typ_in_typ_open_typ_wrt_typ... apply d_inftapp__all...
    replace (typ_all ({` Y ᵗ/ₜ X} A)) with ({` Y ᵗ/ₜ X} (typ_all A)) by auto...
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

Theorem d_binds_var_typ_rename_tvar: forall Ψ1 Ψ2 X Y x A,
  ⊢ᵈₜ (Ψ2 ++ (X, □) :: Ψ1) ->
  Y ∉ dom (Ψ2 ++ (X, □) :: Ψ1) ->
  x ~ A ∈ᵈ (Ψ2 ++ (X, □) :: Ψ1) ->
  x ~ {` Y ᵗ/ₜ X} A ∈ᵈ (map (subst_typ_in_dbind ` Y X) Ψ2 ++ (Y, □) :: Ψ1).
Proof with eauto.
  intros. 
  apply binds_remove_mid_diff_bind in H1...  
  apply binds_app_iff in H1. inversion H1...
  - apply binds_map_2 with (f:=subst_typ_in_dbind `Y X) in H2... 
  - rewrite subst_typ_in_typ_fresh_eq...
    (* rewrite_env ((Ψ2 ++ (X ~ b)) ++ Ψ1) in H0. *)
    apply d_wf_tenv_strengthen_app in H.
    dependent destruction H.
    + apply d_wf_tenv_binds_d_wf_typ in H3...
      rewrite ftvar_in_d_wf_typ_upper...
  - destruct H; solve_false.
Qed.

Theorem d_chk_inf_rename_tvar : forall Ψ1 Ψ2 X Y e A mode, 
  d_chk_inf (Ψ2 ++ (X, □) :: Ψ1) e mode A ->
  Y ∉ (dom (Ψ2 ++ (X, □) :: Ψ1)) ->
  d_chk_inf (map (subst_typ_in_dbind `Y X) Ψ2 ++ (Y, □) :: Ψ1) ({` Y ᵉ/ₜ X} e) mode ({` Y ᵗ/ₜ X} A).
Proof with eauto 6 using d_wf_typ_rename_dtvar, d_mono_typ_rename_dtvar, d_wf_tenv_rename_tvar, d_sub_rename_dtvar, d_infabs_rename_tvar, d_inftapp_rename_tvar.
  intros. dependent induction H; simpl in *; eauto...
  - constructor...
    apply d_binds_var_typ_rename_tvar...
  - inst_cofinites_for d_chk_inf__inf_abs_mono.
    + inst_cofinites_by L.
      apply d_chk_inf_wf_env in H0. dependent destruction H0... dependent destruction H...
      constructor...
    + intros. inst_cofinites_with x...
      rewrite_env (map (subst_typ_in_dbind ` Y X) ((x ~ dbind_typ A) ++ Ψ2) ++ (Y, □) :: Ψ1)...
      replace (exp_var_f x) with (subst_typ_in_exp ` Y X (exp_var_f x))...
      rewrite <- subst_typ_in_exp_open_exp_wrt_exp...
      (* rewrite <- subst_typ_in_exp_open_exp_wrt_exp. *) 
  - inst_cofinites_for d_chk_inf__inf_tabs...
    + intros. inst_cofinites_with X0.
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto. apply s_in_subst_inv...
    + intros. replace (`X0) with (subst_typ_in_typ `Y X (`X0)). 
      rewrite <- subst_typ_in_exp_open_exp_wrt_typ...
      rewrite <- subst_typ_in_typ_open_typ_wrt_typ...
      * rewrite_env (map (subst_typ_in_dbind ` Y X) (X0 ~ □ ++ Ψ2) ++ (Y, □) :: Ψ1)...
      * simpl; destruct_eq_atom...
  - inst_cofinites_for d_chk_inf__chk_abstop...
    intros. inst_cofinites_with x.
    replace (exp_var_f x) with (subst_typ_in_exp ` Y X (exp_var_f x))...
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp.
    rewrite_env (map (subst_typ_in_dbind ` Y X) (x ~ dbind_typ typ_bot ++ Ψ2) ++ (Y, □) :: Ψ1)...
  - inst_cofinites_for d_chk_inf__chk_abs... 
    intros. inst_cofinites_with x.
    replace (exp_var_f x) with (subst_typ_in_exp ` Y X (exp_var_f x))...
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp...
    rewrite_env (map (subst_typ_in_dbind ` Y X) (x ~ dbind_typ A1 ++ Ψ2) ++ (Y, □) :: Ψ1)...
Qed.

Theorem d_chk_inf_rename_tvar_cons : forall Ψ X Y e A mode, 
  d_chk_inf ((X, □) :: Ψ) e mode A ->
  Y ∉ (dom Ψ) ->
  d_chk_inf ((Y, □) :: Ψ) ({` Y ᵉ/ₜ X} e) mode ({` Y ᵗ/ₜ X} A).
Proof.
  intros. destruct (X == Y).
  - subst. rewrite subst_typ_in_typ_refl_eq...
    rewrite subst_typ_in_exp_refl_eq. auto.
  - rewrite_env (map (subst_typ_in_dbind `Y X) nil ++ (Y, □) :: Ψ).
    eapply d_chk_inf_rename_tvar; eauto.
Qed.