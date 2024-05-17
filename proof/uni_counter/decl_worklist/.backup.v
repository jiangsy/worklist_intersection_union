Lemma dom_dwl_to_denv_aenv : forall Ω,
  dom (dwl_to_denv Ω) = dom (dwl_to_aenv Ω).
Proof.
  intros. induction Ω; simpl; auto.
  rewrite IHΩ. auto.
Qed.

Lemma binds_dwl_to_denv_aenv : forall Ω X B,
  binds X B (dwl_to_denv Ω) -> binds X (dbind_to_abind B) (dwl_to_aenv Ω).
Proof.
  intros. induction Ω; simpl in *; auto.
  destruct_binds; auto.
Qed.

Lemma wf_typ_dwl_to_denv_aenv : forall Ω A,
  d_wf_typ (dwl_to_denv Ω) A -> a_wf_typ (dwl_to_aenv Ω) A.
Proof.
  intros. dependent induction H; simpl; auto.
  - eapply a_wf_typ__tvar; eauto.
    eapply binds_dwl_to_denv_aenv in H; eauto.
  - eapply a_wf_typ__stvar; eauto.
    eapply binds_dwl_to_denv_aenv in H; eauto.
  - eapply a_wf_typ__all; eauto.
    intros. inst_cofinites_with X.
    rewrite_env (dwl_to_aenv (dworklist_cons_var Ω X □%dbind)).
    eapply H1. simpl. auto.
Qed.

Lemma wf_dwl_to_denv_aenv : forall Ω,
  d_wf_tenv (dwl_to_denv Ω) -> ⊢ᵃ (dwl_to_aenv Ω).
Proof.
  intros. dependent induction Ω; simpl; auto.
  dependent destruction H; simpl; constructor; auto.
  - rewrite dom_dwl_to_denv_aenv in H0. auto.
  - apply wf_typ_dwl_to_denv_aenv; auto.
  - rewrite <- dom_dwl_to_denv_aenv. auto.
Qed.

Lemma a_wf_env_uniq: forall Σ,
  ⊢ᵃ Σ -> uniq Σ.
Proof.
  intros.
  induction H; auto.
Qed.