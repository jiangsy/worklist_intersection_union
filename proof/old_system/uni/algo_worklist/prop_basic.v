Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import ln_utils.


Theorem a_mono_typ_wf : forall aE A,
  a_mono_typ aE A -> a_wf_typ aE A.
Proof.
  intros. induction H; auto.
Qed.

(* Fixpoint subst_tvar_in_aworklist *)

(* Theorem a_wl_red_rename_tvar : forall Γ1 Γ2 X b X',
  awl_app Γ2 (aworklist_constvar Γ1 X b) ⟶ᵃʷ⁎⋅ ->
  awl_app (subst_tvar_in_aworklist (typ_var_f X') X Γ2) (aworklist_constvar Γ1 X' b) ⟶ᵃʷ⁎⋅.
Proof.
  intros. induction Γ2.
  - simpl in *. destruct b.
    + dependent destruction H. econstructor; auto.
    + dependent destruction H. econstructor; auto.
    + dependent destruction H. econstructor; auto.
    + dependent destruction H. econstructor; auto.
  - simpl in *. destruct ab; try dependent destruction H.
    apply a_wl_red__gc_var; auto.
  - admit.
Admitted. *)

(* Theorem a_wl_red_rename_tvar' : forall Γ1 Γ2 X b X',
  awl_app Γ2 (aworklist_constvar Γ1 X b) ⟶ᵃʷ⁎⋅ ->
  awl_app (subst_tvar_in_aworklist (typ_var_f X') X Γ2) (aworklist_constvar Γ1 X' b) ⟶ᵃʷ⁎⋅.
Proof.
  intros. dependent induction H.
  - admit.
  -
  - simpl in *. destruct ab; try dependent destruction H.
    apply a_wl_red__gc_var; auto.
  - admit.
  -

  
Qed.
 *)

Hint Constructors a_wl_red : Hdb_a_wl_red_basic.
Hint Constructors apply_cont : Hdb_a_wl_red_basic.
Hint Constructors aworklist_subst : Hdb_a_wl_red_basic.


Lemma apply_cont_rename : forall c A w X X',
  apply_cont c A w ->
  apply_cont (subst_tvar_in_cont (typ_var_f X') X c) (subst_tvar_in_typ (typ_var_f X') X A) 
    (subst_tvar_in_work (typ_var_f X') X w).
Proof.
  intros. induction H; simpl; try solve [simpl; eauto with Hdb_a_wl_red_basic].
Qed.

Fixpoint subst_tvar_in_etvar_list (X' X: typvar) (E:list typvar) :=
  match E with 
  | nil => nil
  | X0 :: E' => (if X0 == X then X' else X0) :: (subst_tvar_in_etvar_list X X' E') 
  end.


Fixpoint rename_tvar_in_aworklist (X' X:typvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty 
  | (aworklist_consvar Γ' x b) => aworklist_consvar (rename_tvar_in_aworklist X' X Γ') x (subst_tvar_in_abind (typ_var_f X') X b)
  | (aworklist_constvar Γ' X0 b) => aworklist_constvar (rename_tvar_in_aworklist X' X Γ') (if X0 == X then X' else X0) (subst_tvar_in_abind (typ_var_f X') X b)
  | (aworklist_conswork Γ' w) => aworklist_conswork (rename_tvar_in_aworklist X' X Γ') (subst_tvar_in_work (typ_var_f X') X w)
end.

Lemma worklist_subst_rename : forall Γ X X' A E Γ1 Γ2,
  aworklist_subst Γ X A E Γ1 Γ2 -> 
  aworklist_subst (rename_tvar_in_aworklist X' X Γ) X' ({` X' /ᵗ X} A) 
      (subst_tvar_in_etvar_list X' X E) (rename_tvar_in_aworklist X' X Γ1) (rename_tvar_in_aworklist X' X Γ2).
Proof with auto with Hdb_a_wl_red_basic.
  intros. induction H; try solve [simpl; eauto with Hdb_a_wl_red_basic].
  - simpl. destruct (X == X)...
    contradiction.
  - admit.
  - 
Admitted.

Lemma worklist_subst_rename' : forall Γ X1 X2 X' A E Γ1 Γ2,
  aworklist_subst Γ X2 A E Γ1 Γ2 -> 
  aworklist_subst (rename_tvar_in_aworklist X' X1 Γ) (if X2 == X1 then X' else X2) ({` X' /ᵗ X1} A) 
      (subst_tvar_in_etvar_list X' X1 E) (rename_tvar_in_aworklist X' X1 Γ1) (rename_tvar_in_aworklist X' X1 Γ2).
Proof with auto with Hdb_a_wl_red_basic.
  intros. induction H; try solve [simpl; eauto with Hdb_a_wl_red_basic].
Admitted.


Theorem a_wl_red_rename_tvar : forall Γ X X',
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_tvar_in_aworklist X' X Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_basic.
  intros. dependent induction H; try solve [simpl; eauto with Hdb_a_wl_red_basic].
  - admit. 
  - simpl.
    eapply a_wl_red__sub_alll with (L:=L `union` singleton X).
    + admit.
    + admit.
    + admit.
    + intros. simpl in *. inst_cofinites_with X0.
      rewrite typ_subst_open_comm...
      unfold eq_dec in H3.
      destruct (EqDec_eq_of_X X0 X) in H3...
      admit.
  - simpl.
    eapply a_wl_red__sub_all with (L:=L `union` singleton X).
    intros. inst_cofinites_with X0.
    simpl in H0.
    rewrite typ_subst_open_comm...
    rewrite typ_subst_open_comm...
    admit.
  - simpl. 
    destruct (X0 == X).
    + subst.
      eapply a_wl_red__sub_arrow1 with (L:=L)... admit.
      admit.
      intros.
      inst_cofinites_with X1. inst_cofinites_with X2.
      admit.
    + eapply a_wl_red__sub_arrow1 with (L:=L)... admit.
      admit.
      intros.
      inst_cofinites_with X1. inst_cofinites_with X2.
      admit.
  - admit.
  - simpl. destruct (X0 == X).
    + subst.
      apply worklist_subst_rename with (X':=X') in H1 as Hsubst.
      apply a_wl_red__sub_etvarmono1 with (E:=subst_tvar_in_etvar_list X' X E)
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)
      ; auto... admit.
      admit.
      admit.
    + eapply a_wl_red__sub_etvarmono1; auto. admit.
      admit.
      admit.
      admit.
  - simpl. destruct (X0 == X).
    + subst.
      eapply a_wl_red__sub_etvarmono2; auto. admit.
       admit.
       admit.
       admit.
    + eapply a_wl_red__sub_etvarmono2; auto. admit.
      admit.
      admit.
      admit.
  - simpl in *. 
    eapply a_wl_red__chk_absarrow with (L:=L). intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H0...
  - admit.
  - simpl in *. 
    eapply a_wl_red__chk_abstop with (L:=L). intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H0...
  - simpl in *.
    eapply a_wl_red__inf_var with (A:=({` X' /ᵗ X} A))...
    admit.
  - simpl in *.
    eapply a_wl_red__inf_tabs with (L:=L `union` singleton X)...
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_exp_open_exp_wrt_typ in H0...
    simpl in H0.
    rewrite <- typ_subst_open_comm in H0...
    unfold eq_dec in H0.
    destruct (EqDec_eq_of_X X0 X) in H0...
    + subst. apply notin_union_2 in H1. apply notin_singleton_1 in H1. contradiction.
  - simpl in *.  
    eapply a_wl_red__inf_abs_mono.
    admit.
  - admit.
  - admit.
  - simpl in *. 
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
  - simpl. 
    eapply apply_cont_rename with (X:=X) (X':=X') in H...
Admitted.