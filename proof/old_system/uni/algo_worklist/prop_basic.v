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

Hint Constructors a_wf_wl : Hdb_a_wl_red_basic.
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

Fixpoint rename_tvar_in_etvar_list (X' X: typvar) (E:list typvar) :=
  match E with 
  | nil => nil
  | X0 :: E' => (if X0 == X then X' else X0) :: (rename_tvar_in_etvar_list X' X E') 
  end.


Fixpoint rename_tvar_in_aworklist (X' X:typvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty 
  | (aworklist_consvar Γ' x b) => aworklist_consvar (rename_tvar_in_aworklist X' X Γ') x (subst_tvar_in_abind (typ_var_f X') X b)
  | (aworklist_constvar Γ' X0 b) => aworklist_constvar (rename_tvar_in_aworklist X' X Γ') (if X0 == X then X' else X0) (subst_tvar_in_abind (typ_var_f X') X b)
  | (aworklist_conswork Γ' w) => aworklist_conswork (rename_tvar_in_aworklist X' X Γ') (subst_tvar_in_work (typ_var_f X') X w)
end.


Fixpoint ftvar_in_aworklist' (aW_5:aworklist) : vars :=
  match aW_5 with
  | aworklist_empty => {}
  | (aworklist_consvar aW x ab) => (ftvar_in_aworklist' aW) \u (ftvar_in_abind ab)
  | (aworklist_constvar aW X ab) => (ftvar_in_aworklist' aW) \u (ftvar_in_abind ab) \u (singleton X)
  | (aworklist_conswork aW w) => (ftvar_in_aworklist' aW) \u (ftvar_in_work w)
end.

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
    | H : a_wf_cont ?E (?C_C _) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _ _) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _ _ _) |- _ => dependent destruction H
    end.



Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵃ ?Γ) -> ?P |- _ => destruct_a_wf_wl; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃ Γ) by auto with Hdb_a_wl_red_basic;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2
    end.



Lemma worklist_subst_rename : forall Γ X1 X2 X' A E Γ1 Γ2,
  ⊢ᵃ Γ ->
  X' `notin` ftvar_in_typ A `union` ftvar_in_aworklist' Γ ->
  aworklist_subst Γ X2 A E Γ1 Γ2 -> 
  aworklist_subst (rename_tvar_in_aworklist X' X1 Γ) (if X2 == X1 then X' else X2) ({` X' /ᵗ X1} A) 
      (rename_tvar_in_etvar_list X' X1 E) (rename_tvar_in_aworklist X' X1 Γ1) (rename_tvar_in_aworklist X' X1 Γ2).
Proof with auto with Hdb_a_wl_red_basic.
  intros. induction H1; try solve [simpl; eauto with Hdb_a_wl_red_basic].
  - simpl in *. dependent destruction H. destruct (X == X1)...
  - simpl in *.  _apply_IH_a_wl_red...  unfold eq_dec in *.
    destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
    + subst. constructor. apply IHaworklist_subst... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor. apply IHaworklist_subst... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor. apply IHaworklist_subst...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + constructor. apply IHaworklist_subst...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *.  _apply_IH_a_wl_red... unfold eq_dec in *.
    destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
    + subst. constructor. apply IHaworklist_subst...
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor. apply IHaworklist_subst... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor. apply IHaworklist_subst...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + constructor. apply IHaworklist_subst...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *. _apply_IH_a_wl_red... 
  - simpl in *. _apply_IH_a_wl_red... unfold eq_dec in *.
    destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
    + subst. constructor. apply IHaworklist_subst... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor. apply IHaworklist_subst... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor. apply IHaworklist_subst... 
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + constructor. apply IHaworklist_subst...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *. _apply_IH_a_wl_red... 
Qed.


Lemma binds_var_typ_rename : forall x A X X' Γ,
  ⊢ᵃ Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) -> 
  binds x (abind_var_typ ({` X' /ᵗ X} A)) (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)).
Proof with auto with Hdb_a_wl_red_basic.
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

(* Theorem a_wl_red_rename_tvar : forall Γ X X',
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
      apply a_wl_red__sub_etvarmono1 with (E:=rename_tvar_in_etvar_list X' X E)
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
    apply binds_var_typ_rename... admit.
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
  - simpl in *. 
    eapply a_wl_red__infabs_all with (L:=L `union` singleton X)...
    intros. inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    unfold eq_dec in H0.
    destruct (EqDec_eq_of_X X0 X) in H0...
    + subst. apply notin_union_2 in H1. apply notin_singleton_1 in H1. contradiction.
  - admit.
  - simpl in *. 
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
  - simpl. 
    eapply apply_cont_rename with (X:=X) (X':=X') in H...
Admitted. *)



Ltac solve_notin_eq X :=
  repeat
    match goal with 
    | H : X `notin` singleton X |- _ => apply notin_singleton_1 in H; contradiction
    | H : X `notin` singleton X `union` ?L |- _ => apply notin_union_1 in H; apply notin_singleton_1 in H; contradiction
    | H : X `notin` ?L1 `union` ?L2 |- _ => apply notin_union_2 in H
    end.

Theorem a_wl_red_rename_tvar : forall Γ X X',
  ⊢ᵃ Γ -> 
  X' `notin` ftvar_in_aworklist' Γ ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_tvar_in_aworklist X' X Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_basic.
  intros. dependent induction H1; try solve [simpl in *; try _apply_IH_a_wl_red; eauto with Hdb_a_wl_red_basic].
  - admit.
  - simpl.
    dependent destruction H.
    eapply a_wl_red__sub_alll with (L:=L `union` singleton X `union` singleton X').
    + admit.
    + admit.
    + admit.
    + intros. simpl in *. inst_cofinites_with X0.
      assert (⊢ᵃ (work_sub (B1 ^ᵈ X0) A1 ⫤ aworklist_constvar Γ X0 abind_etvar_empty)) by admit. 
      rewrite typ_subst_open_comm...
      unfold eq_dec in H6.
      destruct (EqDec_eq_of_X X0 X) in H6...
      * subst. solve_notin_eq X.  
      * apply H6... admit.
  - simpl in *.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X0.
    simpl in H0.
    rewrite typ_subst_open_comm...
    rewrite typ_subst_open_comm...
    unfold eq_dec in H2.
    destruct (EqDec_eq_of_X X0 X) in H2...
    + subst. admit.
    + apply H2. admit.
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
  - simpl in *. 
    eapply worklist_subst_rename with (X':=X') (X1:=X) in H3 as Hsubst.
    destruct (X0 == X); apply a_wl_red__sub_etvarmono1 with (E:=rename_tvar_in_etvar_list X' X E)
    (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit. 
  - simpl. 
    eapply worklist_subst_rename with (X':=X') (X1:=X) in H3 as Hsubst.
    destruct (X0 == X); apply a_wl_red__sub_etvarmono2 with (E:=rename_tvar_in_etvar_list X' X E)
    (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit. 
  - simpl in *. 
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x.
    assert (⊢ᵃ (work_check (open_exp_wrt_exp e (exp_var_f x)) A2 ⫤ aworklist_consvar Γ x (abind_var_typ A1))) by admit.
    apply H2 in H4.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H4...
    admit.
  - admit.
  - simpl in *. 
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x.
    assert (⊢ᵃ (work_check (open_exp_wrt_exp e (exp_var_f x)) typ_top ⫤ aworklist_consvar Γ x (abind_var_typ typ_bot))) by admit.
    apply H2 in H4.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H4...
    admit.
  - simpl in *.
    assert (⊢ᵃ (work_apply c A ⫤ Γ)) by admit.
    dependent destruction H.
    apply IHa_wl_red in H4.
    eapply a_wl_red__inf_var with (A:=({` X' /ᵗ X} A))...
    apply binds_var_typ_rename...
    admit.
  - simpl in *.
    inst_cofinites_for  a_wl_red__inf_tabs...
    intros. inst_cofinites_with X0.
    assert (⊢ᵃ (work_check (open_exp_wrt_typ e ` X0) (A ^ᵈ X0) ⫤ X0 ~ᵃ □ ;ᵃ work_apply c (typ_all A) ⫤ Γ)) by admit.
    apply H2 in H4.
    rewrite subst_tvar_in_exp_open_exp_wrt_typ in H4...
    simpl in H4.
    rewrite <- typ_subst_open_comm in H4...
    unfold eq_dec in H4.
    destruct (EqDec_eq_of_X X0 X) in H4...
    + subst. solve_notin_eq X. 
    + admit.
  - simpl in *.  
    eapply a_wl_red__inf_abs_mono.
    admit.
  - simpl in *. 
    eapply a_wl_red__infabs_all with (L:=L `union` singleton X)...
    intros. inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    unfold eq_dec in H2.
    destruct (EqDec_eq_of_X X0 X) in H2...
    + subst. solve_notin_eq X.
    + apply H2.  admit. admit.
  - admit.
  - simpl in *. 
    assert ( ⊢ᵃ (work_apply c (A ^^ᵈ B) ⫤ Γ)) by admit.
    apply IHa_wl_red in H2.
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
    admit.
  - simpl. 
    assert (⊢ᵃ (w ⫤ Γ)) by admit.
    apply IHa_wl_red in H3.
    eapply apply_cont_rename with (X:=X) (X':=X') in H1...
    admit.
Admitted.