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


Ltac solve_notin_eq X :=
  let H := fresh "H" in 
    assert (H: X `notin` singleton X) by auto;
    apply notin_singleton_1 in H; contradiction.

  (* repeat
    match goal with 
    | H : X `notin` singleton X |- _ => apply notin_singleton_1 in H; contradiction
    | H : X `notin` singleton X `union` ?L |- _ => apply notin_union_1 in H; apply notin_singleton_1 in H; contradiction
    | H : X `notin` ?L1 `union` ?L2 |- _ => apply notin_union_2 in H
    end. *)


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
  X' `notin` ftvar_in_typ A `union` ftvar_in_aworklist' Γ `union` singleton X2 ->
  aworklist_subst Γ X2 A E Γ1 Γ2 -> 
  aworklist_subst (rename_tvar_in_aworklist X' X1 Γ) (if X2 == X1 then X' else X2) ({` X' /ᵗ X1} A) 
      (rename_tvar_in_etvar_list X' X1 E) (rename_tvar_in_aworklist X' X1 Γ1) (rename_tvar_in_aworklist X' X1 Γ2).
Proof with auto with Hdb_a_wl_red_basic.
  intros. induction H1; try solve [simpl; eauto with Hdb_a_wl_red_basic].
  - simpl in *. destruct (X == X1).
    + subst.
      constructor...
      apply IHaworklist_subst; auto.
      dependent destruction H...
    + constructor...
      apply IHaworklist_subst...
      dependent destruction H...
  - simpl in *.  _apply_IH_a_wl_red...  unfold eq_dec in *.
    destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
    + subst. contradiction.
    + subst. constructor... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor...
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + constructor... 
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *.  _apply_IH_a_wl_red... unfold eq_dec in *.
    destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
    + subst. contradiction. 
    + subst. constructor...
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor... 
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + constructor... 
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *. _apply_IH_a_wl_red... 
  - simpl in *. _apply_IH_a_wl_red... unfold eq_dec in *.
    destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
    + subst. contradiction.
    + subst. constructor... 
      rewrite subst_tvar_in_typ_fresh_eq...
    + subst. constructor... 
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
    + constructor... 
      rewrite ftvar_in_typ_subst_tvar_in_typ_upper...
  - simpl in *. _apply_IH_a_wl_red... unfold eq_dec in *.
      destruct (EqDec_eq_of_X Y X1); destruct (EqDec_eq_of_X X X1).
      + subst. contradiction.
      + subst. constructor...
      + subst. constructor... 
      + constructor... 
Qed.


Lemma a_mono_typ_rename : forall Γ A X X',
  a_mono_typ (awl_to_aenv Γ) A ->
  a_mono_typ (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)) ({` X' /ᵗ X} A).
Proof.
  intros. dependent induction H; simpl; eauto with Hdb_a_wl_red_basic.
  - destruct (X0 == X); constructor.
    + subst. admit.
    + admit.
  - destruct (X0 == X); constructor.
    + subst. admit.
    + admit.
Admitted.

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

Lemma ftvar_in_work_apply_cont_eq : forall w A c,
  apply_cont c A w ->
  ftvar_in_work w [=] ftvar_in_typ A `union` ftvar_in_cont c.
Proof.
  intros. induction H; simpl; fsetdec.
Qed.

Lemma a_wf_wl_apply_cont : forall Γ w A c,
  apply_cont c A w ->
  a_wf_wl (work_apply c A ⫤ Γ) ->
  a_wf_wl (w ⫤ Γ).
Proof with eauto with Hdb_a_wl_red_basic.
  intros. induction H; destruct_a_wf_wl...
Qed.


Lemma a_wf_wl_wf_bind_typ : forall Γ x A,
  ⊢ᵃ Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  a_wf_typ (awl_to_aenv Γ) A.
Proof.
Admitted.


Lemma tvar_notin_awl_notin_bind_typ : forall X Γ x A,
  ⊢ᵃ Γ ->
  X `notin` ftvar_in_aworklist' Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  X `notin` ftvar_in_typ A.
Proof.
Admitted.

Lemma awl_app_rename_tvar_comm : forall Γ1 Γ2 X X',
  awl_app (rename_tvar_in_aworklist X' X Γ2) (rename_tvar_in_aworklist X' X Γ1) =
  rename_tvar_in_aworklist X' X (awl_app Γ2 Γ1).
Proof. 
  intros. induction Γ2; simpl in *; auto; rewrite IHΓ2; auto.
Qed.

Lemma rename_tvar_in_aworklist_rename_tvar_in_etvar_list : forall X X' E,
  rename_tvar_in_aworklist X' X (etvar_list_to_awl E) = etvar_list_to_awl (rename_tvar_in_etvar_list X' X E).
Proof.
  induction E; auto.
  - simpl. rewrite IHE. auto.
Qed. 

Lemma subst_tvar_in_typ_rename : forall X X' A B,
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


Lemma subst_tvar_in_exp_rename : forall X X' e A,
  X' `notin` ftvar_in_exp e ->
  (subst_tvar_in_exp ` X' X (subst_tvar_in_exp A X e)) =
  (subst_tvar_in_exp ({` X' /ᵗ X} A) X' (subst_tvar_in_exp ` X' X e))
with subst_tvar_in_body_rename : forall X X' b A,
  X' `notin` ftvar_in_body b ->
  (subst_tvar_in_body ` X' X (subst_tvar_in_body A X b)) =
  (subst_tvar_in_body ({` X' /ᵗ X} A) X' (subst_tvar_in_body ` X' X b)).
Proof.
  - intros. induction e; simpl in *; auto.
    + rewrite IHe; auto.
    + rewrite IHe1; auto.
      rewrite IHe2; auto.
    + erewrite subst_tvar_in_body_rename; auto.
    + rewrite IHe; auto.
      rewrite subst_tvar_in_typ_rename; auto.
    + rewrite IHe; auto.
      rewrite subst_tvar_in_typ_rename; auto.
  - intros. induction b.
    simpl in *.
    erewrite subst_tvar_in_exp_rename; auto.
    rewrite subst_tvar_in_typ_rename; auto.
Qed.


Lemma subst_tvar_in_cont_rename : forall X X' A c,
  X' `notin` ftvar_in_cont c ->
  {` X' /ᶜₜ X} {A /ᶜₜ X} c = {({` X' /ᵗ X} A) /ᶜₜ X'} {` X' /ᶜₜ X} c.
Proof.
  intros. induction c; simpl in *;
    try repeat rewrite subst_tvar_in_typ_rename; auto; 
    try rewrite subst_tvar_in_exp_rename; auto;
    try rewrite IHc; auto.
Qed.
  
Lemma subst_tvar_in_work_rename : forall X X' w A,
  X' `notin` ftvar_in_work w ->
  {` X' /ʷₜ X} {A /ʷₜ X} w = {({` X' /ᵗ X} A) /ʷₜ X'} {` X' /ʷₜ X} w.
Proof.
  intros. destruct w; simpl in *; 
    try repeat rewrite subst_tvar_in_typ_rename; auto; 
    try rewrite subst_tvar_in_exp_rename; auto;
    try rewrite subst_tvar_in_cont_rename; auto.
Qed.


Lemma subst_tvar_in_awl_rename_tvar_comm_eq : forall Γ X X' A,
  X' `notin` ftvar_in_aworklist' Γ ->
  (rename_tvar_in_aworklist X' X (subst_tvar_in_aworklist A X Γ)) =
  (subst_tvar_in_aworklist ({` X' /ᵗ X} A) X' (rename_tvar_in_aworklist X' X Γ)).
Proof. 
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal. destruct ab; auto.
    + simpl. rewrite subst_tvar_in_typ_rename; auto.
  - apply f_equal. 
    + destruct ab; auto.
      * simpl. rewrite subst_tvar_in_typ_rename; auto.
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

Lemma a_wf_wl_worklist_subst : forall Γ X A E Γ1 Γ2,
  ⊢ᵃ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  aworklist_subst Γ X A E Γ1 Γ2 ->
  ⊢ᵃ awl_app (subst_tvar_in_aworklist A X Γ2)
     (awl_app (etvar_list_to_awl E) Γ1).
Proof.
  intros. induction H1; auto.
  - dependent destruction H; auto.
  - simpl. inversion H0; auto.
    + dependent destruction H2.
    + constructor; auto.
      admit.
      admit.
      apply IHaworklist_subst; auto.
      admit. 
  - simpl. inversion H0; auto.
      + dependent destruction H4.
      + constructor; auto.
        admit.
        apply IHaworklist_subst; auto.
        admit.
  - simpl. inversion H0; auto.
    + dependent destruction H4.
    + constructor; auto.
      admit.
      apply IHaworklist_subst; auto.
      admit.
  - simpl in *. constructor.
    admit.
    apply IHaworklist_subst; auto.
    admit.
  - simpl in *. inversion H0.
    + dependent destruction H4. contradiction.
    + constructor.
      admit.
      apply IHaworklist_subst; auto.
      admit.
  - simpl in *. inversion H0.
    + dependent destruction H3. contradiction.
    + admit.
Admitted.


Theorem a_wl_red_rename_tvar : forall Γ X X',
  ⊢ᵃ Γ -> 
  X' `notin` ftvar_in_aworklist' Γ ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_tvar_in_aworklist X' X Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_basic.
  intros. dependent induction H1; try solve [simpl in *; try _apply_IH_a_wl_red; eauto with Hdb_a_wl_red_basic].
  - simpl in *. destruct (X0 == X); _apply_IH_a_wl_red... 
  - simpl.
    dependent destruction H.
    eapply a_wl_red__sub_alll with (L:=L `union` singleton X `union` singleton X').
    + apply neq_all_rename...
    + apply neq_intersection_rename... 
    + apply neq_union_rename...
    + intros. simpl in *. inst_cofinites_with X0.
      assert (⊢ᵃ (work_sub (B1 ^ᵗ X0) A1 ⫤ X0 ~ᵃ ⬒;ᵃ Γ)) by admit. 
      rewrite typ_subst_open_comm...
      unfold eq_dec in H6.
      destruct (EqDec_eq_of_X X0 X) in H6...
      * subst. solve_notin_eq X.  
      * apply H6...
        repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X0.
    simpl in H0.
    rewrite typ_subst_open_comm...
    rewrite typ_subst_open_comm...
    unfold eq_dec in H2.
    destruct (EqDec_eq_of_X X0 X) in H2...
    + subst. solve_notin_eq X. 
    + apply H2. admit.
      repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
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
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename with (X':=X') (X1:=X) in H5 as Hsubst...
    unfold eq_dec in *. destruct (EqDec_eq_of_X X0 X);
      apply a_wl_red__sub_etvarmono1 with (E:=rename_tvar_in_etvar_list X' X E)
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + admit.
    + apply a_mono_typ_rename...  
    + subst.
      rewrite <- awl_app_rename_tvar_comm in IHa_wl_red.
      rewrite <- awl_app_rename_tvar_comm in IHa_wl_red.
      rewrite subst_tvar_in_awl_rename_tvar_comm_eq in IHa_wl_red; auto.
      rewrite rename_tvar_in_aworklist_rename_tvar_in_etvar_list in IHa_wl_red.
      apply IHa_wl_red; auto.
      admit.
      admit.
      admit.
    + admit.
    + apply a_mono_typ_rename...
    + rewrite <- awl_app_rename_tvar_comm in IHa_wl_red.
      rewrite <- awl_app_rename_tvar_comm in IHa_wl_red.
      rewrite subst_tvar_in_awl_rename_tvar_comm_neq in IHa_wl_red; auto.
      rewrite rename_tvar_in_aworklist_rename_tvar_in_etvar_list in IHa_wl_red.
      apply IHa_wl_red; auto.
      * admit. (* wf *)
      * admit. 
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename with (X':=X') (X1:=X) in H5 as Hsubst...
    unfold eq_dec in *. destruct (EqDec_eq_of_X X0 X); 
      apply a_wl_red__sub_etvarmono2 with (E:=rename_tvar_in_etvar_list X' X E)
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + admit.
    + apply a_mono_typ_rename...  
    + admit.
    + admit.
    + apply a_mono_typ_rename...
    + admit.
  - simpl in *. 
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H2...
    apply H2.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *. admit.
  - simpl in *. 
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H2...
    apply H2.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    dependent destruction H.
    apply a_wf_wl_wf_bind_typ in H2 as Hwfa...
    assert (⊢ᵃ (work_apply c A ⫤ Γ)) by now destruct_a_wf_wl; eauto with Hdb_a_wl_red_basic.
    apply IHa_wl_red in H4.
    eapply a_wl_red__inf_var with (A:=({` X' /ᵗ X} A))...
    apply binds_var_typ_rename...
    apply tvar_notin_awl_notin_bind_typ with (X:=X') in H2...
  - simpl in *.
    inst_cofinites_for  a_wl_red__inf_tabs...
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_exp_open_exp_wrt_typ in H2...
    simpl in H2.
    rewrite <- typ_subst_open_comm in H2...
    unfold eq_dec in H2.
    destruct (EqDec_eq_of_X X0 X) in H2...
    + subst. solve_notin_eq X. 
    + apply H2.
      * admit. (* wf *)
      * rewrite ftvar_in_exp_open_exp_wrt_typ_upper.
        rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.  
    inst_cofinites_for a_wl_red__inf_abs_mono. 
    intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    unfold eq_dec in *. destruct (EqDec_eq_of_X X2 X); destruct (EqDec_eq_of_X X1 X);
      try solve [subst; solve_notin_eq X].
    + rewrite subst_tvar_in_exp_open_exp_wrt_exp in H2. apply H2.
      * admit. (* wf *)
      * rewrite ftvar_in_exp_open_exp_wrt_exp_upper... 
  - simpl in *. 
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    unfold eq_dec in H2.
    destruct (EqDec_eq_of_X X0 X) in H2...
    + subst. solve_notin_eq X.
    + apply H2.  
      admit. (* wf *) 
      rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    admit.
  - simpl in *. 
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
    apply IHa_wl_red.
    + admit.
    + rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    eapply apply_cont_rename with (X:=X) (X':=X') in H1 as Hac...
    eapply a_wl_red__applycont; eauto.
    apply IHa_wl_red.
    eapply a_wf_wl_apply_cont in H; eauto.
    + apply ftvar_in_work_apply_cont_eq in H1...
      fsetdec.
Admitted.