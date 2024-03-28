Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import ln_utils.
Require Import LibTactics.


Lemma aworklist_binds_split : forall Γ X,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  exists Γ1 Γ2, (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist = Γ.
Proof.
  intros. induction H.
  - inversion H0.
  - inversion H0; try dependent destruction H3.
    + apply IHa_wf_wl in H3. destruct H3 as [Γ1 [Γ2 Heq]].
      exists Γ1, (x ~ᵃ A ;ᵃ Γ2)%aworklist.
      rewrite <- Heq. auto.
  - inversion H0; try dependent destruction H2.
    + apply IHa_wf_wl in H2. destruct H2 as [Γ1 [Γ2 Heq]].
      exists Γ1, (X0 ~ᵃ □ ;ᵃ Γ2)%aworklist.
      rewrite <- Heq. auto.
  - inversion H0; try dependent destruction H2.
    + apply IHa_wf_wl in H2. destruct H2 as [Γ1 [Γ2 Heq]].
      exists Γ1, (X0 ~ᵃ ■ ;ᵃ Γ2)%aworklist.
      rewrite <- Heq. auto.
  - inversion H0; try dependent destruction H2.
    + exists Γ, aworklist_empty; auto.
    + apply IHa_wf_wl in H2. destruct H2 as [Γ1 [Γ2 Heq]].
      exists Γ1, (X0 ~ᵃ ⬒ ;ᵃ Γ2)%aworklist.
      rewrite <- Heq. auto.
  - simpl in H0.
    + apply IHa_wf_wl in H0. destruct H0 as [Γ1 [Γ2 Heq]].
      exists Γ1, (w ⫤ Γ2)%aworklist.
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
    | H : a_wf_cont ?E (?C_C _) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _ _) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _ _ _) |- _ => dependent destruction H
    end.

Hint Constructors a_wf_wl : Hdb_a_wl_red_basic.
Hint Constructors a_wl_red : Hdb_a_wl_red_basic.
Hint Constructors apply_cont : Hdb_a_wl_red_basic.
Hint Constructors aworklist_subst : Hdb_a_wl_red_basic.

Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with
    | H : (⊢ᵃʷ ?Γ) -> ?P |- _ => destruct_a_wf_wl;
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃʷ Γ) by auto with Hdb_a_wl_red_basic;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2
    end.


Ltac auto_apply :=
  match goal with
  | H : context [ ?P -> ?Q ] |- ?Q => apply H
  end.

(* destrcut conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
                         lazymatch T with
                         | exists _ , _ => destruct H
                         | _ /\ _ => destruct H
                         end
    end.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.


(********************************************)
(*                                          *)
(*            Ltac solve_false              *)
(*  try solve the goal by contradiction     *)
(*                                          *)
(********************************************)
Create HintDb FalseHd.
Ltac solve_false := let HF := fresh "HF" in
                    try solve [ try intro HF; destruct_conj; try solve_by_invert;
                                false; eauto 3 with FalseHd ].


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

Lemma dom_aenv_app_comm : forall (Ψ1 Ψ2: aenv),
  dom (Ψ2 ++ Ψ1) [=] dom Ψ2 `union` (dom Ψ1).
Proof.
  intros. induction Ψ2; simpl; auto.
  - fsetdec.
  - destruct a; simpl. rewrite IHΨ2. fsetdec.
Qed.


Lemma worklist_split_etvar_det : forall Γ1 Γ2 Γ'1 Γ'2 X,
  X `notin` dom (awl_to_aenv Γ'2) `union`  dom (awl_to_aenv Γ'1) ->
  (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist = (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ'1)%aworklist ->
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

(* weakening *)
Lemma a_wf_typ_weaken: forall E1 E2 X t A,
    a_wf_typ (E1 ++ E2) A ->
    X ∉ (dom E1 `union` dom E2) ->
    a_wf_typ (E1 ++ (X,t)::E2) A.
Proof.
  introv H HN. inductions H.
  1-3: solve [destruct* t; solve_false].
  1-3: rewrite_env (E1 ++ [(X,t)] ++ E2); forwards*: binds_weaken H.
  1,3-4: now eauto.
  - pick fresh X0 and apply a_wf_typ__all.
    + forwards*: H X0.
    + forwards*: H X0. forwards*: H0 X0.
      forwards*: H1 X0 (X0 ~ abind_tvar_empty ++ E1) E2. simpl; solve_notin.
Qed.

Corollary a_wf_typ_weaken_head: forall E X t A,
    a_wf_typ E A ->
    X ∉ dom E ->
    a_wf_typ ((X, t) :: E) A.
Proof with simpl in *; try solve_notin.
  intros. simpl.
  rewrite_env (nil ++ E) in H.
  forwards*: a_wf_typ_weaken X H...
Qed.

(** the following lemmas are overcomplicated; they could be generalized like
    the above ones **)
Corollary a_wf_typ_weaken_awl_to_aenv: forall Γ1 Γ2 X t A,
    a_wf_typ (awl_to_aenv (awl_app Γ1 Γ2)) A ->
    X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    a_wf_typ (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) A.
Proof with eauto; try autorewrite with core using simpl.
  introv H HN. inductions H.
  1-3: solve [destruct* t; solve_false].
  1-3: rewrite awl_to_aenv_app_2; rewrite awl_to_aenv_app in H...
  1,3-4: now eauto.
  - pick fresh X0 and apply a_wf_typ__all.
    + forwards*: H X0.
    + forwards*: H X0. forwards*: H0 X0.
      forwards: H1 X0 (aworklist_constvar Γ1 X0 abind_tvar_empty) Γ2...
Qed.

Lemma a_wf_exp_weaken: forall Γ1 Γ2 X t e,
    a_wf_exp (awl_to_aenv (awl_app Γ1 Γ2)) e ->
    X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    a_wf_exp (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) e
with a_wf_body_weaken: forall Γ1 Γ2 X t e,
    a_wf_body (awl_to_aenv (awl_app Γ1 Γ2)) e ->
    X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    a_wf_body (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) e.
Proof with try solve_notin; eauto using a_wf_typ_weaken_awl_to_aenv;
try autorewrite with core using simpl.

* clear a_wf_exp_weaken.
  introv H HN. inductions H.
  1,4,6,7: econstructor...
  - (* var *)
    econstructor. rewrite awl_to_aenv_app_2; rewrite awl_to_aenv_app in H...
  - (* abs *)
    pick fresh X0 and apply a_wf_exp__abs.
    + applys a_wf_typ_weaken_awl_to_aenv H...
    + forwards*: H0 X0.
      applys H1 X0 (aworklist_constvar Γ1 X0 (abind_var_typ T)) Γ2...
  - (* tabs *)
    pick fresh X0 and apply a_wf_exp__tabs.
    forwards H0: H X0...
    rewrite awl_to_aenv_app_3 in H0.
    forwards* H1: a_wf_body_weaken X t H0...
    rewrite awl_to_aenv_app_2 in H1...

* clear  a_wf_body_weaken.
  introv H HN. inductions H.
  - econstructor...
Qed.

Lemma a_wf_cont_weaken: forall Γ1 Γ2 X t c,
    a_wf_cont (awl_to_aenv (awl_app Γ1 Γ2)) c ->
    X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    a_wf_cont (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) c.
  Proof with eauto using a_wf_typ_weaken_awl_to_aenv, a_wf_exp_weaken;
try autorewrite with core using simpl.

    introv H HN. inductions H.
    all: econstructor...
  Qed.

Lemma a_wf_work_weaken: forall Γ1 Γ2 X t Ω,
    a_wf_work (awl_to_aenv (awl_app Γ1 Γ2)) Ω ->
    X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    a_wf_work (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) Ω.
Proof with eauto using a_wf_typ_weaken_awl_to_aenv, a_wf_exp_weaken, a_wf_cont_weaken;
try autorewrite with core using simpl.

  introv H HN. inductions H.
  all: econstructor...
Qed.


Lemma a_wf_wl_weaken: forall Γ1 Γ2 X t,
    ⊢ᵃʷ awl_app Γ1 Γ2 -> X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    (~ exists A, t = abind_var_typ A) -> ⊢ᵃʷ awl_app Γ1 (aworklist_constvar Γ2 X t).
Proof with eauto; try autorewrite with core using solve_notin.
  introv H HN HE. induction Γ1; simpl in *.
  - destruct* t. solve_false.
  - inverts H. forwards~: IHΓ1.
    rewrite awl_to_aenv_app in H3.
    econstructor...
    + applys* a_wf_typ_weaken_awl_to_aenv...
  - inverts H.
    all: rewrite awl_to_aenv_app in H2; forwards~: IHΓ1; econstructor...
  - inverts H.
    econstructor...
    + applys* a_wf_work_weaken...
Qed.

Corollary a_wf_wl_weaken_head: forall Γ X t,
    ⊢ᵃʷ Γ ->
    X ∉ (dom (awl_to_aenv Γ)) ->
    (~ exists A, t = abind_var_typ A) ->
    ⊢ᵃʷ aworklist_constvar Γ X t.
Proof with  simpl; solve_notin.
  intros.
  rewrite_env (awl_app aworklist_empty Γ) in H.
  rewrite_env (awl_app aworklist_empty (aworklist_constvar Γ X t)).
  applys* a_wf_wl_weaken...
Qed.

(* -- *)

Lemma awl_rewrite_middle : forall Γ1 Γ2 X,
    (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist = ((Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ Γ1)%aworklist.
Proof.
  introv. induction* Γ2; simpl; rewrite* IHΓ2.
Qed.

Lemma a_wf_wl_reorder : forall  Γ1 Γ2 X Y,
    ⊢ᵃʷ (Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
    ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1).
Proof with rewrite awl_to_aenv_app, awl_to_aenv_cons in *; try solve_notin.
  introv HW.
  inverts HW as FrY HX.
  forwards FrX: a_wf_wl_tvar_notin_remaining HX.
  rewrite awl_rewrite_middle in HX.
  rewrite awl_rewrite_middle.
  applys a_wf_wl_weaken HX...
  solve_false.
Qed.


Theorem a_mono_typ_wf : forall aE A,
  a_mono_typ aE A -> a_wf_typ aE A.
Proof.
  intros. induction H; auto.
Qed.


Lemma apply_cont_rename_tvar : forall c A w X X',
  apply_cont c A w ->
  apply_cont (subst_tvar_in_conts (typ_var_f X') X c) (subst_tvar_in_typ (typ_var_f X') X A)
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

Fixpoint rename_var_in_aworklist (x' x:expvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
  | aworklist_empty => aworklist_empty
  | (aworklist_consvar Γ' x0 b) => aworklist_consvar (rename_var_in_aworklist x' x Γ')  (if x0 == x then x' else x0) b
  | (aworklist_constvar Γ' X b) => aworklist_constvar (rename_var_in_aworklist x' x Γ') X b
  | (aworklist_conswork Γ' w) => aworklist_conswork (rename_var_in_aworklist x' x Γ') (subst_var_in_work (exp_var_f x') x w)
  end.

(* a group of rename lemmas for tvar *)
Lemma rename_tvar_in_aworklist_bind_same : forall Γ X1 X2 X' t,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_aworklist' Γ ->
  binds X1 t (awl_to_aenv Γ) ->
  (~ exists A, t = abind_var_typ A) ->
  binds (if X1 == X2 then X' else X1) t
    (awl_to_aenv (rename_tvar_in_aworklist X' X2 Γ)).
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

Corollary rename_tvar_in_aworklist_bind_same_neq : forall Γ X1 X2 X' t,
  ⊢ᵃʷ Γ ->
  X1 <> X2 ->
  X' `notin` ftvar_in_aworklist' Γ ->
  binds X1 t (awl_to_aenv Γ) ->
  (~ exists A, t = abind_var_typ A) ->
  binds X1 t (awl_to_aenv (rename_tvar_in_aworklist X' X2 Γ)).
Proof.
  intros. eapply rename_tvar_in_aworklist_bind_same with (X2:=X2) in H1; eauto.
  destruct_eq_atom; auto.
Qed.

Corollary rename_tvar_in_aworklist_bind_same_eq : forall Γ X X' t,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_aworklist' Γ ->
  binds X t (awl_to_aenv Γ) ->
  (~ exists A, t = abind_var_typ A) ->
  binds (X') t (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)).
Proof with solve_false.
  intros. eapply rename_tvar_in_aworklist_bind_same with (X2:=X) in H1; eauto...
  destruct_eq_atom; auto.
Qed.


Lemma subst_tvar_in_aworklist_bind_same : forall Γ X Y A t,
  ⊢ᵃʷ Γ ->
  binds Y t (awl_to_aenv Γ) ->
  (~ exists A, t = abind_var_typ A) ->
  binds Y t (awl_to_aenv (subst_tvar_in_aworklist A X Γ)).
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

Lemma aworklist_subst_bind_same_gen : forall Γ Γ' Γ'' Γ1 Γ2 X Y A,
    ⊢ᵃʷ (Γ ⧺ X ~ᵃ ⬒ ;ᵃ Γ' ⧺ Y ~ᵃ ⬒ ;ᵃ Γ'')%aworklist ->
    aworklist_subst (Γ ⧺ X ~ᵃ ⬒ ;ᵃ Γ' ⧺ Y ~ᵃ ⬒ ;ᵃ Γ'') X A Γ1 Γ2 ->
    binds Y abind_etvar_empty (awl_to_aenv Γ1) \/ binds Y abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist A X Γ2)).
Proof with solve_false.
  introv WF H. gen Γ' Γ'' Γ1 Γ2. induction Γ; intros; simpl in *; auto.
  - dependent destruction H; destruct_eq_atom; autorewrite with core; auto...
  - inverts H. forwards* [?|?]: IHΓ; simpl.
    now inverts* WF. eauto.
  - inverts H; inverts WF.
    all: autorewrite with core in *; jauto.
    all: try solve [forwards* [?|?]: IHΓ; simpl; now eauto].
    { left. rewrite_env ( (awl_to_aenv Γ ++
                             (X, abind_etvar_empty) :: awl_to_aenv Γ') ++ ((Y, abind_etvar_empty) :: awl_to_aenv Γ'')).
      eauto. }
    { forwards: a_wf_wl_tvar_notin_remaining H4. forwards (?&?): worklist_split_etvar_det H0. autorewrite with core in *. solve_notin. subst.
      rewrite_env ((Γ ⧺ X ~ᵃ ⬒ ;ᵃ (X0 ~ᵃ ⬒ ;ᵃ Γ') ⧺ Y ~ᵃ ⬒ ;ᵃ Γ'')%aworklist) in H3.
      forwards* [?|?]: IHΓ H3. rewrite awl_rewrite_middle.
      rewrite_env ((Γ ⧺ X ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ ((X0 ~ᵃ ⬒ ;ᵃ Γ') ⧺ Y ~ᵃ ⬒ ;ᵃ Γ''))%aworklist.
      rewrite awl_rewrite_middle in H4.
      applys a_wf_wl_weaken H4.
      autorewrite with core in *. solve_notin.
      solve_false.
    }
  - inverts H; inverts WF.
    all: autorewrite with core in *; jauto.
    all: try solve [forwards* [?|?]: IHΓ; simpl; now eauto].
Qed.

Lemma aworklist_app_assoc : forall Γ1 Γ2 Γ3,
    ((Γ1 ⧺ Γ2) ⧺ Γ3)%aworklist = (Γ1 ⧺ Γ2 ⧺ Γ3)%aworklist.
Proof with simpl; auto.
  introv. induction Γ1...
  all: try rewrite IHΓ1...
Qed.


Corollary aworklist_subst_bind_same : forall Γ Γ'' Γ1 Γ2 X Y A,
    ⊢ᵃʷ (Γ ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ'')%aworklist ->
    aworklist_subst (Γ ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ'') X A Γ1 Γ2 ->
    binds Y abind_etvar_empty (awl_to_aenv Γ1) \/ binds Y abind_etvar_empty (awl_to_aenv (subst_tvar_in_aworklist A X Γ2)).
Proof with applys* aworklist_subst_bind_same_gen.
  intros.
  rewrite awl_rewrite_middle in H.
  rewrite aworklist_app_assoc in H...
Qed.

Lemma binds_var_typ_rename_tvar : forall x A X X' Γ,
  ⊢ᵃʷ Γ ->
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

Lemma a_mono_typ_rename_tvar : forall Γ A X X',
  ⊢ᵃʷ Γ ->  X' ∉ ftvar_in_aworklist' Γ ->
  a_mono_typ (awl_to_aenv Γ) A ->
  a_mono_typ (awl_to_aenv (rename_tvar_in_aworklist X' X Γ)) ({` X' /ᵗ X} A).
Proof with solve_false.
  introv WF HN HA. dependent induction HA; simpl; eauto with Hdb_a_wl_red_basic.
  - destruct (X0 == X).
    + subst. forwards*: rename_tvar_in_aworklist_bind_same_eq H...
    + forwards*: rename_tvar_in_aworklist_bind_same_neq H...
  - destruct (X0 == X).
    + subst. forwards*: rename_tvar_in_aworklist_bind_same_eq H1...
    + forwards*: rename_tvar_in_aworklist_bind_same_neq H1...
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
  ⊢ᵃʷ Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  a_wf_typ (awl_to_aenv Γ) A.
Proof with solve_false.
  introv WF HB. induction* WF.
  - inverts HB.
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj. inverts H2. subst.
      1-2: applys* a_wf_typ_weaken_head...
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj...
      applys* a_wf_typ_weaken_head...
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj...
      applys* a_wf_typ_weaken_head...
  - simpl in HB. apply binds_cons_iff in HB.
    + destruct HB. destruct_conj...
      applys* a_wf_typ_weaken_head...
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
  ftvar_in_aworklist' (awl_app Γ2 Γ1) [=] ftvar_in_aworklist' Γ2 `union` ftvar_in_aworklist' Γ1.
Proof.
  induction Γ2; simpl; fsetdec.
Qed.

#[local] Hint Rewrite ftvar_in_aworklist'_awl_cons ftvar_in_aworklist'_awl_app : core.

Lemma rename_tvar_in_typ_rev_eq : forall X X' A,
  X' `notin` ftvar_in_typ A ->
  subst_tvar_in_typ (typ_var_f X) X' (subst_tvar_in_typ (typ_var_f X') X A) = A.
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
  subst_tvar_in_exp (typ_var_f X) X' (subst_tvar_in_exp (typ_var_f X') X e) = e
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

Lemma rename_tvar_in_cont_rev_eq : forall X X' c,
  X' `notin` ftvar_in_cont c ->
  subst_tvar_in_conts (typ_var_f X) X' (subst_tvar_in_conts (typ_var_f X') X c) = c.
Proof.
  induction c; simpl in *; intros;
    try repeat rewrite rename_tvar_in_typ_rev_eq; auto;
    try rewrite rename_tvar_in_exp_rev_eq; auto;
    try rewrite IHc; auto.
Qed.

Lemma rename_tvar_in_work_rev_eq : forall X X' w,
  X' `notin` ftvar_in_work w ->
  subst_tvar_in_work (typ_var_f X) X' (subst_tvar_in_work (typ_var_f X') X w) = w.
Proof.
  destruct w; intros; simpl in *;
    try repeat rewrite rename_tvar_in_typ_rev_eq; auto;
    try rewrite rename_tvar_in_exp_rev_eq; auto;
    try rewrite rename_tvar_in_cont_rev_eq; auto.
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


Lemma subst_tvar_in_exp_rename_tvar : forall X X' e A,
  X' `notin` ftvar_in_exp e ->
  (subst_tvar_in_exp ` X' X (subst_tvar_in_exp A X e)) =
  (subst_tvar_in_exp ({` X' /ᵗ X} A) X' (subst_tvar_in_exp ` X' X e))
with subst_tvar_in_body_rename_tvar : forall X X' b A,
  X' `notin` ftvar_in_body b ->
  (subst_tvar_in_body ` X' X (subst_tvar_in_body A X b)) =
  (subst_tvar_in_body ({` X' /ᵗ X} A) X' (subst_tvar_in_body ` X' X b)).
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


Lemma subst_tvar_in_cont_rename : forall X X' A c,
  X' `notin` ftvar_in_cont c ->
  {` X' /ᶜₜ X} {A /ᶜₜ X} c = {({` X' /ᵗ X} A) /ᶜₜ X'} {` X' /ᶜₜ X} c.
Proof.
  intros. induction c; simpl in *;
    try repeat rewrite subst_tvar_in_typ_rename_tvar; auto;
    try rewrite subst_tvar_in_exp_rename_tvar; auto;
    try rewrite IHc; auto.
Qed.

Lemma subst_tvar_in_work_rename : forall X X' w A,
  X' `notin` ftvar_in_work w ->
  {` X' /ʷₜ X} {A /ʷₜ X} w = {({` X' /ᵗ X} A) /ʷₜ X'} {` X' /ʷₜ X} w.
Proof.
  intros. destruct w; simpl in *;
    try repeat rewrite subst_tvar_in_typ_rename_tvar; auto;
    try rewrite subst_tvar_in_exp_rename_tvar; auto;
    try rewrite subst_tvar_in_cont_rename; auto.
Qed.


Lemma subst_tvar_in_awl_rename_tvar_comm_eq : forall Γ X X' A,
  X' `notin` ftvar_in_aworklist' Γ ->
  (rename_tvar_in_aworklist X' X (subst_tvar_in_aworklist A X Γ)) =
  (subst_tvar_in_aworklist ({` X' /ᵗ X} A) X' (rename_tvar_in_aworklist X' X Γ)).
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
  (subst_tvar_in_aworklist ({` X' /ᵗ X1} A) X2 (rename_tvar_in_aworklist X' X1 Γ)).
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal. rewrite subst_tvar_in_abind_subst_tvar_in_abind; auto.
  - apply f_equal. rewrite subst_tvar_in_abind_subst_tvar_in_abind; auto.
  - apply f_equal. rewrite subst_tvar_in_work_subst_tvar_in_work; auto.
Qed.

Lemma a_worklist_subst_ftavr_in_aworklist : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist'
    (awl_app (subst_tvar_in_aworklist A X Γ2) Γ1) [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - rewrite ftvar_in_typ_subst_tvar_in_typ_upper; fsetdec.
  - rewrite ftvar_in_work_subst_tvar_in_work_upper; fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.

Lemma a_worklist_subst_ftavr_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ1 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.


Lemma a_worklist_subst_ftavr_in_aworklist_2 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  ftvar_in_aworklist' Γ2 [<=] ftvar_in_aworklist' Γ `union` ftvar_in_typ A.
Proof.
  intros. induction H; simpl; try fsetdec.
  - autorewrite with core in *. fsetdec.
Qed.

(* A group lemmas about dom *)

#[local] Hint Rewrite dom_app dom_cons : core.


Lemma ftvar_in_wf_typ_upper : forall Γ A,
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
    assert ((ftvar_in_typ A) [<=] (ftvar_in_typ (A ^ᵗ X))) by apply ftvar_in_typ_open_typ_wrt_typ_lower.
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
      assert (ftvar_in_exp e [<=] ftvar_in_exp (e ^ᵉₑ exp_var_f x)) by apply ftvar_in_exp_open_exp_wrt_exp_lower.
      assert (x ~ abind_var_typ T ++ awl_to_aenv Γ = awl_to_aenv (x ~ᵃ T ;ᵃ Γ)) by (simpl; auto).
      eapply H1 in H3.
      simpl in *.
      fsetdec.
    + simpl.
      rewrite IHa_wf_exp1; eauto.
      rewrite IHa_wf_exp2; eauto.
      fsetdec.
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_body body5) using_name X.
      replace (X ~ abind_tvar_empty ++ awl_to_aenv Γ) with (awl_to_aenv (X ~ᵃ □ ;ᵃ Γ)) in H by auto.
      assert (ftvar_in_body body5 [<=] ftvar_in_body (open_body_wrt_typ body5 ` X)) by apply
        ftvar_in_body_open_body_wrt_typ_lower.
      apply ftvar_in_wf_body_upper in H.
      simpl in *.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto.
      rewrite ftvar_in_wf_typ_upper; eauto.
      fsetdec.
    + simpl. rewrite IHa_wf_exp; eauto.
      rewrite ftvar_in_wf_typ_upper; eauto.
      fsetdec.
  - intros. destruct b; simpl.
    + dependent destruction H.
      rewrite ftvar_in_wf_exp_upper; eauto.
      rewrite ftvar_in_wf_typ_upper; eauto.
      fsetdec.
Qed.

Lemma ftvar_in_wf_cont_upper : forall Γ c,
  a_wf_cont (awl_to_aenv Γ) c ->
  ftvar_in_cont c [<=] dom (awl_to_aenv Γ).
Proof.
  intros. intros; dependent induction H;
    simpl in *;
    try repeat erewrite ftvar_in_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite IHa_wf_cont; eauto; try fsetdec.
Qed.

Lemma ftvar_in_wf_work_upper : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w ->
  ftvar_in_work w [<=] dom (awl_to_aenv Γ).
Proof.
  intros. intros; dependent destruction H;
    simpl in *;
    try repeat erewrite ftvar_in_wf_typ_upper; eauto;
    try erewrite ftvar_in_wf_exp_upper; eauto;
    try rewrite ftvar_in_wf_cont_upper; eauto; try fsetdec.
Qed.

Lemma ftvar_in_aworklist_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  ftvar_in_aworklist' Γ [<=] dom (awl_to_aenv Γ).
Proof.
  intros; induction H; auto.
  - simpl. fsetdec.
  - simpl. rewrite ftvar_in_wf_typ_upper; eauto. fsetdec.
  - simpl. fsetdec.
  - simpl. fsetdec.
  - simpl. fsetdec.
  - simpl. rewrite ftvar_in_wf_work_upper; eauto.
    fsetdec.
Qed.

Lemma ftvar_in_aworklist_lower : forall Γ ,
  ⊢ᵃʷ Γ ->
  dom (awl_to_aenv Γ) [<=] ftvar_in_aworklist' Γ.
Proof.
  intros; induction H; auto.
  - simpl. fsetdec.
  - simpl.
Abort.

(* -- *)

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

Lemma a_worklist_subst_wf_typ : forall Γ X A B Γ1 Γ2,
    binds X abind_etvar_empty (awl_to_aenv Γ) ->
    X `notin` ftvar_in_typ B ->
    a_wf_typ (awl_to_aenv Γ) B ->
    ⊢ᵃʷ Γ ->
    aworklist_subst Γ X A Γ1 Γ2 ->
    a_wf_typ (awl_to_aenv (awl_app (subst_tvar_in_aworklist A X Γ2) Γ1)) B.
Proof with (autorewrite with core in *); simpl; eauto; solve_false; try solve_notin.
  introv HB HN WF HW HS.
  generalize dependent Γ1. generalize dependent Γ2. dependent induction WF; auto; intros.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    clear HN. induction HS.
    + autorewrite with core using simpl. inverts H...
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        forwards*: IHHS.
        applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
        rewrite dom_aworklist_subst in H5; try apply HS.
        solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** inverts H4. eauto.
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + simpl in *. inverts HW.
      forwards*: IHHS.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        forwards*: IHHS.
        { rewrite_env ((awl_to_aenv Γ2 ++ [(X, abind_etvar_empty)]) ++ awl_to_aenv Γ1) in H4.
          forwards: binds_weaken [(Y, abind_etvar_empty)] H4.
          rewrite_env ((awl_to_aenv Γ2 ++ X ~ abind_etvar_empty) ++ Y ~ abind_etvar_empty ++ awl_to_aenv Γ1). auto.
        }
        rewrite awl_rewrite_middle in *. applys a_wf_wl_weaken. assumption.
        autorewrite with core using solve_notin.
        solve_false.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    clear HN. induction HS.
    + autorewrite with core using simpl. inverts H...
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        forwards*: IHHS.
        applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
        rewrite dom_aworklist_subst in H5; try apply HS.
        solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** inverts H4. eauto.
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + simpl in *. inverts HW.
      forwards*: IHHS.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        forwards*: IHHS.
        { rewrite_env ((awl_to_aenv Γ2 ++ [(X, abind_etvar_empty)]) ++ awl_to_aenv Γ1) in H4.
          forwards: binds_weaken [(Y, abind_etvar_empty)] H4.
          rewrite_env ((awl_to_aenv Γ2 ++ X ~ abind_etvar_empty) ++ Y ~ abind_etvar_empty ++ awl_to_aenv Γ1). auto.
        }
        rewrite awl_rewrite_middle in *. applys a_wf_wl_weaken. assumption.
        autorewrite with core using solve_notin.
        solve_false.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    clear HN. induction HS.
    + autorewrite with core using simpl. inverts H...
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        forwards*: IHHS.
        applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
        rewrite dom_aworklist_subst in H5; try apply HS.
        solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + simpl in *. inverts HW.
      forwards*: IHHS.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** inverts H4. eauto.
        ** forwards*: IHHS.
           applys a_wf_typ_weaken_head Y. { autorewrite with core in H. auto. }
           rewrite dom_aworklist_subst in H6; try apply HS.
           solve_notin.
    + inverts HB; solve_false.
      * inverts HW. inverts H...
        ** inverts H4.
           forwards* [?|?]: aworklist_subst_bind_same HS.
           { rewrite awl_rewrite_middle. rewrite awl_rewrite_middle in H7.
             applys a_wf_wl_weaken H7... }
        ** assert (HB: binds X0 abind_etvar_empty (nil ++ awl_to_aenv Γ2 ++ (X, abind_etvar_empty) :: awl_to_aenv Γ1)) by eauto.
           forwards* [HB1|HB2]: binds_app_1 HB...
           forwards*: IHHS.
           { rewrite_env (((awl_to_aenv Γ2 ++ [(X, abind_etvar_empty)]) ++ awl_to_aenv Γ1)) in HB2.
             forwards*: binds_weaken [(Y, abind_etvar_empty)] HB2.
             rewrite_env ((awl_to_aenv Γ2 ++ X ~ abind_etvar_empty) ++ Y ~ abind_etvar_empty ++ awl_to_aenv Γ1).
             now auto. }
           { rewrite awl_rewrite_middle. rewrite awl_rewrite_middle in H7.
             applys* a_wf_wl_weaken... }
  - simpl in *. constructor; eauto.
  - intros. pick fresh X0 and apply a_wf_typ__all.
    now auto. subst.
    + pick fresh U. inst_cofinites_with X0.
      replace ((X0 ~ abind_tvar_empty ++ awl_to_aenv (awl_app (subst_tvar_in_aworklist A X Γ2) Γ1)))
        with  ((awl_to_aenv (awl_app (subst_tvar_in_aworklist A X (aworklist_constvar Γ2 X0 abind_tvar_empty)) Γ1))) by auto.
      eapply H1 with (Γ:=aworklist_constvar Γ X0 abind_tvar_empty); auto.
      applys~ binds_cons_3.
      { simpl in HN. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. solve_notin. }
      { econstructor... }
  - simpl in *. constructor; eauto.
  - simpl in *. constructor; eauto.
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
      [rewrite a_worklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
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
  | H : _ |- context [?e1 ^ᵉₑ ?e2] => rewrite ftvar_in_exp_open_exp_wrt_exp_upper
  | H : _ |- context [rename_tvar_in_aworklist ?X' ?X ?Γ] =>
    (* assert True *)
    match goal with
    | H1 : X `notin` ftvar_in_aworklist' (rename_tvar_in_aworklist X' X Γ) |- _ => fail 1
    | _ =>
      assert (X `notin` ftvar_in_aworklist' (rename_tvar_in_aworklist X' X Γ)) by now apply notin_rename_tvar_in_aworklist
    end
  | H : _ |- context [subst_tvar_in_conts ?X' ?X ?c] =>
    match goal with
    | H1 : (X `notin` (ftvar_in_cont (subst_tvar_in_conts X' X c))) |- _ => fail 1
    | _ =>
      assert (X `notin` (ftvar_in_cont (subst_tvar_in_conts X' X c))) by (simpl; apply subst_tvar_in_cont_fresh_same; auto)
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
  | H : _ |- _ => idtac
  end; auto.


Ltac solve_tvar_notin_ftvarlist_worklist_subst :=
  repeat
    lazymatch goal with
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- ?X ∉ ftvar_in_aworklist' ?Γ2 =>
      rewrite (a_worklist_subst_ftavr_in_aworklist_2 _ _ _ _ _ H); eauto; try (progress simpl; auto); try (progress solve_notin_rename_tvar; auto)
    | H : aworklist_subst ?Γ ?X' ?A ?Γ1 ?Γ2 |- ?X ∉ ftvar_in_aworklist' ?Γ1 =>
      rewrite (a_worklist_subst_ftavr_in_aworklist_1 _ _ _ _ _ H); eauto; try (progress simpl; auto); try (progress solve_notin_rename_tvar; auto)
   end.


Ltac rewrite_aworklist_rename_rev' :=
  lazymatch goal with
  | H : context [rename_tvar_in_aworklist _ _ (rename_tvar_in_aworklist ?X' ?X ?Γ)] |- _ =>
    let H1 := fresh "H" in
    assert (H1: X' `notin` ftvar_in_aworklist' Γ) by (try solve [solve_notin_rename_tvar; solve_tvar_notin_ftvarlist_worklist_subst]);
    rewrite rename_tvar_in_aworklist_rev_eq in H; auto
  end.

Ltac rewrite_aworklist_rename_rev :=
  repeat rewrite_aworklist_rename_rev'.


Ltac rewrite_aworklist_rename_subst' :=
  match goal with
  | H : context [rename_tvar_in_aworklist _ ?X (subst_tvar_in_aworklist ?A ?X _)] |- _ =>
    rewrite subst_tvar_in_awl_rename_tvar_comm_eq in H; try solve [apply notin_rename_tvar_in_aworklist; auto]; try solve
      [rewrite a_worklist_subst_ftavr_in_aworklist_2; eauto; simpl; eauto]
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


Lemma ftvar_in_typ_subst_tvar_in_typ_replace: forall A X Y,
   X `in` ftvar_in_typ A→ ftvar_in_typ ({`Y /ᵗ X} A) [=] ftvar_in_typ A `union` (singleton Y).
Admitted.

Lemma worklist_subst_rename_tvar : forall Γ X1 X2 X' A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  X' `notin` ftvar_in_typ A `union` ftvar_in_aworklist' Γ `union` singleton X2 ->
  aworklist_subst Γ X2 A Γ1 Γ2 ->
  aworklist_subst (rename_tvar_in_aworklist X' X1 Γ) (if X2 == X1 then X' else X2) ({` X' /ᵗ X1} A)
      (rename_tvar_in_aworklist X' X1 Γ1) (rename_tvar_in_aworklist X' X1 Γ2).
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
    assert (⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1)) by applys a_wf_wl_reorder H.
    apply IHaworklist_subst in H4. destruct_eq_atom.
    + rewrite_aworklist_rename_tvar'.
      applys a_ws1__etvar_move H4... applys* ftvar_in_typ_subst_tvar_in_typ_lower.
    + rewrite_aworklist_rename_tvar'.
      forwards*: a_ws1__etvar_move X' H4.
      rewrite ftvar_in_typ_subst_tvar_in_typ_replace...
    + rewrite_aworklist_rename_tvar'.
      applys a_ws1__etvar_move H4... applys* ftvar_in_typ_subst_tvar_in_typ_lower.
    + autorewrite with core. rewrite ftvar_in_aworklist'_awl_app in H0.
      rewrite ftvar_in_aworklist'_awl_cons in H0.
      solve_notin.
Qed.


Lemma a_worklist_subst_wf_wl : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  ⊢ᵃʷ awl_app (subst_tvar_in_aworklist A X Γ2) Γ1.
Proof.
  intros. induction H1; auto.
  - dependent destruction H; auto.
  - simpl. inversion H0; auto.
    + dependent destruction H2.
    + constructor; auto.
      * admit.
      * eapply a_worklist_subst_wf_typ; eauto.
        admit. admit. admit.
      * apply IHaworklist_subst; auto.
        dependent destruction H; auto.
  - simpl. inversion H0; auto.
      + dependent destruction H4.
      + constructor; auto.
        * admit.
        * apply IHaworklist_subst; auto.
          dependent destruction H; auto.
  - simpl. inversion H0; auto.
    + dependent destruction H4.
    + constructor; auto.
      * admit.
      * apply IHaworklist_subst; auto.
        dependent destruction H; auto.
  - simpl in *. constructor.
    admit.
    apply IHaworklist_subst; auto.
    dependent destruction H; auto.
  - simpl in *. inversion H0.
    + dependent destruction H4. contradiction.
    + constructor.
      * admit.
      * apply IHaworklist_subst; auto.
        dependent destruction H; auto.
  - simpl in *. inversion H0.
    + dependent destruction H4. contradiction.
    + apply* IHaworklist_subst.
      admit.
      admit.
Admitted.


Lemma a_wf_wl_rename_tvar_in_awl : forall Γ X X',
  ⊢ᵃʷ Γ ->
  X' `notin` dom (awl_to_aenv Γ) ->
  ⊢ᵃʷ (rename_tvar_in_aworklist X' X Γ).
Proof.
  intros. induction H; try solve [simpl in *; eauto with Hdb_a_wl_red_basic].
  - simpl in *. econstructor; auto.
    admit. admit.
  - simpl in *. destruct (X0 == X); subst.
    + constructor; auto.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto.
    + constructor; auto. admit.
  - simpl in *. destruct (X0 == X); subst.
    + constructor; auto.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto.
    + constructor; auto. admit.
  - simpl in *. destruct (X0 == X); subst.
    + constructor; auto.
      rewrite rename_tvar_in_aworklist_fresh_eq; auto.
      rewrite <- ftvar_in_aworklist_upper in H; auto.
    + constructor; auto. admit.
  - simpl.
Admitted.



Theorem a_wl_red_rename_tvar : forall Γ X X',
  X <> X' ->
  ⊢ᵃʷ Γ ->
  (* needs to change to (dom (awl_to_aenv Γ))*)
  X' `notin` ftvar_in_aworklist' Γ ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_tvar_in_aworklist X' X Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_basic; solve_false.
  intros. dependent induction H2; try solve [simpl in *; try _apply_IH_a_wl_red; eauto with Hdb_a_wl_red_basic].
  - simpl in *. destruct (X0 == X); _apply_IH_a_wl_red...
  - simpl.
    destruct_a_wf_wl. dependent destruction H0.
    inst_cofinites_for a_wl_red__sub_alll.
    + apply neq_all_rename...
    + apply neq_intersection_rename...
    + apply neq_union_rename...
    + intros. simpl in *. inst_cofinites_with X0.
      rewrite typ_subst_open_comm...
      destruct_eq_atom.
      auto_apply.
      * admit. (* wf *)
      * repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *. destruct_a_wf_wl.
    dependent destruction H0. dependent destruction H2.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X0.
    simpl in H0.
    rewrite typ_subst_open_comm...
    rewrite typ_subst_open_comm...
    destruct_eq_atom.
    auto_apply.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    destruct (X0 == X);
    inst_cofinites_for a_wl_red__sub_arrow1...
    + subst. apply rename_tvar_in_aworklist_bind_same_eq; auto...
      destruct_a_wf_wl; auto.
    + admit. (* mono *)
    + subst. admit.
    + intros. simpl in *. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H9 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite subst_tvar_in_typ_fresh_eq in H9; auto.
        rewrite subst_tvar_in_typ_fresh_eq in H9; auto.
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in *. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl. apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); eauto.
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
      destruct_a_wf_wl; auto.
    + admit. (* mono *)
    + admit.
    + intros. simpl in *.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H9 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl; apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); auto.
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__sub_arrow2...
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + admit. (* mono *)
    + admit.
    + intros. simpl in *. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H10 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite subst_tvar_in_typ_fresh_eq in H10; auto.
        rewrite subst_tvar_in_typ_fresh_eq in H10; auto.
        apply H8 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl. apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); auto.
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + admit. (* mono *)
    + admit.
    + intros. simpl in *.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H10 as Hws.
      * destruct_eq_atom. simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_typ_rev_eq in *...
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        apply H8 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; eauto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto.
           admit.
           simpl. apply binds_cons. apply binds_cons...
        -- rewrite (a_worklist_subst_ftavr_in_aworklist _ _ _ _ _ Hws); auto...
      * admit. (* wf *)
      * solve_notin_rename_tvar; auto.
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename_tvar with (X':=X') (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
      apply a_wl_red__sub_etvarmono1 with
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + apply rename_tvar_in_aworklist_bind_same_eq; eauto...
    + apply a_mono_typ_rename_tvar...
    + admit.
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply a_worklist_subst_wf_wl; eauto.
      rewrite a_worklist_subst_ftavr_in_aworklist with (Γ:=Γ); auto.
    + admit. (* bind *)
    + apply a_mono_typ_rename_tvar...
    + admit.
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply a_worklist_subst_wf_wl; eauto.
      * rewrite a_worklist_subst_ftavr_in_aworklist; auto...
  - simpl in *. destruct_a_wf_wl.
    eapply worklist_subst_rename_tvar with (X':=X') (X1:=X) in H7 as Hsubst...
    destruct_eq_atom;
      apply a_wl_red__sub_etvarmono2 with
        (Γ1:=rename_tvar_in_aworklist X' X Γ1) (Γ2:=rename_tvar_in_aworklist X' X Γ2)...
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + apply a_mono_typ_rename_tvar...
    + admit.
    + subst.
      rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      eapply a_worklist_subst_wf_wl; eauto.
      rewrite a_worklist_subst_ftavr_in_aworklist; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + apply a_mono_typ_rename_tvar...
    + admit.
    + rewrite_aworklist_rename.
      apply IHa_wl_red; auto.
      * eapply a_worklist_subst_wf_wl; eauto.
      * rewrite a_worklist_subst_ftavr_in_aworklist; auto.
  - simpl in *. destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H5...
    auto_apply.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *; destruct_a_wf_wl; destruct (X0 == X); subst;
    inst_cofinites_for a_wl_red__chk_absetvar.
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + intros. subst.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H11 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        simpl in Hws.
        replace (exp_var_f x) with (subst_tvar_in_exp (` X') X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_tvar_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        eapply H7 with (x:=x) in Hws as Hawlred; simpl in *; auto.
        assert (X `notin` (ftvar_in_exp (subst_tvar_in_exp ` X' X e ^ᵉₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto. admit. admit. (* wf *)
        -- rewrite a_worklist_subst_ftavr_in_aworklist with
            (Γ:=(work_check (e ^ᵉₑ exp_var_f x) ` X2 ⫤ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)%aworklist); auto. simpl.
          solve_notin_rename_tvar; auto.
        -- solve_notin_rename_tvar; auto.
      * admit. (* wf *)
      * simpl. solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H11 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto.
        replace (exp_var_f x) with (subst_tvar_in_exp (` X') X (exp_var_f x)) in Hws by auto.
        rewrite <- subst_tvar_in_exp_open_exp_wrt_exp in Hws.
        rewrite rename_tvar_in_exp_rev_eq in Hws.
        eapply H7 with (x:=x) in Hws as Hawlred; simpl; auto.
        assert (X `notin`(ftvar_in_exp (subst_tvar_in_exp ` X' X e ^ᵉₑ exp_var_f x))) by (solve_notin_rename_tvar; auto).
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- eapply a_worklist_subst_wf_wl in Hws; eauto. admit.
           repeat (apply binds_cons). auto.
        -- admit. (* wf *)
        -- rewrite ftvar_in_exp_open_exp_wrt_exp_upper; auto.
      * admit. (* wf *)
      * simpl; solve_notin_rename_tvar; auto.
  - simpl in *.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H3...
    apply H3.
    + admit. (* wf *)
    + repeat rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    dependent destruction H0.
    apply a_wf_wl_wf_bind_typ in H3 as Hwfa...
    assert (⊢ᵃʷ (work_apply c A ⫤ Γ)) by now destruct_a_wf_wl; eauto with Hdb_a_wl_red_basic.
    eapply a_wl_red__inf_var with (A:=({` X' /ᵗ X} A))...
    apply binds_var_typ_rename_tvar...
    auto_apply.
    + admit. (* wf *)
    + apply tvar_notin_awl_notin_bind_typ with (X:=X') in H3...
  - simpl in *.
    inst_cofinites_for a_wl_red__inf_tabs...
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_exp_open_exp_wrt_typ in H3...
    simpl in H3.
    rewrite <- typ_subst_open_comm in H3...
    destruct_eq_atom.
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_exp_open_exp_wrt_typ_upper.
      rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros. inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_tvar_in_exp_open_exp_wrt_exp in H3.
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - simpl in *.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    destruct_eq_atom.
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *. destruct_a_wf_wl.
    destruct (X0 == X); subst; inst_cofinites_for a_wl_red__infabs_etvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_eq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X') in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_cont_rev_eq in Hws; auto.
        assert (X `notin` (ftvar_in_cont ({` X' /ᶜₜ X} c))) by (solve_notin_rename_tvar; auto).
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- admit. (* wf *)
        -- rewrite a_worklist_subst_ftavr_in_aworklist with
            (Γ:=(work_infabs (typ_arrow ` X1 ` X2) c ⫤ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)%aworklist);
            auto.
      * admit. (* wf *)
      * simpl; solve_notin_rename_tvar; auto.
    + apply rename_tvar_in_aworklist_bind_same_neq; auto...
    + intros.
      apply worklist_subst_rename_tvar with (X':=X) (X1:=X') (X2:=X0) in H9 as Hws.
      destruct_eq_atom.
      * simpl in Hws.
        destruct_eq_atom.
        rewrite rename_tvar_in_aworklist_rev_eq in Hws; auto...
        rewrite rename_tvar_in_cont_rev_eq in Hws; auto.
        assert (X `notin` (ftvar_in_cont ({` X' /ᶜₜ X} c))) by now solve_notin_rename_tvar.
        apply H6 in Hws as Hawlred; simpl; auto.
        destruct_eq_atom.
        rewrite_aworklist_rename; simpl; auto.
        rewrite_aworklist_rename_rev.
        simpl in Hawlred. destruct_eq_atom.
        -- auto.
        -- admit. (* wf *)
        -- rewrite a_worklist_subst_ftavr_in_aworklist with
            (Γ:=(work_infabs (typ_arrow ` X1 ` X2) c ⫤ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)%aworklist); auto.
      * admit. (* wf *)
      * simpl; solve_notin_rename_tvar; auto...
  - simpl in *. destruct_a_wf_wl.
    eapply a_wl_red__inftapp_all.
    rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
    auto_apply.
    + admit. (* wf *)
    + rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
  - simpl in *.
    eapply apply_cont_rename_tvar with (X:=X) (X':=X') in H2 as Hac...
    eapply a_wl_red__applycont; eauto.
    auto_apply.
    eapply a_wf_wl_apply_cont in H0; eauto.
    + apply ftvar_in_work_apply_cont_eq in H2...
      fsetdec.
Admitted.

Lemma worklist_subst_rename_var : forall Γ x x' X A Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  x' `notin` fvar_in_aworklist' Γ ->
  aworklist_subst Γ X A Γ1 Γ2 ->
  aworklist_subst (rename_var_in_aworklist x' x Γ) X A (rename_var_in_aworklist x' x Γ1) (rename_var_in_aworklist x' x Γ2).
Proof.
  intros. induction H1; try solve [simpl in *; destruct_a_wf_wl; constructor; auto].
  simpl. admit.
  (* apply IHaworklist_subst *)
Admitted.

Lemma rename_var_in_aworklist_rev_eq : forall x x' Γ,
  x' `notin` fvar_in_aworklist' Γ ->
  rename_var_in_aworklist x x' (rename_var_in_aworklist x' x Γ) = Γ.
Proof.
  induction Γ; simpl in *; auto; intros; destruct_a_wf_wl.
  - destruct_eq_atom.  unfold eq_dec in *. destruct_eq_atom.
    + rewrite IHΓ; auto.
    + rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
  - rewrite IHΓ; auto.
    admit.
Admitted.




Lemma awl_app_rename_var_comm : forall Γ1 Γ2 X X',
  awl_app (rename_var_in_aworklist X' X Γ2) (rename_var_in_aworklist X' X Γ1) =
  rename_var_in_aworklist X' X (awl_app Γ2 Γ1).
Proof.
  intros. induction Γ2; simpl in *; auto; rewrite IHΓ2; auto.
Qed.


Lemma fvar_in_aworklist_upper : forall Γ ,
  ⊢ᵃʷ Γ ->
  fvar_in_aworklist' Γ [<=] dom (awl_to_aenv Γ).
Proof.
Admitted.


Ltac rewrite_fvar_in_aworklist :=
  match goal with
  | H : context [dom (awl_to_aenv ?Γ)] |- context [fvar_in_aworklist' ?Γ] =>
    rewrite fvar_in_aworklist_upper; auto
  end.

(* Lemma rename_var_in_etvar_list_eq : forall x x' E,
  rename_var_in_aworklist x x' (etvar_list_to_awl E) = (etvar_list_to_awl E).
Proof.
  induction E; simpl; auto.
  rewrite IHE; auto.
Qed. *)


Lemma subst_var_in_awl_rename_tvar_comm : forall Γ x x' X A,
  x' `notin` fvar_in_aworklist' Γ ->
  (rename_var_in_aworklist x' x (subst_tvar_in_aworklist A X Γ)) =
  (subst_tvar_in_aworklist A X (rename_var_in_aworklist x' x Γ)).
Proof.
  intros. induction Γ; simpl in *; auto; rewrite IHΓ; auto.
  - apply f_equal.
    admit.
Admitted.


Lemma a_worklist_subst_fvar_in_aworklist_2 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  fvar_in_aworklist' Γ2 [<=] fvar_in_aworklist' Γ.
Proof.
  intros. induction H; simpl; try fsetdec.
  admit.
Admitted.


Lemma a_worklist_subst_fvar_in_aworklist_1 : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  fvar_in_aworklist' Γ1 [<=] fvar_in_aworklist' Γ.
Proof.
  intros. induction H; simpl; try fsetdec.
  admit.
Admitted.


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

Lemma apply_cont_rename_var : forall x x' c w A,
  apply_cont c A w ->
  apply_cont (subst_var_in_cont (exp_var_f x') x c) A (subst_var_in_work (exp_var_f x') x w).
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
  | H : _ |- context [rename_var_in_aworklist ?x' ?x ?Γ] =>
    (* assert True *)
    match goal with
    | H1 : x `notin` fvar_in_aworklist' (rename_var_in_aworklist x' x Γ) |- _ => fail 1
    | _ =>
      assert (x `notin` fvar_in_aworklist' (rename_var_in_aworklist x' x Γ)) by
        (apply notin_rename_var_in_aworklist; auto)
    end
  | H : aworklist_subst ?Γ ?X ?A ?Γ1 ?Γ2 |- context [fvar_in_aworklist' ?Γ2] =>
      rewrite a_worklist_subst_fvar_in_aworklist_2; eauto
  | H : aworklist_subst ?Γ ?X ?A ?Γ1 ?Γ2 |- context [fvar_in_aworklist' ?Γ1] =>
      rewrite a_worklist_subst_fvar_in_aworklist_1; eauto
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

Theorem a_wl_red_rename_var : forall Γ x x',
  ⊢ᵃʷ Γ ->
  x' <> x ->
  x' `notin` (dom (awl_to_aenv Γ)) ->
  Γ ⟶ᵃʷ⁎⋅ ->
  (rename_var_in_aworklist x' x Γ) ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_basic.
  intros. dependent induction H2; try solve [simpl in *; try _apply_IH_a_wl_red; eauto with Hdb_a_wl_red_basic].
  - simpl.
    dependent destruction H.
    inst_cofinites_for a_wl_red__sub_alll; auto.
    + intros. simpl in *. inst_cofinites_with X.
      auto_apply; auto.
      admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__sub_all.
    intros. inst_cofinites_with X...
    auto_apply; auto.
    admit.  (* wf *)
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow1; auto.
    + admit. (* binds *)
    + admit. (* mono *)
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H10 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H8 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev.
           auto.
        -- admit. (* wf *)
        -- admit. (* notin *)
      * admit.
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__sub_arrow2; auto.
    + admit.
    + admit.
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H12 as Hws; simpl in *.
      * rewrite_aworklist_rename_var_rev.
        apply H9 in Hws as Hawlred; auto.
        -- rewrite_aworklist_rename_var.
           rewrite_aworklist_rename_var_rev.
           auto.
        -- admit. (* wf *)
        -- admit. (* notin *)
      * admit. (* wf *)
      * solve_notin_rename_var.
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono1 with (Γ1:=(rename_var_in_aworklist x' x Γ1))
      (Γ2:=(rename_var_in_aworklist x' x Γ2)); auto.
    + admit. (* binds *)
    + admit. (* mono *)
    + apply worklist_subst_rename_var with (x:=x) (x':=x') in H7 as Hws; eauto.
      * rewrite fvar_in_aworklist_upper; auto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev.
      auto_apply; auto.
      * admit. (* wf *)
      * admit. (* notin *)
  - simpl in *; destruct_a_wf_wl.
    eapply a_wl_red__sub_etvarmono2 with (Γ1:=(rename_var_in_aworklist x' x Γ1))
      (Γ2:=(rename_var_in_aworklist x' x Γ2)); auto.
    + admit. (* binds *)
    + admit. (* mono *)
    + apply worklist_subst_rename_var with (x:=x) (x':=x') in H7 as Hws; eauto.
      * rewrite fvar_in_aworklist_upper; auto.
    + rewrite_aworklist_rename_var.
      rewrite_aworklist_rename_var_rev.
      auto_apply.
      * admit. (* wf *)
      * admit. (* notin *)
  - simpl in *.
    inst_cofinites_for a_wl_red__chk_absarrow. intros.
    inst_cofinites_with x0.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    admit. (* wf *)
  - simpl in *; destruct_a_wf_wl.
    inst_cofinites_for a_wl_red__chk_absetvar.
    + admit. (* binds *)
    + intros.
      apply worklist_subst_rename_var with (x:=x') (x':=x) in H11 as Hws.
      simpl in Hws. destruct_eq_atom.
      rewrite_aworklist_rename_var_rev.
      * simpl in Hws.
        replace (({exp_var_f x' /ᵉₑ x} e) ^ᵉₑ exp_var_f x0) with
          (({exp_var_f x' /ᵉₑ x} e) ^ᵉₑ ({exp_var_f x' /ᵉₑ x} exp_var_f x0)) in Hws by (simpl; destruct_eq_atom; auto).
        rewrite <- subst_var_in_exp_open_exp_wrt_exp in Hws; auto.
        rewrite rename_var_in_exp_rev_eq in Hws.
        -- apply H7 in Hws; auto.
           ++ rewrite_aworklist_rename_var.
              rewrite_aworklist_rename_var_rev.
              auto.
           ++ admit. (* wf *)
           ++ admit. (* notin *)
        -- admit. (* notin *)
      * admit. (* wf *)
      * simpl.
        rewrite fvar_in_exp_open_exp_wrt_exp_upper.
        assert (x `notin` fvar_in_exp ({exp_var_f x' /ᵉₑ x} e)) by (apply subst_var_in_exp_fresh_same; auto).
        solve_notin_rename_var.
  - simpl in *.
    inst_cofinites_for a_wl_red__chk_abstop. intros.
    inst_cofinites_with x0.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *... simpl in *.
    destruct_eq_atom.
    auto_apply...
    admit. (* wf *)
  - simpl in *.
    destruct (x0 == x); subst; apply a_wl_red__inf_var with (A:=A).
    + admit.
    + auto_apply; auto. admit.
    + admit.
    + auto_apply; auto. admit.
  - simpl in *.
    inst_cofinites_for  a_wl_red__inf_tabs...
    intros. inst_cofinites_with X.
    rewrite subst_var_in_exp_open_exp_wrt_typ in *...
    auto_apply...
    admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__inf_abs_mono.
    intros.
    destruct_eq_atom.
    inst_cofinites_with x0. inst_cofinites_with X1. inst_cofinites_with X2.
    destruct_eq_atom.
    rewrite subst_var_in_exp_open_exp_wrt_exp in *; auto; simpl in *.
    destruct_eq_atom.
    auto_apply; auto.
    admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__infabs_all.
    intros. inst_cofinites_with X.
    auto_apply; auto.
    admit. (* wf *)
  - simpl in *.
    inst_cofinites_for a_wl_red__infabs_etvar; auto.
    + admit. (* binds *)
    + intros. admit.
  - simpl in *.
    eapply a_wl_red__inftapp_all.
    auto_apply; auto.
    admit. (* wf *)
  - simpl in *.
    eapply apply_cont_rename_var with (x':=x') (x:=x) in H2 as Hac.
    econstructor; eauto.
    auto_apply...
    eapply a_wf_wl_apply_cont; eauto.
Admitted.
