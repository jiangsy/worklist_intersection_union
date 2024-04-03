Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import ln_utils.
Require Import LibTactics.


Open Scope aworklist_scope.


Lemma a_wf_wl_a_wf_env : forall Γ,
  ⊢ᵃʷ Γ ->
  a_wf_env (awl_to_aenv Γ).
Proof. 
Admitted.

Lemma a_wf_env_uniq : forall aE,
  a_wf_env aE ->
  uniq aE.
Proof.
  intros. induction H; auto.  
Qed.


Theorem a_mono_typ_wf : forall aE A,
  a_mono_typ aE A -> a_wf_typ aE A.
Proof.
  intros. induction H; auto.
Qed.

#[export] Hint Resolve a_mono_typ_wf a_wf_wl_a_wf_env a_wf_env_uniq : core.


Lemma aworklist_binds_split : forall Γ X,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  exists Γ1 Γ2, (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) = Γ.
Proof.
  intros. induction H.
  - inversion H0.
  - inversion H0; try dependent destruction H3.
    + apply IHa_wf_wl in H3. destruct H3 as [Γ1 [Γ2 Heq]].
      exists Γ1, (x ~ᵃ A ;ᵃ Γ2).
      rewrite <- Heq. auto.
  - inversion H0; try dependent destruction H2.
    + apply IHa_wf_wl in H2. destruct H2 as [Γ1 [Γ2 Heq]].
      exists Γ1, (X0 ~ᵃ □ ;ᵃ Γ2).
      rewrite <- Heq. auto.
  - inversion H0; try dependent destruction H2.
    + apply IHa_wf_wl in H2. destruct H2 as [Γ1 [Γ2 Heq]].
      exists Γ1, (X0 ~ᵃ ■ ;ᵃ Γ2).
      rewrite <- Heq. auto.
  - inversion H0; try dependent destruction H2.
    + exists Γ, aworklist_empty; auto.
    + apply IHa_wf_wl in H2. destruct H2 as [Γ1 [Γ2 Heq]].
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


Ltac auto_apply :=
  match goal with
  | H : context [ ?P -> ?Q ] |- ?Q => apply H
  end.

(* destruct conjunctions *)
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

Corollary a_wf_typ_weaken_cons: forall E X t A,
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

Lemma a_wf_conts_weaken: forall Γ1 Γ2 X t cs,
  a_wf_conts (awl_to_aenv (awl_app Γ1 Γ2)) cs ->
  X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
  a_wf_conts (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) cs
with a_wf_contd_weaken : forall Γ1 Γ2 X t cd,
  a_wf_contd (awl_to_aenv (awl_app Γ1 Γ2)) cd ->
  X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
  a_wf_contd (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) cd.
Proof with eauto using a_wf_typ_weaken_awl_to_aenv, a_wf_exp_weaken;
  try autorewrite with core using simpl.
  - introv H HN. inductions H.
    all: econstructor...
  - introv H HN. inductions H.
    all: econstructor...
Qed.

Lemma a_wf_work_weaken: forall Γ1 Γ2 X t Ω,
    a_wf_work (awl_to_aenv (awl_app Γ1 Γ2)) Ω ->
    X ∉ (dom (awl_to_aenv Γ1) `union` dom (awl_to_aenv Γ2)) ->
    a_wf_work (awl_to_aenv (awl_app Γ1 (aworklist_constvar Γ2 X t))) Ω.
Proof with eauto using a_wf_typ_weaken_awl_to_aenv, a_wf_exp_weaken, a_wf_conts_weaken, a_wf_contd_weaken;
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
  applys a_wf_wl_weaken HX...
  solve_false.
Qed.

Lemma apply_conts_rename_tvar : forall cs A w X X',
  apply_conts cs A w ->
  apply_conts (subst_tvar_in_conts (typ_var_f X') X cs) (subst_tvar_in_typ (typ_var_f X') X A)
    (subst_tvar_in_work (typ_var_f X') X w).
Proof.
  intros. induction H; simpl; try solve [simpl; eauto].
Qed.

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
    ⊢ᵃʷ (Γ ⧺ X ~ᵃ ⬒ ;ᵃ Γ' ⧺ Y ~ᵃ ⬒ ;ᵃ Γ'') ->
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
      rewrite_env ((Γ ⧺ X ~ᵃ ⬒ ;ᵃ (X0 ~ᵃ ⬒ ;ᵃ Γ') ⧺ Y ~ᵃ ⬒ ;ᵃ Γ'')) in H3.
      forwards* [?|?]: IHΓ H3. rewrite awl_rewrite_middle.
      rewrite_env ((Γ ⧺ X ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ ((X0 ~ᵃ ⬒ ;ᵃ Γ') ⧺ Y ~ᵃ ⬒ ;ᵃ Γ'')).
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
    ((Γ1 ⧺ Γ2) ⧺ Γ3) = (Γ1 ⧺ Γ2 ⧺ Γ3).
Proof with simpl; auto.
  introv. induction Γ1...
  all: try rewrite IHΓ1...
Qed.


Corollary aworklist_subst_bind_same : forall Γ Γ'' Γ1 Γ2 X Y A,
    ⊢ᵃʷ (Γ ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ'') ->
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
Proof with auto.
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
  introv WF HN HA. dependent induction HA; simpl; eauto.
  - destruct (X0 == X).
    + subst. forwards*: rename_tvar_in_aworklist_bind_same_eq H...
    + forwards*: rename_tvar_in_aworklist_bind_same_neq H...
  - destruct (X0 == X).
    + subst. forwards*: rename_tvar_in_aworklist_bind_same_eq H...
    + forwards*: rename_tvar_in_aworklist_bind_same_neq H...
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


Lemma a_wf_wl_wf_bind_typ : forall Γ x A,
  ⊢ᵃʷ Γ ->
  binds x (abind_var_typ A) (awl_to_aenv Γ) ->
  a_wf_typ (awl_to_aenv Γ) A.
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


(* A group lemmas about dom *)

Ltac destruct_wf_arrow :=
  match goal with
  | [ H : a_wf_typ _ (typ_arrow _ _) |- _ ] => dependent destruction H
  end.


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

Lemma a_worklist_subst_binds_same : forall Γ1 Γ2 X b X1 A Γ'1 Γ'2,
  ⊢ᵃʷ (awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty)) ->
  b = abind_tvar_empty \/ b = abind_stvar_empty \/ b = abind_etvar_empty ->
  aworklist_subst (awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty)) X A Γ'1 Γ'2 ->
  X <> X1 ->
  binds X1 b (awl_to_aenv (awl_app Γ2 (aworklist_constvar Γ1 X abind_etvar_empty))) ->
  binds X1 b (awl_to_aenv (awl_app (subst_tvar_in_aworklist A X Γ'2) Γ'1)).
Proof.
  intros. generalize dependent Γ1. generalize dependent Γ'1. generalize dependent Γ'2. induction Γ2; intros.
  - simpl in *. dependent destruction H1; simpl; auto.
    + inversion H3. dependent destruction H1. solve_notin_eq X1. auto.
    + solve_notin_eq X. 
    + solve_notin_eq X.
  - dependent destruction H.
    dependent destruction H4. simpl in *. destruct_binds; auto.
    + intuition. inversion H5. inversion H0. inversion H0.
    + apply binds_cons. eapply IHΓ2; eauto.
  - dependent destruction H.
    + dependent destruction H3. destruct_binds; auto.
      * apply binds_cons. eapply IHΓ2; eauto.
    + dependent destruction H3. destruct_binds; auto.
      * apply binds_cons. eapply IHΓ2; eauto.
    + dependent destruction H3.
      * rewrite awl_to_aenv_app in H. simpl in H. solve_notin_eq X0.
      * simpl in *.  destruct_binds; auto.
        apply binds_cons. eapply IHΓ2; eauto.
      * apply worklist_split_etvar_det in x; auto. 
        -- destruct x. subst. apply IHΓ2 in H3; auto.
           apply a_wf_wl_move_etvar_back; eauto.
           simpl in H6. rewrite awl_to_aenv_app in H6. simpl in H6. 
           rewrite awl_to_aenv_app. simpl. destruct_binds; eauto.
           apply in_app_iff in H8. inversion H8; auto.
           destruct_in; eauto.
        -- apply a_wf_wl_tvar_notin_remaining in H1; auto.
  - dependent destruction H.
    dependent destruction H3.
    simpl in *. eauto.
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
    apply a_wf_typ__tvar.
    apply aworklist_binds_split in HB. destruct HB as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    eapply a_worklist_subst_binds_same; eauto. auto.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    apply a_wf_typ__stvar.
    apply aworklist_binds_split in HB. destruct HB as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    eapply a_worklist_subst_binds_same; eauto. auto.
  - case_eq (X==X0); intros. { subst. simpl in HN. solve_notin. }
    apply a_wf_typ__etvar.
    apply aworklist_binds_split in HB. destruct HB as [Γ'1 [Γ'2 Heq]]; rewrite <- Heq in *.
    eapply a_worklist_subst_binds_same; eauto. auto.
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

