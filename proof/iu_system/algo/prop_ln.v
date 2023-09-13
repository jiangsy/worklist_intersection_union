Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export algo.def_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme a_typ_ind' := Induction for a_typ Sort Prop.

Combined Scheme a_typ_mutind from a_typ_ind'.

Scheme a_typ_rec' := Induction for a_typ Sort Set.

Combined Scheme a_typ_mutrec from a_typ_rec'.

Scheme a_body_ind' := Induction for a_body Sort Prop
  with a_exp_ind' := Induction for a_exp Sort Prop.

Combined Scheme a_body_a_exp_mutind from a_body_ind',a_exp_ind'.

Scheme a_body_rec' := Induction for a_body Sort Set
  with a_exp_rec' := Induction for a_exp Sort Set.

Combined Scheme a_body_a_exp_mutrec from a_body_rec',a_exp_rec'.

Scheme a_binding_ind' := Induction for a_binding Sort Prop.

Combined Scheme a_binding_mutind from a_binding_ind'.

Scheme a_binding_rec' := Induction for a_binding Sort Set.

Combined Scheme a_binding_mutrec from a_binding_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_a_typ (T1 : a_typ) {struct T1} : nat :=
  match T1 with
    | a_typ_unit => 1
    | a_typ_top => 1
    | a_typ_bot => 1
    | a_typ_tvar_f X1 => 1
    | a_typ_tvar_b n1 => 1
    | a_typ_stvar SX1 => 1
    | a_typ_etvar EX1 => 1
    | a_typ_arrow T2 T3 => 1 + (size_a_typ T2) + (size_a_typ T3)
    | a_typ_all T2 => 1 + (size_a_typ T2)
    | a_typ_union T2 T3 => 1 + (size_a_typ T2) + (size_a_typ T3)
    | a_typ_intersection T2 T3 => 1 + (size_a_typ T2) + (size_a_typ T3)
  end.

Fixpoint size_a_body (a_body1 : a_body) {struct a_body1} : nat :=
  match a_body1 with
    | a_body_anno e1 T1 => 1 + (size_a_exp e1) + (size_a_typ T1)
  end

with size_a_exp (e1 : a_exp) {struct e1} : nat :=
  match e1 with
    | a_exp_unit => 1
    | a_exp_top => 1
    | a_exp_var_f x1 => 1
    | a_exp_var_b n1 => 1
    | a_exp_abs e2 => 1 + (size_a_exp e2)
    | a_exp_app e2 e3 => 1 + (size_a_exp e2) + (size_a_exp e3)
    | a_exp_tabs a_body1 => 1 + (size_a_body a_body1)
    | a_exp_tapp e2 T1 => 1 + (size_a_exp e2) + (size_a_typ T1)
    | a_exp_anno e2 T1 => 1 + (size_a_exp e2) + (size_a_typ T1)
  end.

Fixpoint size_a_binding (b1 : a_binding) {struct b1} : nat :=
  match b1 with
    | a_bind_tvarempty => 1
    | a_bind_stvarempty => 1
    | a_bind_typ T1 => 1 + (size_a_typ T1)
    | a_bind_bound T1 T2 => 1 + (size_a_typ T1) + (size_a_typ T2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_a_typ_wrt_a_typ : nat -> a_typ -> Prop :=
  | degree_wrt_a_typ_a_typ_unit : forall n1,
    degree_a_typ_wrt_a_typ n1 (a_typ_unit)
  | degree_wrt_a_typ_a_typ_top : forall n1,
    degree_a_typ_wrt_a_typ n1 (a_typ_top)
  | degree_wrt_a_typ_a_typ_bot : forall n1,
    degree_a_typ_wrt_a_typ n1 (a_typ_bot)
  | degree_wrt_a_typ_a_typ_tvar_f : forall n1 X1,
    degree_a_typ_wrt_a_typ n1 (a_typ_tvar_f X1)
  | degree_wrt_a_typ_a_typ_tvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_a_typ_wrt_a_typ n1 (a_typ_tvar_b n2)
  | degree_wrt_a_typ_a_typ_stvar : forall n1 SX1,
    degree_a_typ_wrt_a_typ n1 (a_typ_stvar SX1)
  | degree_wrt_a_typ_a_typ_etvar : forall n1 EX1,
    degree_a_typ_wrt_a_typ n1 (a_typ_etvar EX1)
  | degree_wrt_a_typ_a_typ_arrow : forall n1 T1 T2,
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_typ_wrt_a_typ n1 T2 ->
    degree_a_typ_wrt_a_typ n1 (a_typ_arrow T1 T2)
  | degree_wrt_a_typ_a_typ_all : forall n1 T1,
    degree_a_typ_wrt_a_typ (S n1) T1 ->
    degree_a_typ_wrt_a_typ n1 (a_typ_all T1)
  | degree_wrt_a_typ_a_typ_union : forall n1 T1 T2,
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_typ_wrt_a_typ n1 T2 ->
    degree_a_typ_wrt_a_typ n1 (a_typ_union T1 T2)
  | degree_wrt_a_typ_a_typ_intersection : forall n1 T1 T2,
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_typ_wrt_a_typ n1 T2 ->
    degree_a_typ_wrt_a_typ n1 (a_typ_intersection T1 T2).

Scheme degree_a_typ_wrt_a_typ_ind' := Induction for degree_a_typ_wrt_a_typ Sort Prop.

Combined Scheme degree_a_typ_wrt_a_typ_mutind from degree_a_typ_wrt_a_typ_ind'.

#[export] Hint Constructors degree_a_typ_wrt_a_typ : core lngen.

Inductive degree_a_body_wrt_a_typ : nat -> a_body -> Prop :=
  | degree_wrt_a_typ_a_body_anno : forall n1 e1 T1,
    degree_a_exp_wrt_a_typ n1 e1 ->
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_body_wrt_a_typ n1 (a_body_anno e1 T1)

with degree_a_exp_wrt_a_typ : nat -> a_exp -> Prop :=
  | degree_wrt_a_typ_a_exp_unit : forall n1,
    degree_a_exp_wrt_a_typ n1 (a_exp_unit)
  | degree_wrt_a_typ_a_exp_top : forall n1,
    degree_a_exp_wrt_a_typ n1 (a_exp_top)
  | degree_wrt_a_typ_a_exp_var_f : forall n1 x1,
    degree_a_exp_wrt_a_typ n1 (a_exp_var_f x1)
  | degree_wrt_a_typ_a_exp_var_b : forall n1 n2,
    degree_a_exp_wrt_a_typ n1 (a_exp_var_b n2)
  | degree_wrt_a_typ_a_exp_abs : forall n1 e1,
    degree_a_exp_wrt_a_typ n1 e1 ->
    degree_a_exp_wrt_a_typ n1 (a_exp_abs e1)
  | degree_wrt_a_typ_a_exp_app : forall n1 e1 e2,
    degree_a_exp_wrt_a_typ n1 e1 ->
    degree_a_exp_wrt_a_typ n1 e2 ->
    degree_a_exp_wrt_a_typ n1 (a_exp_app e1 e2)
  | degree_wrt_a_typ_a_exp_tabs : forall n1 a_body1,
    degree_a_body_wrt_a_typ (S n1) a_body1 ->
    degree_a_exp_wrt_a_typ n1 (a_exp_tabs a_body1)
  | degree_wrt_a_typ_a_exp_tapp : forall n1 e1 T1,
    degree_a_exp_wrt_a_typ n1 e1 ->
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_exp_wrt_a_typ n1 (a_exp_tapp e1 T1)
  | degree_wrt_a_typ_a_exp_anno : forall n1 e1 T1,
    degree_a_exp_wrt_a_typ n1 e1 ->
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_exp_wrt_a_typ n1 (a_exp_anno e1 T1).

Inductive degree_a_body_wrt_a_exp : nat -> a_body -> Prop :=
  | degree_wrt_a_exp_a_body_anno : forall n1 e1 T1,
    degree_a_exp_wrt_a_exp n1 e1 ->
    degree_a_body_wrt_a_exp n1 (a_body_anno e1 T1)

with degree_a_exp_wrt_a_exp : nat -> a_exp -> Prop :=
  | degree_wrt_a_exp_a_exp_unit : forall n1,
    degree_a_exp_wrt_a_exp n1 (a_exp_unit)
  | degree_wrt_a_exp_a_exp_top : forall n1,
    degree_a_exp_wrt_a_exp n1 (a_exp_top)
  | degree_wrt_a_exp_a_exp_var_f : forall n1 x1,
    degree_a_exp_wrt_a_exp n1 (a_exp_var_f x1)
  | degree_wrt_a_exp_a_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_a_exp_wrt_a_exp n1 (a_exp_var_b n2)
  | degree_wrt_a_exp_a_exp_abs : forall n1 e1,
    degree_a_exp_wrt_a_exp (S n1) e1 ->
    degree_a_exp_wrt_a_exp n1 (a_exp_abs e1)
  | degree_wrt_a_exp_a_exp_app : forall n1 e1 e2,
    degree_a_exp_wrt_a_exp n1 e1 ->
    degree_a_exp_wrt_a_exp n1 e2 ->
    degree_a_exp_wrt_a_exp n1 (a_exp_app e1 e2)
  | degree_wrt_a_exp_a_exp_tabs : forall n1 a_body1,
    degree_a_body_wrt_a_exp n1 a_body1 ->
    degree_a_exp_wrt_a_exp n1 (a_exp_tabs a_body1)
  | degree_wrt_a_exp_a_exp_tapp : forall n1 e1 T1,
    degree_a_exp_wrt_a_exp n1 e1 ->
    degree_a_exp_wrt_a_exp n1 (a_exp_tapp e1 T1)
  | degree_wrt_a_exp_a_exp_anno : forall n1 e1 T1,
    degree_a_exp_wrt_a_exp n1 e1 ->
    degree_a_exp_wrt_a_exp n1 (a_exp_anno e1 T1).

Scheme degree_a_body_wrt_a_typ_ind' := Induction for degree_a_body_wrt_a_typ Sort Prop
  with degree_a_exp_wrt_a_typ_ind' := Induction for degree_a_exp_wrt_a_typ Sort Prop.

Combined Scheme degree_a_body_wrt_a_typ_degree_a_exp_wrt_a_typ_mutind from degree_a_body_wrt_a_typ_ind',degree_a_exp_wrt_a_typ_ind'.

Scheme degree_a_body_wrt_a_exp_ind' := Induction for degree_a_body_wrt_a_exp Sort Prop
  with degree_a_exp_wrt_a_exp_ind' := Induction for degree_a_exp_wrt_a_exp Sort Prop.

Combined Scheme degree_a_body_wrt_a_exp_degree_a_exp_wrt_a_exp_mutind from degree_a_body_wrt_a_exp_ind',degree_a_exp_wrt_a_exp_ind'.

#[export] Hint Constructors degree_a_body_wrt_a_typ : core lngen.

#[export] Hint Constructors degree_a_exp_wrt_a_typ : core lngen.

#[export] Hint Constructors degree_a_body_wrt_a_exp : core lngen.

#[export] Hint Constructors degree_a_exp_wrt_a_exp : core lngen.

Inductive degree_a_binding_wrt_a_typ : nat -> a_binding -> Prop :=
  | degree_wrt_a_typ_a_bind_tvarempty : forall n1,
    degree_a_binding_wrt_a_typ n1 (a_bind_tvarempty)
  | degree_wrt_a_typ_a_bind_stvarempty : forall n1,
    degree_a_binding_wrt_a_typ n1 (a_bind_stvarempty)
  | degree_wrt_a_typ_a_bind_typ : forall n1 T1,
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_binding_wrt_a_typ n1 (a_bind_typ T1)
  | degree_wrt_a_typ_a_bind_bound : forall n1 T1 T2,
    degree_a_typ_wrt_a_typ n1 T1 ->
    degree_a_typ_wrt_a_typ n1 T2 ->
    degree_a_binding_wrt_a_typ n1 (a_bind_bound T1 T2).

Scheme degree_a_binding_wrt_a_typ_ind' := Induction for degree_a_binding_wrt_a_typ Sort Prop.

Combined Scheme degree_a_binding_wrt_a_typ_mutind from degree_a_binding_wrt_a_typ_ind'.

#[export] Hint Constructors degree_a_binding_wrt_a_typ : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_a_typ : a_typ -> Set :=
  | lc_set_a_typ_unit :
    lc_set_a_typ (a_typ_unit)
  | lc_set_a_typ_top :
    lc_set_a_typ (a_typ_top)
  | lc_set_a_typ_bot :
    lc_set_a_typ (a_typ_bot)
  | lc_set_a_typ_tvar_f : forall X1,
    lc_set_a_typ (a_typ_tvar_f X1)
  | lc_set_a_typ_stvar : forall SX1,
    lc_set_a_typ (a_typ_stvar SX1)
  | lc_set_a_typ_etvar : forall EX1,
    lc_set_a_typ (a_typ_etvar EX1)
  | lc_set_a_typ_arrow : forall T1 T2,
    lc_set_a_typ T1 ->
    lc_set_a_typ T2 ->
    lc_set_a_typ (a_typ_arrow T1 T2)
  | lc_set_a_typ_all : forall T1,
    (forall X1 : typvar, lc_set_a_typ (open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1))) ->
    lc_set_a_typ (a_typ_all T1)
  | lc_set_a_typ_union : forall T1 T2,
    lc_set_a_typ T1 ->
    lc_set_a_typ T2 ->
    lc_set_a_typ (a_typ_union T1 T2)
  | lc_set_a_typ_intersection : forall T1 T2,
    lc_set_a_typ T1 ->
    lc_set_a_typ T2 ->
    lc_set_a_typ (a_typ_intersection T1 T2).

Scheme lc_a_typ_ind' := Induction for lc_a_typ Sort Prop.

Combined Scheme lc_a_typ_mutind from lc_a_typ_ind'.

Scheme lc_set_a_typ_ind' := Induction for lc_set_a_typ Sort Prop.

Combined Scheme lc_set_a_typ_mutind from lc_set_a_typ_ind'.

Scheme lc_set_a_typ_rec' := Induction for lc_set_a_typ Sort Set.

Combined Scheme lc_set_a_typ_mutrec from lc_set_a_typ_rec'.

#[export] Hint Constructors lc_a_typ : core lngen.

#[export] Hint Constructors lc_set_a_typ : core lngen.

Inductive lc_set_a_body : a_body -> Set :=
  | lc_set_a_body_anno : forall e1 T1,
    lc_set_a_exp e1 ->
    lc_set_a_typ T1 ->
    lc_set_a_body (a_body_anno e1 T1)

with lc_set_a_exp : a_exp -> Set :=
  | lc_set_a_exp_unit :
    lc_set_a_exp (a_exp_unit)
  | lc_set_a_exp_top :
    lc_set_a_exp (a_exp_top)
  | lc_set_a_exp_var_f : forall x1,
    lc_set_a_exp (a_exp_var_f x1)
  | lc_set_a_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_a_exp (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1))) ->
    lc_set_a_exp (a_exp_abs e1)
  | lc_set_a_exp_app : forall e1 e2,
    lc_set_a_exp e1 ->
    lc_set_a_exp e2 ->
    lc_set_a_exp (a_exp_app e1 e2)
  | lc_set_a_exp_tabs : forall a_body1,
    (forall X1 : typvar, lc_set_a_body (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1))) ->
    lc_set_a_exp (a_exp_tabs a_body1)
  | lc_set_a_exp_tapp : forall e1 T1,
    lc_set_a_exp e1 ->
    lc_set_a_typ T1 ->
    lc_set_a_exp (a_exp_tapp e1 T1)
  | lc_set_a_exp_anno : forall e1 T1,
    lc_set_a_exp e1 ->
    lc_set_a_typ T1 ->
    lc_set_a_exp (a_exp_anno e1 T1).

Scheme lc_a_body_ind' := Induction for lc_a_body Sort Prop
  with lc_a_exp_ind' := Induction for lc_a_exp Sort Prop.

Combined Scheme lc_a_body_lc_a_exp_mutind from lc_a_body_ind',lc_a_exp_ind'.

Scheme lc_set_a_body_ind' := Induction for lc_set_a_body Sort Prop
  with lc_set_a_exp_ind' := Induction for lc_set_a_exp Sort Prop.

Combined Scheme lc_set_a_body_lc_set_a_exp_mutind from lc_set_a_body_ind',lc_set_a_exp_ind'.

Scheme lc_set_a_body_rec' := Induction for lc_set_a_body Sort Set
  with lc_set_a_exp_rec' := Induction for lc_set_a_exp Sort Set.

Combined Scheme lc_set_a_body_lc_set_a_exp_mutrec from lc_set_a_body_rec',lc_set_a_exp_rec'.

#[export] Hint Constructors lc_a_body : core lngen.

#[export] Hint Constructors lc_a_exp : core lngen.

#[export] Hint Constructors lc_set_a_body : core lngen.

#[export] Hint Constructors lc_set_a_exp : core lngen.

Inductive lc_set_a_binding : a_binding -> Set :=
  | lc_set_a_bind_tvarempty :
    lc_set_a_binding (a_bind_tvarempty)
  | lc_set_a_bind_stvarempty :
    lc_set_a_binding (a_bind_stvarempty)
  | lc_set_a_bind_typ : forall T1,
    lc_set_a_typ T1 ->
    lc_set_a_binding (a_bind_typ T1)
  | lc_set_a_bind_bound : forall T1 T2,
    lc_set_a_typ T1 ->
    lc_set_a_typ T2 ->
    lc_set_a_binding (a_bind_bound T1 T2).

Scheme lc_a_binding_ind' := Induction for lc_a_binding Sort Prop.

Combined Scheme lc_a_binding_mutind from lc_a_binding_ind'.

Scheme lc_set_a_binding_ind' := Induction for lc_set_a_binding Sort Prop.

Combined Scheme lc_set_a_binding_mutind from lc_set_a_binding_ind'.

Scheme lc_set_a_binding_rec' := Induction for lc_set_a_binding Sort Set.

Combined Scheme lc_set_a_binding_mutrec from lc_set_a_binding_rec'.

#[export] Hint Constructors lc_a_binding : core lngen.

#[export] Hint Constructors lc_set_a_binding : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_a_typ_wrt_a_typ T1 := forall X1, lc_a_typ (open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1)).

#[export] Hint Unfold body_a_typ_wrt_a_typ : core.

Definition body_a_body_wrt_a_typ a_body1 := forall X1, lc_a_body (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)).

Definition body_a_exp_wrt_a_typ e1 := forall X1, lc_a_exp (open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X1)).

Definition body_a_body_wrt_a_exp a_body1 := forall x1, lc_a_body (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1)).

Definition body_a_exp_wrt_a_exp e1 := forall x1, lc_a_exp (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)).

#[export] Hint Unfold body_a_body_wrt_a_typ : core.

#[export] Hint Unfold body_a_exp_wrt_a_typ : core.

#[export] Hint Unfold body_a_body_wrt_a_exp : core.

#[export] Hint Unfold body_a_exp_wrt_a_exp : core.

Definition body_a_binding_wrt_a_typ b1 := forall X1, lc_a_binding (open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X1)).

#[export] Hint Unfold body_a_binding_wrt_a_typ : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_a_typ_min_mutual :
(forall T1, 1 <= size_a_typ T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_a_typ_min :
forall T1, 1 <= size_a_typ T1.
Proof.
pose proof size_a_typ_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_typ_min : lngen.

(* begin hide *)

Lemma size_a_body_min_size_a_exp_min_mutual :
(forall a_body1, 1 <= size_a_body a_body1) /\
(forall e1, 1 <= size_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_a_body_min :
forall a_body1, 1 <= size_a_body a_body1.
Proof.
pose proof size_a_body_min_size_a_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_min : lngen.

Lemma size_a_exp_min :
forall e1, 1 <= size_a_exp e1.
Proof.
pose proof size_a_body_min_size_a_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_min : lngen.

(* begin hide *)

Lemma size_a_binding_min_mutual :
(forall b1, 1 <= size_a_binding b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_a_binding_min :
forall b1, 1 <= size_a_binding b1.
Proof.
pose proof size_a_binding_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_binding_min : lngen.

(* begin hide *)

Lemma size_a_typ_close_a_typ_wrt_a_typ_rec_mutual :
(forall T1 X1 n1,
  size_a_typ (close_a_typ_wrt_a_typ_rec n1 X1 T1) = size_a_typ T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_typ_close_a_typ_wrt_a_typ_rec :
forall T1 X1 n1,
  size_a_typ (close_a_typ_wrt_a_typ_rec n1 X1 T1) = size_a_typ T1.
Proof.
pose proof size_a_typ_close_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_typ_close_a_typ_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite size_a_typ_close_a_typ_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_body_close_a_body_wrt_a_typ_rec_size_a_exp_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1,
  size_a_body (close_a_body_wrt_a_typ_rec n1 X1 a_body1) = size_a_body a_body1) /\
(forall e1 X1 n1,
  size_a_exp (close_a_exp_wrt_a_typ_rec n1 X1 e1) = size_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_body_close_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1,
  size_a_body (close_a_body_wrt_a_typ_rec n1 X1 a_body1) = size_a_body a_body1.
Proof.
pose proof size_a_body_close_a_body_wrt_a_typ_rec_size_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_close_a_body_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite size_a_body_close_a_body_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_exp_close_a_exp_wrt_a_typ_rec :
forall e1 X1 n1,
  size_a_exp (close_a_exp_wrt_a_typ_rec n1 X1 e1) = size_a_exp e1.
Proof.
pose proof size_a_body_close_a_body_wrt_a_typ_rec_size_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_close_a_exp_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite size_a_exp_close_a_exp_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_body_close_a_body_wrt_a_exp_rec_size_a_exp_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1,
  size_a_body (close_a_body_wrt_a_exp_rec n1 x1 a_body1) = size_a_body a_body1) /\
(forall e1 x1 n1,
  size_a_exp (close_a_exp_wrt_a_exp_rec n1 x1 e1) = size_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_body_close_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1,
  size_a_body (close_a_body_wrt_a_exp_rec n1 x1 a_body1) = size_a_body a_body1.
Proof.
pose proof size_a_body_close_a_body_wrt_a_exp_rec_size_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_close_a_body_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite size_a_body_close_a_body_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_exp_close_a_exp_wrt_a_exp_rec :
forall e1 x1 n1,
  size_a_exp (close_a_exp_wrt_a_exp_rec n1 x1 e1) = size_a_exp e1.
Proof.
pose proof size_a_body_close_a_body_wrt_a_exp_rec_size_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_close_a_exp_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite size_a_exp_close_a_exp_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_binding_close_a_binding_wrt_a_typ_rec_mutual :
(forall b1 X1 n1,
  size_a_binding (close_a_binding_wrt_a_typ_rec n1 X1 b1) = size_a_binding b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_binding_close_a_binding_wrt_a_typ_rec :
forall b1 X1 n1,
  size_a_binding (close_a_binding_wrt_a_typ_rec n1 X1 b1) = size_a_binding b1.
Proof.
pose proof size_a_binding_close_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_binding_close_a_binding_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite size_a_binding_close_a_binding_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_a_typ_close_a_typ_wrt_a_typ :
forall T1 X1,
  size_a_typ (close_a_typ_wrt_a_typ X1 T1) = size_a_typ T1.
Proof.
unfold close_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_typ_close_a_typ_wrt_a_typ : lngen.
#[export] Hint Rewrite size_a_typ_close_a_typ_wrt_a_typ using solve [auto] : lngen.

Lemma size_a_body_close_a_body_wrt_a_typ :
forall a_body1 X1,
  size_a_body (close_a_body_wrt_a_typ X1 a_body1) = size_a_body a_body1.
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_body_close_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite size_a_body_close_a_body_wrt_a_typ using solve [auto] : lngen.

Lemma size_a_exp_close_a_exp_wrt_a_typ :
forall e1 X1,
  size_a_exp (close_a_exp_wrt_a_typ X1 e1) = size_a_exp e1.
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_exp_close_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite size_a_exp_close_a_exp_wrt_a_typ using solve [auto] : lngen.

Lemma size_a_body_close_a_body_wrt_a_exp :
forall a_body1 x1,
  size_a_body (close_a_body_wrt_a_exp x1 a_body1) = size_a_body a_body1.
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve size_a_body_close_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite size_a_body_close_a_body_wrt_a_exp using solve [auto] : lngen.

Lemma size_a_exp_close_a_exp_wrt_a_exp :
forall e1 x1,
  size_a_exp (close_a_exp_wrt_a_exp x1 e1) = size_a_exp e1.
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve size_a_exp_close_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite size_a_exp_close_a_exp_wrt_a_exp using solve [auto] : lngen.

Lemma size_a_binding_close_a_binding_wrt_a_typ :
forall b1 X1,
  size_a_binding (close_a_binding_wrt_a_typ X1 b1) = size_a_binding b1.
Proof.
unfold close_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_binding_close_a_binding_wrt_a_typ : lngen.
#[export] Hint Rewrite size_a_binding_close_a_binding_wrt_a_typ using solve [auto] : lngen.

(* begin hide *)

Lemma size_a_typ_open_a_typ_wrt_a_typ_rec_mutual :
(forall T1 T2 n1,
  size_a_typ T1 <= size_a_typ (open_a_typ_wrt_a_typ_rec n1 T2 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_typ_open_a_typ_wrt_a_typ_rec :
forall T1 T2 n1,
  size_a_typ T1 <= size_a_typ (open_a_typ_wrt_a_typ_rec n1 T2 T1).
Proof.
pose proof size_a_typ_open_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_typ_open_a_typ_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_typ_rec_size_a_exp_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 T1 n1,
  size_a_body a_body1 <= size_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1)) /\
(forall e1 T1 n1,
  size_a_exp e1 <= size_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_typ_rec :
forall a_body1 T1 n1,
  size_a_body a_body1 <= size_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1).
Proof.
pose proof size_a_body_open_a_body_wrt_a_typ_rec_size_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_exp_open_a_exp_wrt_a_typ_rec :
forall e1 T1 n1,
  size_a_exp e1 <= size_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1).
Proof.
pose proof size_a_body_open_a_body_wrt_a_typ_rec_size_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_exp_rec_size_a_exp_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 e1 n1,
  size_a_body a_body1 <= size_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1)) /\
(forall e1 e2 n1,
  size_a_exp e1 <= size_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_exp_rec :
forall a_body1 e1 n1,
  size_a_body a_body1 <= size_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1).
Proof.
pose proof size_a_body_open_a_body_wrt_a_exp_rec_size_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_exp_open_a_exp_wrt_a_exp_rec :
forall e1 e2 n1,
  size_a_exp e1 <= size_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1).
Proof.
pose proof size_a_body_open_a_body_wrt_a_exp_rec_size_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_binding_open_a_binding_wrt_a_typ_rec_mutual :
(forall b1 T1 n1,
  size_a_binding b1 <= size_a_binding (open_a_binding_wrt_a_typ_rec n1 T1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_binding_open_a_binding_wrt_a_typ_rec :
forall b1 T1 n1,
  size_a_binding b1 <= size_a_binding (open_a_binding_wrt_a_typ_rec n1 T1 b1).
Proof.
pose proof size_a_binding_open_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_binding_open_a_binding_wrt_a_typ_rec : lngen.

(* end hide *)

Lemma size_a_typ_open_a_typ_wrt_a_typ :
forall T1 T2,
  size_a_typ T1 <= size_a_typ (open_a_typ_wrt_a_typ T1 T2).
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_typ_open_a_typ_wrt_a_typ : lngen.

Lemma size_a_body_open_a_body_wrt_a_typ :
forall a_body1 T1,
  size_a_body a_body1 <= size_a_body (open_a_body_wrt_a_typ a_body1 T1).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_typ : lngen.

Lemma size_a_exp_open_a_exp_wrt_a_typ :
forall e1 T1,
  size_a_exp e1 <= size_a_exp (open_a_exp_wrt_a_typ e1 T1).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_typ : lngen.

Lemma size_a_body_open_a_body_wrt_a_exp :
forall a_body1 e1,
  size_a_body a_body1 <= size_a_body (open_a_body_wrt_a_exp a_body1 e1).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_exp : lngen.

Lemma size_a_exp_open_a_exp_wrt_a_exp :
forall e1 e2,
  size_a_exp e1 <= size_a_exp (open_a_exp_wrt_a_exp e1 e2).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_exp : lngen.

Lemma size_a_binding_open_a_binding_wrt_a_typ :
forall b1 T1,
  size_a_binding b1 <= size_a_binding (open_a_binding_wrt_a_typ b1 T1).
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_binding_open_a_binding_wrt_a_typ : lngen.

(* begin hide *)

Lemma size_a_typ_open_a_typ_wrt_a_typ_rec_var_mutual :
(forall T1 X1 n1,
  size_a_typ (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1) = size_a_typ T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_typ_open_a_typ_wrt_a_typ_rec_var :
forall T1 X1 n1,
  size_a_typ (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1) = size_a_typ T1.
Proof.
pose proof size_a_typ_open_a_typ_wrt_a_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_typ_open_a_typ_wrt_a_typ_rec_var : lngen.
#[export] Hint Rewrite size_a_typ_open_a_typ_wrt_a_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_typ_rec_var_size_a_exp_open_a_exp_wrt_a_typ_rec_var_mutual :
(forall a_body1 X1 n1,
  size_a_body (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1) = size_a_body a_body1) /\
(forall e1 X1 n1,
  size_a_exp (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1) = size_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_typ_rec_var :
forall a_body1 X1 n1,
  size_a_body (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1) = size_a_body a_body1.
Proof.
pose proof size_a_body_open_a_body_wrt_a_typ_rec_var_size_a_exp_open_a_exp_wrt_a_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_typ_rec_var : lngen.
#[export] Hint Rewrite size_a_body_open_a_body_wrt_a_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_exp_open_a_exp_wrt_a_typ_rec_var :
forall e1 X1 n1,
  size_a_exp (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1) = size_a_exp e1.
Proof.
pose proof size_a_body_open_a_body_wrt_a_typ_rec_var_size_a_exp_open_a_exp_wrt_a_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_typ_rec_var : lngen.
#[export] Hint Rewrite size_a_exp_open_a_exp_wrt_a_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_exp_rec_var_size_a_exp_open_a_exp_wrt_a_exp_rec_var_mutual :
(forall a_body1 x1 n1,
  size_a_body (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1) = size_a_body a_body1) /\
(forall e1 x1 n1,
  size_a_exp (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1) = size_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_body_open_a_body_wrt_a_exp_rec_var :
forall a_body1 x1 n1,
  size_a_body (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1) = size_a_body a_body1.
Proof.
pose proof size_a_body_open_a_body_wrt_a_exp_rec_var_size_a_exp_open_a_exp_wrt_a_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_exp_rec_var : lngen.
#[export] Hint Rewrite size_a_body_open_a_body_wrt_a_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_exp_open_a_exp_wrt_a_exp_rec_var :
forall e1 x1 n1,
  size_a_exp (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1) = size_a_exp e1.
Proof.
pose proof size_a_body_open_a_body_wrt_a_exp_rec_var_size_a_exp_open_a_exp_wrt_a_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_exp_rec_var : lngen.
#[export] Hint Rewrite size_a_exp_open_a_exp_wrt_a_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_a_binding_open_a_binding_wrt_a_typ_rec_var_mutual :
(forall b1 X1 n1,
  size_a_binding (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1) = size_a_binding b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_a_binding_open_a_binding_wrt_a_typ_rec_var :
forall b1 X1 n1,
  size_a_binding (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1) = size_a_binding b1.
Proof.
pose proof size_a_binding_open_a_binding_wrt_a_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_a_binding_open_a_binding_wrt_a_typ_rec_var : lngen.
#[export] Hint Rewrite size_a_binding_open_a_binding_wrt_a_typ_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_a_typ_open_a_typ_wrt_a_typ_var :
forall T1 X1,
  size_a_typ (open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1)) = size_a_typ T1.
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_typ_open_a_typ_wrt_a_typ_var : lngen.
#[export] Hint Rewrite size_a_typ_open_a_typ_wrt_a_typ_var using solve [auto] : lngen.

Lemma size_a_body_open_a_body_wrt_a_typ_var :
forall a_body1 X1,
  size_a_body (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)) = size_a_body a_body1.
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_typ_var : lngen.
#[export] Hint Rewrite size_a_body_open_a_body_wrt_a_typ_var using solve [auto] : lngen.

Lemma size_a_exp_open_a_exp_wrt_a_typ_var :
forall e1 X1,
  size_a_exp (open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X1)) = size_a_exp e1.
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_typ_var : lngen.
#[export] Hint Rewrite size_a_exp_open_a_exp_wrt_a_typ_var using solve [auto] : lngen.

Lemma size_a_body_open_a_body_wrt_a_exp_var :
forall a_body1 x1,
  size_a_body (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1)) = size_a_body a_body1.
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve size_a_body_open_a_body_wrt_a_exp_var : lngen.
#[export] Hint Rewrite size_a_body_open_a_body_wrt_a_exp_var using solve [auto] : lngen.

Lemma size_a_exp_open_a_exp_wrt_a_exp_var :
forall e1 x1,
  size_a_exp (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)) = size_a_exp e1.
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve size_a_exp_open_a_exp_wrt_a_exp_var : lngen.
#[export] Hint Rewrite size_a_exp_open_a_exp_wrt_a_exp_var using solve [auto] : lngen.

Lemma size_a_binding_open_a_binding_wrt_a_typ_var :
forall b1 X1,
  size_a_binding (open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X1)) = size_a_binding b1.
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve size_a_binding_open_a_binding_wrt_a_typ_var : lngen.
#[export] Hint Rewrite size_a_binding_open_a_binding_wrt_a_typ_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_S_mutual :
(forall n1 T1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_typ_wrt_a_typ (S n1) T1).
Proof.
apply_mutual_ind degree_a_typ_wrt_a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_a_typ_wrt_a_typ_S :
forall n1 T1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_typ_wrt_a_typ (S n1) T1.
Proof.
pose proof degree_a_typ_wrt_a_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_S : lngen.

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_S_degree_a_exp_wrt_a_typ_S_mutual :
(forall n1 a_body1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_body_wrt_a_typ (S n1) a_body1) /\
(forall n1 e1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ (S n1) e1).
Proof.
apply_mutual_ind degree_a_body_wrt_a_typ_degree_a_exp_wrt_a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_a_body_wrt_a_typ_S :
forall n1 a_body1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_body_wrt_a_typ (S n1) a_body1.
Proof.
pose proof degree_a_body_wrt_a_typ_S_degree_a_exp_wrt_a_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_S : lngen.

Lemma degree_a_exp_wrt_a_typ_S :
forall n1 e1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ (S n1) e1.
Proof.
pose proof degree_a_body_wrt_a_typ_S_degree_a_exp_wrt_a_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_S : lngen.

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_S_degree_a_exp_wrt_a_exp_S_mutual :
(forall n1 a_body1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp (S n1) a_body1) /\
(forall n1 e1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp (S n1) e1).
Proof.
apply_mutual_ind degree_a_body_wrt_a_exp_degree_a_exp_wrt_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_a_body_wrt_a_exp_S :
forall n1 a_body1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp (S n1) a_body1.
Proof.
pose proof degree_a_body_wrt_a_exp_S_degree_a_exp_wrt_a_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_S : lngen.

Lemma degree_a_exp_wrt_a_exp_S :
forall n1 e1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp (S n1) e1.
Proof.
pose proof degree_a_body_wrt_a_exp_S_degree_a_exp_wrt_a_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_S : lngen.

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_S_mutual :
(forall n1 b1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  degree_a_binding_wrt_a_typ (S n1) b1).
Proof.
apply_mutual_ind degree_a_binding_wrt_a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_a_binding_wrt_a_typ_S :
forall n1 b1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  degree_a_binding_wrt_a_typ (S n1) b1.
Proof.
pose proof degree_a_binding_wrt_a_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_S : lngen.

Lemma degree_a_typ_wrt_a_typ_O :
forall n1 T1,
  degree_a_typ_wrt_a_typ O T1 ->
  degree_a_typ_wrt_a_typ n1 T1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_O : lngen.

Lemma degree_a_body_wrt_a_typ_O :
forall n1 a_body1,
  degree_a_body_wrt_a_typ O a_body1 ->
  degree_a_body_wrt_a_typ n1 a_body1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_O : lngen.

Lemma degree_a_exp_wrt_a_typ_O :
forall n1 e1,
  degree_a_exp_wrt_a_typ O e1 ->
  degree_a_exp_wrt_a_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_O : lngen.

Lemma degree_a_body_wrt_a_exp_O :
forall n1 a_body1,
  degree_a_body_wrt_a_exp O a_body1 ->
  degree_a_body_wrt_a_exp n1 a_body1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_O : lngen.

Lemma degree_a_exp_wrt_a_exp_O :
forall n1 e1,
  degree_a_exp_wrt_a_exp O e1 ->
  degree_a_exp_wrt_a_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_O : lngen.

Lemma degree_a_binding_wrt_a_typ_O :
forall n1 b1,
  degree_a_binding_wrt_a_typ O b1 ->
  degree_a_binding_wrt_a_typ n1 b1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_O : lngen.

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec_mutual :
(forall T1 X1 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_typ_wrt_a_typ (S n1) (close_a_typ_wrt_a_typ_rec n1 X1 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec :
forall T1 X1 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_typ_wrt_a_typ (S n1) (close_a_typ_wrt_a_typ_rec n1 X1 T1).
Proof.
pose proof degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_body_wrt_a_typ (S n1) (close_a_body_wrt_a_typ_rec n1 X1 a_body1)) /\
(forall e1 X1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ (S n1) (close_a_exp_wrt_a_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_body_wrt_a_typ (S n1) (close_a_body_wrt_a_typ_rec n1 X1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec :
forall e1 X1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ (S n1) (close_a_exp_wrt_a_typ_rec n1 X1 e1).
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1 n2,
  degree_a_body_wrt_a_typ n2 a_body1 ->
  degree_a_body_wrt_a_typ n2 (close_a_body_wrt_a_exp_rec n1 x1 a_body1)) /\
(forall e1 x1 n1 n2,
  degree_a_exp_wrt_a_typ n2 e1 ->
  degree_a_exp_wrt_a_typ n2 (close_a_exp_wrt_a_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1 n2,
  degree_a_body_wrt_a_typ n2 a_body1 ->
  degree_a_body_wrt_a_typ n2 (close_a_body_wrt_a_exp_rec n1 x1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec :
forall e1 x1 n1 n2,
  degree_a_exp_wrt_a_typ n2 e1 ->
  degree_a_exp_wrt_a_typ n2 (close_a_exp_wrt_a_exp_rec n1 x1 e1).
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1 n2,
  degree_a_body_wrt_a_exp n2 a_body1 ->
  degree_a_body_wrt_a_exp n2 (close_a_body_wrt_a_typ_rec n1 X1 a_body1)) /\
(forall e1 X1 n1 n2,
  degree_a_exp_wrt_a_exp n2 e1 ->
  degree_a_exp_wrt_a_exp n2 (close_a_exp_wrt_a_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1 n2,
  degree_a_body_wrt_a_exp n2 a_body1 ->
  degree_a_body_wrt_a_exp n2 (close_a_body_wrt_a_typ_rec n1 X1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec :
forall e1 X1 n1 n2,
  degree_a_exp_wrt_a_exp n2 e1 ->
  degree_a_exp_wrt_a_exp n2 (close_a_exp_wrt_a_typ_rec n1 X1 e1).
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp (S n1) (close_a_body_wrt_a_exp_rec n1 x1 a_body1)) /\
(forall e1 x1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp (S n1) (close_a_exp_wrt_a_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp (S n1) (close_a_body_wrt_a_exp_rec n1 x1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec :
forall e1 x1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp (S n1) (close_a_exp_wrt_a_exp_rec n1 x1 e1).
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec_mutual :
(forall b1 X1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  degree_a_binding_wrt_a_typ (S n1) (close_a_binding_wrt_a_typ_rec n1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec :
forall b1 X1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  degree_a_binding_wrt_a_typ (S n1) (close_a_binding_wrt_a_typ_rec n1 X1 b1).
Proof.
pose proof degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec : lngen.

(* end hide *)

Lemma degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ :
forall T1 X1,
  degree_a_typ_wrt_a_typ 0 T1 ->
  degree_a_typ_wrt_a_typ 1 (close_a_typ_wrt_a_typ X1 T1).
Proof.
unfold close_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ : lngen.

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ :
forall a_body1 X1,
  degree_a_body_wrt_a_typ 0 a_body1 ->
  degree_a_body_wrt_a_typ 1 (close_a_body_wrt_a_typ X1 a_body1).
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ : lngen.

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ :
forall e1 X1,
  degree_a_exp_wrt_a_typ 0 e1 ->
  degree_a_exp_wrt_a_typ 1 (close_a_exp_wrt_a_typ X1 e1).
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ : lngen.

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp :
forall a_body1 x1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_body_wrt_a_typ n1 (close_a_body_wrt_a_exp x1 a_body1).
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp : lngen.

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp :
forall e1 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ n1 (close_a_exp_wrt_a_exp x1 e1).
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp : lngen.

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ :
forall a_body1 X1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp n1 (close_a_body_wrt_a_typ X1 a_body1).
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ : lngen.

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ :
forall e1 X1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 (close_a_exp_wrt_a_typ X1 e1).
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ : lngen.

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp :
forall a_body1 x1,
  degree_a_body_wrt_a_exp 0 a_body1 ->
  degree_a_body_wrt_a_exp 1 (close_a_body_wrt_a_exp x1 a_body1).
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp : lngen.

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp :
forall e1 x1,
  degree_a_exp_wrt_a_exp 0 e1 ->
  degree_a_exp_wrt_a_exp 1 (close_a_exp_wrt_a_exp x1 e1).
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp : lngen.

Lemma degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ :
forall b1 X1,
  degree_a_binding_wrt_a_typ 0 b1 ->
  degree_a_binding_wrt_a_typ 1 (close_a_binding_wrt_a_typ X1 b1).
Proof.
unfold close_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ : lngen.

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec_inv_mutual :
(forall T1 X1 n1,
  degree_a_typ_wrt_a_typ (S n1) (close_a_typ_wrt_a_typ_rec n1 X1 T1) ->
  degree_a_typ_wrt_a_typ n1 T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec_inv :
forall T1 X1 n1,
  degree_a_typ_wrt_a_typ (S n1) (close_a_typ_wrt_a_typ_rec n1 X1 T1) ->
  degree_a_typ_wrt_a_typ n1 T1.
Proof.
pose proof degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_inv_mutual :
(forall a_body1 X1 n1,
  degree_a_body_wrt_a_typ (S n1) (close_a_body_wrt_a_typ_rec n1 X1 a_body1) ->
  degree_a_body_wrt_a_typ n1 a_body1) /\
(forall e1 X1 n1,
  degree_a_exp_wrt_a_typ (S n1) (close_a_exp_wrt_a_typ_rec n1 X1 e1) ->
  degree_a_exp_wrt_a_typ n1 e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_inv :
forall a_body1 X1 n1,
  degree_a_body_wrt_a_typ (S n1) (close_a_body_wrt_a_typ_rec n1 X1 a_body1) ->
  degree_a_body_wrt_a_typ n1 a_body1.
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_inv :
forall e1 X1 n1,
  degree_a_exp_wrt_a_typ (S n1) (close_a_exp_wrt_a_typ_rec n1 X1 e1) ->
  degree_a_exp_wrt_a_typ n1 e1.
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_inv_mutual :
(forall a_body1 x1 n1 n2,
  degree_a_body_wrt_a_typ n2 (close_a_body_wrt_a_exp_rec n1 x1 a_body1) ->
  degree_a_body_wrt_a_typ n2 a_body1) /\
(forall e1 x1 n1 n2,
  degree_a_exp_wrt_a_typ n2 (close_a_exp_wrt_a_exp_rec n1 x1 e1) ->
  degree_a_exp_wrt_a_typ n2 e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_inv :
forall a_body1 x1 n1 n2,
  degree_a_body_wrt_a_typ n2 (close_a_body_wrt_a_exp_rec n1 x1 a_body1) ->
  degree_a_body_wrt_a_typ n2 a_body1.
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_a_exp_wrt_a_typ n2 (close_a_exp_wrt_a_exp_rec n1 x1 e1) ->
  degree_a_exp_wrt_a_typ n2 e1.
Proof.
pose proof degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_inv_mutual :
(forall a_body1 X1 n1 n2,
  degree_a_body_wrt_a_exp n2 (close_a_body_wrt_a_typ_rec n1 X1 a_body1) ->
  degree_a_body_wrt_a_exp n2 a_body1) /\
(forall e1 X1 n1 n2,
  degree_a_exp_wrt_a_exp n2 (close_a_exp_wrt_a_typ_rec n1 X1 e1) ->
  degree_a_exp_wrt_a_exp n2 e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_inv :
forall a_body1 X1 n1 n2,
  degree_a_body_wrt_a_exp n2 (close_a_body_wrt_a_typ_rec n1 X1 a_body1) ->
  degree_a_body_wrt_a_exp n2 a_body1.
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_a_exp_wrt_a_exp n2 (close_a_exp_wrt_a_typ_rec n1 X1 e1) ->
  degree_a_exp_wrt_a_exp n2 e1.
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_inv_mutual :
(forall a_body1 x1 n1,
  degree_a_body_wrt_a_exp (S n1) (close_a_body_wrt_a_exp_rec n1 x1 a_body1) ->
  degree_a_body_wrt_a_exp n1 a_body1) /\
(forall e1 x1 n1,
  degree_a_exp_wrt_a_exp (S n1) (close_a_exp_wrt_a_exp_rec n1 x1 e1) ->
  degree_a_exp_wrt_a_exp n1 e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_inv :
forall a_body1 x1 n1,
  degree_a_body_wrt_a_exp (S n1) (close_a_body_wrt_a_exp_rec n1 x1 a_body1) ->
  degree_a_body_wrt_a_exp n1 a_body1.
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_inv :
forall e1 x1 n1,
  degree_a_exp_wrt_a_exp (S n1) (close_a_exp_wrt_a_exp_rec n1 x1 e1) ->
  degree_a_exp_wrt_a_exp n1 e1.
Proof.
pose proof degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec_inv_mutual :
(forall b1 X1 n1,
  degree_a_binding_wrt_a_typ (S n1) (close_a_binding_wrt_a_typ_rec n1 X1 b1) ->
  degree_a_binding_wrt_a_typ n1 b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec_inv :
forall b1 X1 n1,
  degree_a_binding_wrt_a_typ (S n1) (close_a_binding_wrt_a_typ_rec n1 X1 b1) ->
  degree_a_binding_wrt_a_typ n1 b1.
Proof.
pose proof degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_inv :
forall T1 X1,
  degree_a_typ_wrt_a_typ 1 (close_a_typ_wrt_a_typ X1 T1) ->
  degree_a_typ_wrt_a_typ 0 T1.
Proof.
unfold close_a_typ_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ_inv : lngen.

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_inv :
forall a_body1 X1,
  degree_a_body_wrt_a_typ 1 (close_a_body_wrt_a_typ X1 a_body1) ->
  degree_a_body_wrt_a_typ 0 a_body1.
Proof.
unfold close_a_body_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_close_a_body_wrt_a_typ_inv : lngen.

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_inv :
forall e1 X1,
  degree_a_exp_wrt_a_typ 1 (close_a_exp_wrt_a_typ X1 e1) ->
  degree_a_exp_wrt_a_typ 0 e1.
Proof.
unfold close_a_exp_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ_inv : lngen.

Lemma degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_inv :
forall a_body1 x1 n1,
  degree_a_body_wrt_a_typ n1 (close_a_body_wrt_a_exp x1 a_body1) ->
  degree_a_body_wrt_a_typ n1 a_body1.
Proof.
unfold close_a_body_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_close_a_body_wrt_a_exp_inv : lngen.

Lemma degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_inv :
forall e1 x1 n1,
  degree_a_exp_wrt_a_typ n1 (close_a_exp_wrt_a_exp x1 e1) ->
  degree_a_exp_wrt_a_typ n1 e1.
Proof.
unfold close_a_exp_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_close_a_exp_wrt_a_exp_inv : lngen.

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_inv :
forall a_body1 X1 n1,
  degree_a_body_wrt_a_exp n1 (close_a_body_wrt_a_typ X1 a_body1) ->
  degree_a_body_wrt_a_exp n1 a_body1.
Proof.
unfold close_a_body_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_close_a_body_wrt_a_typ_inv : lngen.

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_inv :
forall e1 X1 n1,
  degree_a_exp_wrt_a_exp n1 (close_a_exp_wrt_a_typ X1 e1) ->
  degree_a_exp_wrt_a_exp n1 e1.
Proof.
unfold close_a_exp_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_typ_inv : lngen.

Lemma degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_inv :
forall a_body1 x1,
  degree_a_body_wrt_a_exp 1 (close_a_body_wrt_a_exp x1 a_body1) ->
  degree_a_body_wrt_a_exp 0 a_body1.
Proof.
unfold close_a_body_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_close_a_body_wrt_a_exp_inv : lngen.

Lemma degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_inv :
forall e1 x1,
  degree_a_exp_wrt_a_exp 1 (close_a_exp_wrt_a_exp x1 e1) ->
  degree_a_exp_wrt_a_exp 0 e1.
Proof.
unfold close_a_exp_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp_inv : lngen.

Lemma degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_inv :
forall b1 X1,
  degree_a_binding_wrt_a_typ 1 (close_a_binding_wrt_a_typ X1 b1) ->
  degree_a_binding_wrt_a_typ 0 b1.
Proof.
unfold close_a_binding_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ_inv : lngen.

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec_mutual :
(forall T1 T2 n1,
  degree_a_typ_wrt_a_typ (S n1) T1 ->
  degree_a_typ_wrt_a_typ n1 T2 ->
  degree_a_typ_wrt_a_typ n1 (open_a_typ_wrt_a_typ_rec n1 T2 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec :
forall T1 T2 n1,
  degree_a_typ_wrt_a_typ (S n1) T1 ->
  degree_a_typ_wrt_a_typ n1 T2 ->
  degree_a_typ_wrt_a_typ n1 (open_a_typ_wrt_a_typ_rec n1 T2 T1).
Proof.
pose proof degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 T1 n1,
  degree_a_body_wrt_a_typ (S n1) a_body1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_typ_rec n1 T1 a_body1)) /\
(forall e1 T1 n1,
  degree_a_exp_wrt_a_typ (S n1) e1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec :
forall a_body1 T1 n1,
  degree_a_body_wrt_a_typ (S n1) a_body1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_typ_rec n1 T1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec :
forall e1 T1 n1,
  degree_a_exp_wrt_a_typ (S n1) e1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_typ_rec n1 T1 e1).
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 e1 n1 n2,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_exp_rec n2 e1 a_body1)) /\
(forall e1 e2 n1 n2,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ n1 e2 ->
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec :
forall a_body1 e1 n1 n2,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_exp_rec n2 e1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec :
forall e1 e2 n1 n2,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ n1 e2 ->
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_exp_rec n2 e2 e1).
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 T1 n1 n2,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_typ_rec n2 T1 a_body1)) /\
(forall e1 T1 n1 n2,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_typ_rec n2 T1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec :
forall a_body1 T1 n1 n2,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_typ_rec n2 T1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec :
forall e1 T1 n1 n2,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_typ_rec n2 T1 e1).
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 e1 n1,
  degree_a_body_wrt_a_exp (S n1) a_body1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_exp_rec n1 e1 a_body1)) /\
(forall e1 e2 n1,
  degree_a_exp_wrt_a_exp (S n1) e1 ->
  degree_a_exp_wrt_a_exp n1 e2 ->
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec :
forall a_body1 e1 n1,
  degree_a_body_wrt_a_exp (S n1) a_body1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_exp_rec n1 e1 a_body1).
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec :
forall e1 e2 n1,
  degree_a_exp_wrt_a_exp (S n1) e1 ->
  degree_a_exp_wrt_a_exp n1 e2 ->
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_exp_rec n1 e2 e1).
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec_mutual :
(forall b1 T1 n1,
  degree_a_binding_wrt_a_typ (S n1) b1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_binding_wrt_a_typ n1 (open_a_binding_wrt_a_typ_rec n1 T1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec :
forall b1 T1 n1,
  degree_a_binding_wrt_a_typ (S n1) b1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_binding_wrt_a_typ n1 (open_a_binding_wrt_a_typ_rec n1 T1 b1).
Proof.
pose proof degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec : lngen.

(* end hide *)

Lemma degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ :
forall T1 T2,
  degree_a_typ_wrt_a_typ 1 T1 ->
  degree_a_typ_wrt_a_typ 0 T2 ->
  degree_a_typ_wrt_a_typ 0 (open_a_typ_wrt_a_typ T1 T2).
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ : lngen.

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ :
forall a_body1 T1,
  degree_a_body_wrt_a_typ 1 a_body1 ->
  degree_a_typ_wrt_a_typ 0 T1 ->
  degree_a_body_wrt_a_typ 0 (open_a_body_wrt_a_typ a_body1 T1).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ : lngen.

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ :
forall e1 T1,
  degree_a_exp_wrt_a_typ 1 e1 ->
  degree_a_typ_wrt_a_typ 0 T1 ->
  degree_a_exp_wrt_a_typ 0 (open_a_exp_wrt_a_typ e1 T1).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ : lngen.

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp :
forall a_body1 e1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_exp a_body1 e1).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp : lngen.

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp :
forall e1 e2 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ n1 e2 ->
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_exp e1 e2).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp : lngen.

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ :
forall a_body1 T1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_typ a_body1 T1).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ : lngen.

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ :
forall e1 T1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_typ e1 T1).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ : lngen.

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp :
forall a_body1 e1,
  degree_a_body_wrt_a_exp 1 a_body1 ->
  degree_a_exp_wrt_a_exp 0 e1 ->
  degree_a_body_wrt_a_exp 0 (open_a_body_wrt_a_exp a_body1 e1).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp : lngen.

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp :
forall e1 e2,
  degree_a_exp_wrt_a_exp 1 e1 ->
  degree_a_exp_wrt_a_exp 0 e2 ->
  degree_a_exp_wrt_a_exp 0 (open_a_exp_wrt_a_exp e1 e2).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp : lngen.

Lemma degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ :
forall b1 T1,
  degree_a_binding_wrt_a_typ 1 b1 ->
  degree_a_typ_wrt_a_typ 0 T1 ->
  degree_a_binding_wrt_a_typ 0 (open_a_binding_wrt_a_typ b1 T1).
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ : lngen.

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec_inv_mutual :
(forall T1 T2 n1,
  degree_a_typ_wrt_a_typ n1 (open_a_typ_wrt_a_typ_rec n1 T2 T1) ->
  degree_a_typ_wrt_a_typ (S n1) T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec_inv :
forall T1 T2 n1,
  degree_a_typ_wrt_a_typ n1 (open_a_typ_wrt_a_typ_rec n1 T2 T1) ->
  degree_a_typ_wrt_a_typ (S n1) T1.
Proof.
pose proof degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_inv_mutual :
(forall a_body1 T1 n1,
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_typ_rec n1 T1 a_body1) ->
  degree_a_body_wrt_a_typ (S n1) a_body1) /\
(forall e1 T1 n1,
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_typ_rec n1 T1 e1) ->
  degree_a_exp_wrt_a_typ (S n1) e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_inv :
forall a_body1 T1 n1,
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_typ_rec n1 T1 a_body1) ->
  degree_a_body_wrt_a_typ (S n1) a_body1.
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_inv :
forall e1 T1 n1,
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_typ_rec n1 T1 e1) ->
  degree_a_exp_wrt_a_typ (S n1) e1.
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_inv_mutual :
(forall a_body1 e1 n1 n2,
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_exp_rec n2 e1 a_body1) ->
  degree_a_body_wrt_a_typ n1 a_body1) /\
(forall e1 e2 n1 n2,
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_exp_rec n2 e2 e1) ->
  degree_a_exp_wrt_a_typ n1 e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_inv :
forall a_body1 e1 n1 n2,
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_exp_rec n2 e1 a_body1) ->
  degree_a_body_wrt_a_typ n1 a_body1.
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_exp_rec n2 e2 e1) ->
  degree_a_exp_wrt_a_typ n1 e1.
Proof.
pose proof degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_inv_mutual :
(forall a_body1 T1 n1 n2,
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_typ_rec n2 T1 a_body1) ->
  degree_a_body_wrt_a_exp n1 a_body1) /\
(forall e1 T1 n1 n2,
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_typ_rec n2 T1 e1) ->
  degree_a_exp_wrt_a_exp n1 e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_inv :
forall a_body1 T1 n1 n2,
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_typ_rec n2 T1 a_body1) ->
  degree_a_body_wrt_a_exp n1 a_body1.
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_inv :
forall e1 T1 n1 n2,
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_typ_rec n2 T1 e1) ->
  degree_a_exp_wrt_a_exp n1 e1.
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_rec_inv_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_inv_mutual :
(forall a_body1 e1 n1,
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_exp_rec n1 e1 a_body1) ->
  degree_a_body_wrt_a_exp (S n1) a_body1) /\
(forall e1 e2 n1,
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_exp_rec n1 e2 e1) ->
  degree_a_exp_wrt_a_exp (S n1) e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_inv :
forall a_body1 e1 n1,
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_exp_rec n1 e1 a_body1) ->
  degree_a_body_wrt_a_exp (S n1) a_body1.
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_inv :
forall e1 e2 n1,
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_exp_rec n1 e2 e1) ->
  degree_a_exp_wrt_a_exp (S n1) e1.
Proof.
pose proof degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_rec_inv_degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec_inv_mutual :
(forall b1 T1 n1,
  degree_a_binding_wrt_a_typ n1 (open_a_binding_wrt_a_typ_rec n1 T1 b1) ->
  degree_a_binding_wrt_a_typ (S n1) b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec_inv :
forall b1 T1 n1,
  degree_a_binding_wrt_a_typ n1 (open_a_binding_wrt_a_typ_rec n1 T1 b1) ->
  degree_a_binding_wrt_a_typ (S n1) b1.
Proof.
pose proof degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_inv :
forall T1 T2,
  degree_a_typ_wrt_a_typ 0 (open_a_typ_wrt_a_typ T1 T2) ->
  degree_a_typ_wrt_a_typ 1 T1.
Proof.
unfold open_a_typ_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ_inv : lngen.

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_inv :
forall a_body1 T1,
  degree_a_body_wrt_a_typ 0 (open_a_body_wrt_a_typ a_body1 T1) ->
  degree_a_body_wrt_a_typ 1 a_body1.
Proof.
unfold open_a_body_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_open_a_body_wrt_a_typ_inv : lngen.

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_inv :
forall e1 T1,
  degree_a_exp_wrt_a_typ 0 (open_a_exp_wrt_a_typ e1 T1) ->
  degree_a_exp_wrt_a_typ 1 e1.
Proof.
unfold open_a_exp_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ_inv : lngen.

Lemma degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_inv :
forall a_body1 e1 n1,
  degree_a_body_wrt_a_typ n1 (open_a_body_wrt_a_exp a_body1 e1) ->
  degree_a_body_wrt_a_typ n1 a_body1.
Proof.
unfold open_a_body_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_typ_open_a_body_wrt_a_exp_inv : lngen.

Lemma degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_inv :
forall e1 e2 n1,
  degree_a_exp_wrt_a_typ n1 (open_a_exp_wrt_a_exp e1 e2) ->
  degree_a_exp_wrt_a_typ n1 e1.
Proof.
unfold open_a_exp_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_typ_open_a_exp_wrt_a_exp_inv : lngen.

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_inv :
forall a_body1 T1 n1,
  degree_a_body_wrt_a_exp n1 (open_a_body_wrt_a_typ a_body1 T1) ->
  degree_a_body_wrt_a_exp n1 a_body1.
Proof.
unfold open_a_body_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_open_a_body_wrt_a_typ_inv : lngen.

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_inv :
forall e1 T1 n1,
  degree_a_exp_wrt_a_exp n1 (open_a_exp_wrt_a_typ e1 T1) ->
  degree_a_exp_wrt_a_exp n1 e1.
Proof.
unfold open_a_exp_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_typ_inv : lngen.

Lemma degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_inv :
forall a_body1 e1,
  degree_a_body_wrt_a_exp 0 (open_a_body_wrt_a_exp a_body1 e1) ->
  degree_a_body_wrt_a_exp 1 a_body1.
Proof.
unfold open_a_body_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_body_wrt_a_exp_open_a_body_wrt_a_exp_inv : lngen.

Lemma degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_inv :
forall e1 e2,
  degree_a_exp_wrt_a_exp 0 (open_a_exp_wrt_a_exp e1 e2) ->
  degree_a_exp_wrt_a_exp 1 e1.
Proof.
unfold open_a_exp_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp_inv : lngen.

Lemma degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_inv :
forall b1 T1,
  degree_a_binding_wrt_a_typ 0 (open_a_binding_wrt_a_typ b1 T1) ->
  degree_a_binding_wrt_a_typ 1 b1.
Proof.
unfold open_a_binding_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_a_typ_wrt_a_typ_rec_inj_mutual :
(forall T1 T2 X1 n1,
  close_a_typ_wrt_a_typ_rec n1 X1 T1 = close_a_typ_wrt_a_typ_rec n1 X1 T2 ->
  T1 = T2).
Proof.
apply_mutual_ind a_typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_typ_wrt_a_typ_rec_inj :
forall T1 T2 X1 n1,
  close_a_typ_wrt_a_typ_rec n1 X1 T1 = close_a_typ_wrt_a_typ_rec n1 X1 T2 ->
  T1 = T2.
Proof.
pose proof close_a_typ_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_a_typ_wrt_a_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_typ_rec_inj_close_a_exp_wrt_a_typ_rec_inj_mutual :
(forall a_body1 a_body2 X1 n1,
  close_a_body_wrt_a_typ_rec n1 X1 a_body1 = close_a_body_wrt_a_typ_rec n1 X1 a_body2 ->
  a_body1 = a_body2) /\
(forall e1 e2 X1 n1,
  close_a_exp_wrt_a_typ_rec n1 X1 e1 = close_a_exp_wrt_a_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_typ_rec_inj :
forall a_body1 a_body2 X1 n1,
  close_a_body_wrt_a_typ_rec n1 X1 a_body1 = close_a_body_wrt_a_typ_rec n1 X1 a_body2 ->
  a_body1 = a_body2.
Proof.
pose proof close_a_body_wrt_a_typ_rec_inj_close_a_exp_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_a_body_wrt_a_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_exp_wrt_a_typ_rec_inj :
forall e1 e2 X1 n1,
  close_a_exp_wrt_a_typ_rec n1 X1 e1 = close_a_exp_wrt_a_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_a_body_wrt_a_typ_rec_inj_close_a_exp_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_a_exp_wrt_a_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_exp_rec_inj_close_a_exp_wrt_a_exp_rec_inj_mutual :
(forall a_body1 a_body2 x1 n1,
  close_a_body_wrt_a_exp_rec n1 x1 a_body1 = close_a_body_wrt_a_exp_rec n1 x1 a_body2 ->
  a_body1 = a_body2) /\
(forall e1 e2 x1 n1,
  close_a_exp_wrt_a_exp_rec n1 x1 e1 = close_a_exp_wrt_a_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_exp_rec_inj :
forall a_body1 a_body2 x1 n1,
  close_a_body_wrt_a_exp_rec n1 x1 a_body1 = close_a_body_wrt_a_exp_rec n1 x1 a_body2 ->
  a_body1 = a_body2.
Proof.
pose proof close_a_body_wrt_a_exp_rec_inj_close_a_exp_wrt_a_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_a_body_wrt_a_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_exp_wrt_a_exp_rec_inj :
forall e1 e2 x1 n1,
  close_a_exp_wrt_a_exp_rec n1 x1 e1 = close_a_exp_wrt_a_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_a_body_wrt_a_exp_rec_inj_close_a_exp_wrt_a_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_a_exp_wrt_a_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_binding_wrt_a_typ_rec_inj_mutual :
(forall b1 b2 X1 n1,
  close_a_binding_wrt_a_typ_rec n1 X1 b1 = close_a_binding_wrt_a_typ_rec n1 X1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind a_binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_binding_wrt_a_typ_rec_inj :
forall b1 b2 X1 n1,
  close_a_binding_wrt_a_typ_rec n1 X1 b1 = close_a_binding_wrt_a_typ_rec n1 X1 b2 ->
  b1 = b2.
Proof.
pose proof close_a_binding_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_a_binding_wrt_a_typ_rec_inj : lngen.

(* end hide *)

Lemma close_a_typ_wrt_a_typ_inj :
forall T1 T2 X1,
  close_a_typ_wrt_a_typ X1 T1 = close_a_typ_wrt_a_typ X1 T2 ->
  T1 = T2.
Proof.
unfold close_a_typ_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_a_typ_wrt_a_typ_inj : lngen.

Lemma close_a_body_wrt_a_typ_inj :
forall a_body1 a_body2 X1,
  close_a_body_wrt_a_typ X1 a_body1 = close_a_body_wrt_a_typ X1 a_body2 ->
  a_body1 = a_body2.
Proof.
unfold close_a_body_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_a_body_wrt_a_typ_inj : lngen.

Lemma close_a_exp_wrt_a_typ_inj :
forall e1 e2 X1,
  close_a_exp_wrt_a_typ X1 e1 = close_a_exp_wrt_a_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_a_exp_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_a_exp_wrt_a_typ_inj : lngen.

Lemma close_a_body_wrt_a_exp_inj :
forall a_body1 a_body2 x1,
  close_a_body_wrt_a_exp x1 a_body1 = close_a_body_wrt_a_exp x1 a_body2 ->
  a_body1 = a_body2.
Proof.
unfold close_a_body_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_a_body_wrt_a_exp_inj : lngen.

Lemma close_a_exp_wrt_a_exp_inj :
forall e1 e2 x1,
  close_a_exp_wrt_a_exp x1 e1 = close_a_exp_wrt_a_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_a_exp_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_a_exp_wrt_a_exp_inj : lngen.

Lemma close_a_binding_wrt_a_typ_inj :
forall b1 b2 X1,
  close_a_binding_wrt_a_typ X1 b1 = close_a_binding_wrt_a_typ X1 b2 ->
  b1 = b2.
Proof.
unfold close_a_binding_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_a_binding_wrt_a_typ_inj : lngen.

(* begin hide *)

Lemma close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec_mutual :
(forall T1 X1 n1,
  X1 `notin` ftv_in_a_typ T1 ->
  close_a_typ_wrt_a_typ_rec n1 X1 (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1) = T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec :
forall T1 X1 n1,
  X1 `notin` ftv_in_a_typ T1 ->
  close_a_typ_wrt_a_typ_rec n1 X1 (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1) = T1.
Proof.
pose proof close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1,
  X1 `notin` ftv_in_a_body a_body1 ->
  close_a_body_wrt_a_typ_rec n1 X1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1) = a_body1) /\
(forall e1 X1 n1,
  X1 `notin` ftv_in_a_exp e1 ->
  close_a_exp_wrt_a_typ_rec n1 X1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1) = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1,
  X1 `notin` ftv_in_a_body a_body1 ->
  close_a_body_wrt_a_typ_rec n1 X1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1) = a_body1.
Proof.
pose proof close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec :
forall e1 X1 n1,
  X1 `notin` ftv_in_a_exp e1 ->
  close_a_exp_wrt_a_typ_rec n1 X1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1) = e1.
Proof.
pose proof close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1,
  x1 `notin` fv_in_a_body a_body1 ->
  close_a_body_wrt_a_exp_rec n1 x1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1) = a_body1) /\
(forall e1 x1 n1,
  x1 `notin` fv_in_a_exp e1 ->
  close_a_exp_wrt_a_exp_rec n1 x1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1,
  x1 `notin` fv_in_a_body a_body1 ->
  close_a_body_wrt_a_exp_rec n1 x1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1) = a_body1.
Proof.
pose proof close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec :
forall e1 x1 n1,
  x1 `notin` fv_in_a_exp e1 ->
  close_a_exp_wrt_a_exp_rec n1 x1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1) = e1.
Proof.
pose proof close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec_mutual :
(forall b1 X1 n1,
  X1 `notin` ftv_in_a_binding b1 ->
  close_a_binding_wrt_a_typ_rec n1 X1 (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1) = b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec :
forall b1 X1 n1,
  X1 `notin` ftv_in_a_binding b1 ->
  close_a_binding_wrt_a_typ_rec n1 X1 (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1) = b1.
Proof.
pose proof close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ :
forall T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  close_a_typ_wrt_a_typ X1 (open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1)) = T1.
Proof.
unfold close_a_typ_wrt_a_typ; unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ using solve [auto] : lngen.

Lemma close_a_body_wrt_a_typ_open_a_body_wrt_a_typ :
forall a_body1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  close_a_body_wrt_a_typ X1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)) = a_body1.
Proof.
unfold close_a_body_wrt_a_typ; unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_typ_open_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_typ_open_a_body_wrt_a_typ using solve [auto] : lngen.

Lemma close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ :
forall e1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  close_a_exp_wrt_a_typ X1 (open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X1)) = e1.
Proof.
unfold close_a_exp_wrt_a_typ; unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ using solve [auto] : lngen.

Lemma close_a_body_wrt_a_exp_open_a_body_wrt_a_exp :
forall a_body1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  close_a_body_wrt_a_exp x1 (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1)) = a_body1.
Proof.
unfold close_a_body_wrt_a_exp; unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_exp_open_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_exp_open_a_body_wrt_a_exp using solve [auto] : lngen.

Lemma close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp :
forall e1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  close_a_exp_wrt_a_exp x1 (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)) = e1.
Proof.
unfold close_a_exp_wrt_a_exp; unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp using solve [auto] : lngen.

Lemma close_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ :
forall b1 X1,
  X1 `notin` ftv_in_a_binding b1 ->
  close_a_binding_wrt_a_typ X1 (open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X1)) = b1.
Proof.
unfold close_a_binding_wrt_a_typ; unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_a_typ_wrt_a_typ_rec_close_a_typ_wrt_a_typ_rec_mutual :
(forall T1 X1 n1,
  open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_typ_wrt_a_typ_rec n1 X1 T1) = T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_typ_wrt_a_typ_rec_close_a_typ_wrt_a_typ_rec :
forall T1 X1 n1,
  open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_typ_wrt_a_typ_rec n1 X1 T1) = T1.
Proof.
pose proof open_a_typ_wrt_a_typ_rec_close_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_typ_wrt_a_typ_rec_close_a_typ_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite open_a_typ_wrt_a_typ_rec_close_a_typ_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_typ_rec_close_a_body_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1,
  open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_body_wrt_a_typ_rec n1 X1 a_body1) = a_body1) /\
(forall e1 X1 n1,
  open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_exp_wrt_a_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_typ_rec_close_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1,
  open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_body_wrt_a_typ_rec n1 X1 a_body1) = a_body1.
Proof.
pose proof open_a_body_wrt_a_typ_rec_close_a_body_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_typ_rec_close_a_body_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_typ_rec_close_a_body_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_exp_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec :
forall e1 X1 n1,
  open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_exp_wrt_a_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_a_body_wrt_a_typ_rec_close_a_body_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_typ_rec_close_a_exp_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_exp_rec_close_a_body_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1,
  open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) (close_a_body_wrt_a_exp_rec n1 x1 a_body1) = a_body1) /\
(forall e1 x1 n1,
  open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) (close_a_exp_wrt_a_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_exp_rec_close_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1,
  open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) (close_a_body_wrt_a_exp_rec n1 x1 a_body1) = a_body1.
Proof.
pose proof open_a_body_wrt_a_exp_rec_close_a_body_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_exp_rec_close_a_body_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_exp_rec_close_a_body_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_exp_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec :
forall e1 x1 n1,
  open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) (close_a_exp_wrt_a_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_a_body_wrt_a_exp_rec_close_a_body_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_exp_rec_close_a_exp_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_binding_wrt_a_typ_rec_close_a_binding_wrt_a_typ_rec_mutual :
(forall b1 X1 n1,
  open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_binding_wrt_a_typ_rec n1 X1 b1) = b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_binding_wrt_a_typ_rec_close_a_binding_wrt_a_typ_rec :
forall b1 X1 n1,
  open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) (close_a_binding_wrt_a_typ_rec n1 X1 b1) = b1.
Proof.
pose proof open_a_binding_wrt_a_typ_rec_close_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_binding_wrt_a_typ_rec_close_a_binding_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite open_a_binding_wrt_a_typ_rec_close_a_binding_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ :
forall T1 X1,
  open_a_typ_wrt_a_typ (close_a_typ_wrt_a_typ X1 T1) (a_typ_tvar_f X1) = T1.
Proof.
unfold close_a_typ_wrt_a_typ; unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_typ_wrt_a_typ_close_a_typ_wrt_a_typ using solve [auto] : lngen.

Lemma open_a_body_wrt_a_typ_close_a_body_wrt_a_typ :
forall a_body1 X1,
  open_a_body_wrt_a_typ (close_a_body_wrt_a_typ X1 a_body1) (a_typ_tvar_f X1) = a_body1.
Proof.
unfold close_a_body_wrt_a_typ; unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_typ_close_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_typ_close_a_body_wrt_a_typ using solve [auto] : lngen.

Lemma open_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ :
forall e1 X1,
  open_a_exp_wrt_a_typ (close_a_exp_wrt_a_typ X1 e1) (a_typ_tvar_f X1) = e1.
Proof.
unfold close_a_exp_wrt_a_typ; unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_typ_close_a_exp_wrt_a_typ using solve [auto] : lngen.

Lemma open_a_body_wrt_a_exp_close_a_body_wrt_a_exp :
forall a_body1 x1,
  open_a_body_wrt_a_exp (close_a_body_wrt_a_exp x1 a_body1) (a_exp_var_f x1) = a_body1.
Proof.
unfold close_a_body_wrt_a_exp; unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_exp_close_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_exp_close_a_body_wrt_a_exp using solve [auto] : lngen.

Lemma open_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp :
forall e1 x1,
  open_a_exp_wrt_a_exp (close_a_exp_wrt_a_exp x1 e1) (a_exp_var_f x1) = e1.
Proof.
unfold close_a_exp_wrt_a_exp; unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_exp_close_a_exp_wrt_a_exp using solve [auto] : lngen.

Lemma open_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ :
forall b1 X1,
  open_a_binding_wrt_a_typ (close_a_binding_wrt_a_typ X1 b1) (a_typ_tvar_f X1) = b1.
Proof.
unfold close_a_binding_wrt_a_typ; unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_binding_wrt_a_typ_close_a_binding_wrt_a_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_a_typ_wrt_a_typ_rec_inj_mutual :
(forall T2 T1 X1 n1,
  X1 `notin` ftv_in_a_typ T2 ->
  X1 `notin` ftv_in_a_typ T1 ->
  open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T2 = open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1 ->
  T2 = T1).
Proof.
apply_mutual_ind a_typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_typ_wrt_a_typ_rec_inj :
forall T2 T1 X1 n1,
  X1 `notin` ftv_in_a_typ T2 ->
  X1 `notin` ftv_in_a_typ T1 ->
  open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T2 = open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1 ->
  T2 = T1.
Proof.
pose proof open_a_typ_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_a_typ_wrt_a_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_typ_rec_inj_open_a_exp_wrt_a_typ_rec_inj_mutual :
(forall a_body2 a_body1 X1 n1,
  X1 `notin` ftv_in_a_body a_body2 ->
  X1 `notin` ftv_in_a_body a_body1 ->
  open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body2 = open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1 ->
  a_body2 = a_body1) /\
(forall e2 e1 X1 n1,
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp e1 ->
  open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e2 = open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_typ_rec_inj :
forall a_body2 a_body1 X1 n1,
  X1 `notin` ftv_in_a_body a_body2 ->
  X1 `notin` ftv_in_a_body a_body1 ->
  open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body2 = open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1 ->
  a_body2 = a_body1.
Proof.
pose proof open_a_body_wrt_a_typ_rec_inj_open_a_exp_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_a_body_wrt_a_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_exp_wrt_a_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp e1 ->
  open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e2 = open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_a_body_wrt_a_typ_rec_inj_open_a_exp_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_a_exp_wrt_a_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_exp_rec_inj_open_a_exp_wrt_a_exp_rec_inj_mutual :
(forall a_body2 a_body1 x1 n1,
  x1 `notin` fv_in_a_body a_body2 ->
  x1 `notin` fv_in_a_body a_body1 ->
  open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body2 = open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1 ->
  a_body2 = a_body1) /\
(forall e2 e1 x1 n1,
  x1 `notin` fv_in_a_exp e2 ->
  x1 `notin` fv_in_a_exp e1 ->
  open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e2 = open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_exp_rec_inj :
forall a_body2 a_body1 x1 n1,
  x1 `notin` fv_in_a_body a_body2 ->
  x1 `notin` fv_in_a_body a_body1 ->
  open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body2 = open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1 ->
  a_body2 = a_body1.
Proof.
pose proof open_a_body_wrt_a_exp_rec_inj_open_a_exp_wrt_a_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_a_body_wrt_a_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_exp_wrt_a_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_in_a_exp e2 ->
  x1 `notin` fv_in_a_exp e1 ->
  open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e2 = open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_a_body_wrt_a_exp_rec_inj_open_a_exp_wrt_a_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_a_exp_wrt_a_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_binding_wrt_a_typ_rec_inj_mutual :
(forall b2 b1 X1 n1,
  X1 `notin` ftv_in_a_binding b2 ->
  X1 `notin` ftv_in_a_binding b1 ->
  open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b2 = open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind a_binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_binding_wrt_a_typ_rec_inj :
forall b2 b1 X1 n1,
  X1 `notin` ftv_in_a_binding b2 ->
  X1 `notin` ftv_in_a_binding b1 ->
  open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b2 = open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1 ->
  b2 = b1.
Proof.
pose proof open_a_binding_wrt_a_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_a_binding_wrt_a_typ_rec_inj : lngen.

(* end hide *)

Lemma open_a_typ_wrt_a_typ_inj :
forall T2 T1 X1,
  X1 `notin` ftv_in_a_typ T2 ->
  X1 `notin` ftv_in_a_typ T1 ->
  open_a_typ_wrt_a_typ T2 (a_typ_tvar_f X1) = open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1) ->
  T2 = T1.
Proof.
unfold open_a_typ_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_a_typ_wrt_a_typ_inj : lngen.

Lemma open_a_body_wrt_a_typ_inj :
forall a_body2 a_body1 X1,
  X1 `notin` ftv_in_a_body a_body2 ->
  X1 `notin` ftv_in_a_body a_body1 ->
  open_a_body_wrt_a_typ a_body2 (a_typ_tvar_f X1) = open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1) ->
  a_body2 = a_body1.
Proof.
unfold open_a_body_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_a_body_wrt_a_typ_inj : lngen.

Lemma open_a_exp_wrt_a_typ_inj :
forall e2 e1 X1,
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp e1 ->
  open_a_exp_wrt_a_typ e2 (a_typ_tvar_f X1) = open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X1) ->
  e2 = e1.
Proof.
unfold open_a_exp_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_a_exp_wrt_a_typ_inj : lngen.

Lemma open_a_body_wrt_a_exp_inj :
forall a_body2 a_body1 x1,
  x1 `notin` fv_in_a_body a_body2 ->
  x1 `notin` fv_in_a_body a_body1 ->
  open_a_body_wrt_a_exp a_body2 (a_exp_var_f x1) = open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1) ->
  a_body2 = a_body1.
Proof.
unfold open_a_body_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_a_body_wrt_a_exp_inj : lngen.

Lemma open_a_exp_wrt_a_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_in_a_exp e2 ->
  x1 `notin` fv_in_a_exp e1 ->
  open_a_exp_wrt_a_exp e2 (a_exp_var_f x1) = open_a_exp_wrt_a_exp e1 (a_exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_a_exp_wrt_a_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_a_exp_wrt_a_exp_inj : lngen.

Lemma open_a_binding_wrt_a_typ_inj :
forall b2 b1 X1,
  X1 `notin` ftv_in_a_binding b2 ->
  X1 `notin` ftv_in_a_binding b1 ->
  open_a_binding_wrt_a_typ b2 (a_typ_tvar_f X1) = open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X1) ->
  b2 = b1.
Proof.
unfold open_a_binding_wrt_a_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_a_binding_wrt_a_typ_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_a_typ_wrt_a_typ_of_lc_a_typ_mutual :
(forall T1,
  lc_a_typ T1 ->
  degree_a_typ_wrt_a_typ 0 T1).
Proof.
apply_mutual_ind lc_a_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_a_typ_wrt_a_typ_of_lc_a_typ :
forall T1,
  lc_a_typ T1 ->
  degree_a_typ_wrt_a_typ 0 T1.
Proof.
pose proof degree_a_typ_wrt_a_typ_of_lc_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_typ_wrt_a_typ_of_lc_a_typ : lngen.

(* begin hide *)

Lemma degree_a_body_wrt_a_typ_of_lc_a_body_degree_a_exp_wrt_a_typ_of_lc_a_exp_mutual :
(forall a_body1,
  lc_a_body a_body1 ->
  degree_a_body_wrt_a_typ 0 a_body1) /\
(forall e1,
  lc_a_exp e1 ->
  degree_a_exp_wrt_a_typ 0 e1).
Proof.
apply_mutual_ind lc_a_body_lc_a_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_a_body_wrt_a_typ_of_lc_a_body :
forall a_body1,
  lc_a_body a_body1 ->
  degree_a_body_wrt_a_typ 0 a_body1.
Proof.
pose proof degree_a_body_wrt_a_typ_of_lc_a_body_degree_a_exp_wrt_a_typ_of_lc_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_typ_of_lc_a_body : lngen.

Lemma degree_a_exp_wrt_a_typ_of_lc_a_exp :
forall e1,
  lc_a_exp e1 ->
  degree_a_exp_wrt_a_typ 0 e1.
Proof.
pose proof degree_a_body_wrt_a_typ_of_lc_a_body_degree_a_exp_wrt_a_typ_of_lc_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_typ_of_lc_a_exp : lngen.

(* begin hide *)

Lemma degree_a_body_wrt_a_exp_of_lc_a_body_degree_a_exp_wrt_a_exp_of_lc_a_exp_mutual :
(forall a_body1,
  lc_a_body a_body1 ->
  degree_a_body_wrt_a_exp 0 a_body1) /\
(forall e1,
  lc_a_exp e1 ->
  degree_a_exp_wrt_a_exp 0 e1).
Proof.
apply_mutual_ind lc_a_body_lc_a_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_a_body_wrt_a_exp_of_lc_a_body :
forall a_body1,
  lc_a_body a_body1 ->
  degree_a_body_wrt_a_exp 0 a_body1.
Proof.
pose proof degree_a_body_wrt_a_exp_of_lc_a_body_degree_a_exp_wrt_a_exp_of_lc_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_body_wrt_a_exp_of_lc_a_body : lngen.

Lemma degree_a_exp_wrt_a_exp_of_lc_a_exp :
forall e1,
  lc_a_exp e1 ->
  degree_a_exp_wrt_a_exp 0 e1.
Proof.
pose proof degree_a_body_wrt_a_exp_of_lc_a_body_degree_a_exp_wrt_a_exp_of_lc_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_exp_wrt_a_exp_of_lc_a_exp : lngen.

(* begin hide *)

Lemma degree_a_binding_wrt_a_typ_of_lc_a_binding_mutual :
(forall b1,
  lc_a_binding b1 ->
  degree_a_binding_wrt_a_typ 0 b1).
Proof.
apply_mutual_ind lc_a_binding_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_a_binding_wrt_a_typ_of_lc_a_binding :
forall b1,
  lc_a_binding b1 ->
  degree_a_binding_wrt_a_typ 0 b1.
Proof.
pose proof degree_a_binding_wrt_a_typ_of_lc_a_binding_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_a_binding_wrt_a_typ_of_lc_a_binding : lngen.

(* begin hide *)

Lemma lc_a_typ_of_degree_size_mutual :
forall i1,
(forall T1,
  size_a_typ T1 = i1 ->
  degree_a_typ_wrt_a_typ 0 T1 ->
  lc_a_typ T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind a_typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_a_typ_of_degree :
forall T1,
  degree_a_typ_wrt_a_typ 0 T1 ->
  lc_a_typ T1.
Proof.
intros T1; intros;
pose proof (lc_a_typ_of_degree_size_mutual (size_a_typ T1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_a_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_a_body_of_degree_lc_a_exp_of_degree_size_mutual :
forall i1,
(forall a_body1,
  size_a_body a_body1 = i1 ->
  degree_a_body_wrt_a_typ 0 a_body1 ->
  degree_a_body_wrt_a_exp 0 a_body1 ->
  lc_a_body a_body1) /\
(forall e1,
  size_a_exp e1 = i1 ->
  degree_a_exp_wrt_a_typ 0 e1 ->
  degree_a_exp_wrt_a_exp 0 e1 ->
  lc_a_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind a_body_a_exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_a_body_of_degree :
forall a_body1,
  degree_a_body_wrt_a_typ 0 a_body1 ->
  degree_a_body_wrt_a_exp 0 a_body1 ->
  lc_a_body a_body1.
Proof.
intros a_body1; intros;
pose proof (lc_a_body_of_degree_lc_a_exp_of_degree_size_mutual (size_a_body a_body1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_a_body_of_degree : lngen.

Lemma lc_a_exp_of_degree :
forall e1,
  degree_a_exp_wrt_a_typ 0 e1 ->
  degree_a_exp_wrt_a_exp 0 e1 ->
  lc_a_exp e1.
Proof.
intros e1; intros;
pose proof (lc_a_body_of_degree_lc_a_exp_of_degree_size_mutual (size_a_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_a_exp_of_degree : lngen.

(* begin hide *)

Lemma lc_a_binding_of_degree_size_mutual :
forall i1,
(forall b1,
  size_a_binding b1 = i1 ->
  degree_a_binding_wrt_a_typ 0 b1 ->
  lc_a_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind a_binding_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_a_binding_of_degree :
forall b1,
  degree_a_binding_wrt_a_typ 0 b1 ->
  lc_a_binding b1.
Proof.
intros b1; intros;
pose proof (lc_a_binding_of_degree_size_mutual (size_a_binding b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_a_binding_of_degree : lngen.

Ltac a_typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_a_typ_wrt_a_typ_of_lc_a_typ in J1; clear H
          end).

Ltac a_body_a_exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_a_body_wrt_a_typ_of_lc_a_body in J1;
              let J2 := fresh in pose proof H as J2; apply degree_a_body_wrt_a_exp_of_lc_a_body in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_a_exp_wrt_a_typ_of_lc_a_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_a_exp_wrt_a_exp_of_lc_a_exp in J2; clear H
          end).

Ltac a_binding_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_a_binding_wrt_a_typ_of_lc_a_binding in J1; clear H
          end).

Lemma lc_a_typ_all_exists :
forall X1 T1,
  lc_a_typ (open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1)) ->
  lc_a_typ (a_typ_all T1).
Proof.
intros; a_typ_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_a_exp_abs_exists :
forall x1 e1,
  lc_a_exp (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)) ->
  lc_a_exp (a_exp_abs e1).
Proof.
intros; a_body_a_exp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_a_exp_tabs_exists :
forall X1 a_body1,
  lc_a_body (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)) ->
  lc_a_exp (a_exp_tabs a_body1).
Proof.
intros; a_body_a_exp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_a_typ (a_typ_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_a_typ_all_exists X1) : core.

#[export] Hint Extern 1 (lc_a_exp (a_exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_a_exp (a_exp_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_a_exp_tabs_exists X1) : core.

Lemma lc_body_a_typ_wrt_a_typ :
forall T1 T2,
  body_a_typ_wrt_a_typ T1 ->
  lc_a_typ T2 ->
  lc_a_typ (open_a_typ_wrt_a_typ T1 T2).
Proof.
unfold body_a_typ_wrt_a_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
a_typ_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_a_typ_wrt_a_typ : lngen.

Lemma lc_body_a_body_wrt_a_typ :
forall a_body1 T1,
  body_a_body_wrt_a_typ a_body1 ->
  lc_a_typ T1 ->
  lc_a_body (open_a_body_wrt_a_typ a_body1 T1).
Proof.
unfold body_a_body_wrt_a_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
a_body_a_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_a_body_wrt_a_typ : lngen.

Lemma lc_body_a_exp_wrt_a_typ :
forall e1 T1,
  body_a_exp_wrt_a_typ e1 ->
  lc_a_typ T1 ->
  lc_a_exp (open_a_exp_wrt_a_typ e1 T1).
Proof.
unfold body_a_exp_wrt_a_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
a_body_a_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_a_exp_wrt_a_typ : lngen.

Lemma lc_body_a_body_wrt_a_exp :
forall a_body1 e1,
  body_a_body_wrt_a_exp a_body1 ->
  lc_a_exp e1 ->
  lc_a_body (open_a_body_wrt_a_exp a_body1 e1).
Proof.
unfold body_a_body_wrt_a_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
a_body_a_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_a_body_wrt_a_exp : lngen.

Lemma lc_body_a_exp_wrt_a_exp :
forall e1 e2,
  body_a_exp_wrt_a_exp e1 ->
  lc_a_exp e2 ->
  lc_a_exp (open_a_exp_wrt_a_exp e1 e2).
Proof.
unfold body_a_exp_wrt_a_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
a_body_a_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_a_exp_wrt_a_exp : lngen.

Lemma lc_body_a_binding_wrt_a_typ :
forall b1 T1,
  body_a_binding_wrt_a_typ b1 ->
  lc_a_typ T1 ->
  lc_a_binding (open_a_binding_wrt_a_typ b1 T1).
Proof.
unfold body_a_binding_wrt_a_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
a_binding_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_a_binding_wrt_a_typ : lngen.

Lemma lc_body_a_typ_all_1 :
forall T1,
  lc_a_typ (a_typ_all T1) ->
  body_a_typ_wrt_a_typ T1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_typ_all_1 : lngen.

Lemma lc_body_a_exp_abs_1 :
forall e1,
  lc_a_exp (a_exp_abs e1) ->
  body_a_exp_wrt_a_exp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_exp_abs_1 : lngen.

Lemma lc_body_a_exp_tabs_1 :
forall a_body1,
  lc_a_exp (a_exp_tabs a_body1) ->
  body_a_body_wrt_a_typ a_body1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_exp_tabs_1 : lngen.

(* begin hide *)

Lemma lc_a_typ_unique_mutual :
(forall T1 (proof2 proof3 : lc_a_typ T1), proof2 = proof3).
Proof.
apply_mutual_ind lc_a_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_a_typ_unique :
forall T1 (proof2 proof3 : lc_a_typ T1), proof2 = proof3.
Proof.
pose proof lc_a_typ_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_typ_unique : lngen.

(* begin hide *)

Lemma lc_a_body_unique_lc_a_exp_unique_mutual :
(forall a_body1 (proof2 proof3 : lc_a_body a_body1), proof2 = proof3) /\
(forall e1 (proof2 proof3 : lc_a_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_a_body_lc_a_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_a_body_unique :
forall a_body1 (proof2 proof3 : lc_a_body a_body1), proof2 = proof3.
Proof.
pose proof lc_a_body_unique_lc_a_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_body_unique : lngen.

Lemma lc_a_exp_unique :
forall e1 (proof2 proof3 : lc_a_exp e1), proof2 = proof3.
Proof.
pose proof lc_a_body_unique_lc_a_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_exp_unique : lngen.

(* begin hide *)

Lemma lc_a_binding_unique_mutual :
(forall b1 (proof2 proof3 : lc_a_binding b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_a_binding_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_a_binding_unique :
forall b1 (proof2 proof3 : lc_a_binding b1), proof2 = proof3.
Proof.
pose proof lc_a_binding_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_binding_unique : lngen.

(* begin hide *)

Lemma lc_a_typ_of_lc_set_a_typ_mutual :
(forall T1, lc_set_a_typ T1 -> lc_a_typ T1).
Proof.
apply_mutual_ind lc_set_a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_a_typ_of_lc_set_a_typ :
forall T1, lc_set_a_typ T1 -> lc_a_typ T1.
Proof.
pose proof lc_a_typ_of_lc_set_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_typ_of_lc_set_a_typ : lngen.

(* begin hide *)

Lemma lc_a_body_of_lc_set_a_body_lc_a_exp_of_lc_set_a_exp_mutual :
(forall a_body1, lc_set_a_body a_body1 -> lc_a_body a_body1) /\
(forall e1, lc_set_a_exp e1 -> lc_a_exp e1).
Proof.
apply_mutual_ind lc_set_a_body_lc_set_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_a_body_of_lc_set_a_body :
forall a_body1, lc_set_a_body a_body1 -> lc_a_body a_body1.
Proof.
pose proof lc_a_body_of_lc_set_a_body_lc_a_exp_of_lc_set_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_body_of_lc_set_a_body : lngen.

Lemma lc_a_exp_of_lc_set_a_exp :
forall e1, lc_set_a_exp e1 -> lc_a_exp e1.
Proof.
pose proof lc_a_body_of_lc_set_a_body_lc_a_exp_of_lc_set_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_exp_of_lc_set_a_exp : lngen.

(* begin hide *)

Lemma lc_a_binding_of_lc_set_a_binding_mutual :
(forall b1, lc_set_a_binding b1 -> lc_a_binding b1).
Proof.
apply_mutual_ind lc_set_a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_a_binding_of_lc_set_a_binding :
forall b1, lc_set_a_binding b1 -> lc_a_binding b1.
Proof.
pose proof lc_a_binding_of_lc_set_a_binding_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_a_binding_of_lc_set_a_binding : lngen.

(* begin hide *)

Lemma lc_set_a_typ_of_lc_a_typ_size_mutual :
forall i1,
(forall T1,
  size_a_typ T1 = i1 ->
  lc_a_typ T1 ->
  lc_set_a_typ T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind a_typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_a_typ_of_lc_a_typ];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_a_typ_of_lc_a_typ :
forall T1,
  lc_a_typ T1 ->
  lc_set_a_typ T1.
Proof.
intros T1; intros;
pose proof (lc_set_a_typ_of_lc_a_typ_size_mutual (size_a_typ T1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_a_typ_of_lc_a_typ : lngen.

(* begin hide *)

Lemma lc_set_a_body_of_lc_a_body_lc_set_a_exp_of_lc_a_exp_size_mutual :
forall i1,
(forall a_body1,
  size_a_body a_body1 = i1 ->
  lc_a_body a_body1 ->
  lc_set_a_body a_body1) *
(forall e1,
  size_a_exp e1 = i1 ->
  lc_a_exp e1 ->
  lc_set_a_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind a_body_a_exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_a_typ_of_lc_a_typ
 | apply lc_set_a_body_of_lc_a_body
 | apply lc_set_a_exp_of_lc_a_exp
 | apply lc_set_a_typ_of_lc_a_typ
 | apply lc_set_a_body_of_lc_a_body
 | apply lc_set_a_exp_of_lc_a_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_a_body_of_lc_a_body :
forall a_body1,
  lc_a_body a_body1 ->
  lc_set_a_body a_body1.
Proof.
intros a_body1; intros;
pose proof (lc_set_a_body_of_lc_a_body_lc_set_a_exp_of_lc_a_exp_size_mutual (size_a_body a_body1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_a_body_of_lc_a_body : lngen.

Lemma lc_set_a_exp_of_lc_a_exp :
forall e1,
  lc_a_exp e1 ->
  lc_set_a_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_a_body_of_lc_a_body_lc_set_a_exp_of_lc_a_exp_size_mutual (size_a_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_a_exp_of_lc_a_exp : lngen.

(* begin hide *)

Lemma lc_set_a_binding_of_lc_a_binding_size_mutual :
forall i1,
(forall b1,
  size_a_binding b1 = i1 ->
  lc_a_binding b1 ->
  lc_set_a_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind a_binding_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_a_typ_of_lc_a_typ
 | apply lc_set_a_binding_of_lc_a_binding];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_a_binding_of_lc_a_binding :
forall b1,
  lc_a_binding b1 ->
  lc_set_a_binding b1.
Proof.
intros b1; intros;
pose proof (lc_set_a_binding_of_lc_a_binding_size_mutual (size_a_binding b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_a_binding_of_lc_a_binding : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ_mutual :
(forall T1 X1 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  close_a_typ_wrt_a_typ_rec n1 X1 T1 = T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ :
forall T1 X1 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  close_a_typ_wrt_a_typ_rec n1 X1 T1 = T1.
Proof.
pose proof close_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ_close_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_mutual :
(forall a_body1 X1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  X1 `notin` ftv_in_a_body a_body1 ->
  close_a_body_wrt_a_typ_rec n1 X1 a_body1 = a_body1) /\
(forall e1 X1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  close_a_exp_wrt_a_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ :
forall a_body1 X1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  X1 `notin` ftv_in_a_body a_body1 ->
  close_a_body_wrt_a_typ_rec n1 X1 a_body1 = a_body1.
Proof.
pose proof close_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ_close_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ :
forall e1 X1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  close_a_exp_wrt_a_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ_close_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp_close_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_mutual :
(forall a_body1 x1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  x1 `notin` fv_in_a_body a_body1 ->
  close_a_body_wrt_a_exp_rec n1 x1 a_body1 = a_body1) /\
(forall e1 x1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  x1 `notin` fv_in_a_exp e1 ->
  close_a_exp_wrt_a_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp :
forall a_body1 x1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  x1 `notin` fv_in_a_body a_body1 ->
  close_a_body_wrt_a_exp_rec n1 x1 a_body1 = a_body1.
Proof.
pose proof close_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp_close_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp :
forall e1 x1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  x1 `notin` fv_in_a_exp e1 ->
  close_a_exp_wrt_a_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp_close_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ_mutual :
(forall b1 X1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  X1 `notin` ftv_in_a_binding b1 ->
  close_a_binding_wrt_a_typ_rec n1 X1 b1 = b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ :
forall b1 X1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  X1 `notin` ftv_in_a_binding b1 ->
  close_a_binding_wrt_a_typ_rec n1 X1 b1 = b1.
Proof.
pose proof close_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ : lngen.
#[export] Hint Rewrite close_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

Lemma close_a_typ_wrt_a_typ_lc_a_typ :
forall T1 X1,
  lc_a_typ T1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  close_a_typ_wrt_a_typ X1 T1 = T1.
Proof.
unfold close_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_typ_wrt_a_typ_lc_a_typ : lngen.
#[export] Hint Rewrite close_a_typ_wrt_a_typ_lc_a_typ using solve [auto] : lngen.

Lemma close_a_body_wrt_a_typ_lc_a_body :
forall a_body1 X1,
  lc_a_body a_body1 ->
  X1 `notin` ftv_in_a_body a_body1 ->
  close_a_body_wrt_a_typ X1 a_body1 = a_body1.
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_typ_lc_a_body : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_typ_lc_a_body using solve [auto] : lngen.

Lemma close_a_exp_wrt_a_typ_lc_a_exp :
forall e1 X1,
  lc_a_exp e1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  close_a_exp_wrt_a_typ X1 e1 = e1.
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_typ_lc_a_exp : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_typ_lc_a_exp using solve [auto] : lngen.

Lemma close_a_body_wrt_a_exp_lc_a_body :
forall a_body1 x1,
  lc_a_body a_body1 ->
  x1 `notin` fv_in_a_body a_body1 ->
  close_a_body_wrt_a_exp x1 a_body1 = a_body1.
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve close_a_body_wrt_a_exp_lc_a_body : lngen.
#[export] Hint Rewrite close_a_body_wrt_a_exp_lc_a_body using solve [auto] : lngen.

Lemma close_a_exp_wrt_a_exp_lc_a_exp :
forall e1 x1,
  lc_a_exp e1 ->
  x1 `notin` fv_in_a_exp e1 ->
  close_a_exp_wrt_a_exp x1 e1 = e1.
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve close_a_exp_wrt_a_exp_lc_a_exp : lngen.
#[export] Hint Rewrite close_a_exp_wrt_a_exp_lc_a_exp using solve [auto] : lngen.

Lemma close_a_binding_wrt_a_typ_lc_a_binding :
forall b1 X1,
  lc_a_binding b1 ->
  X1 `notin` ftv_in_a_binding b1 ->
  close_a_binding_wrt_a_typ X1 b1 = b1.
Proof.
unfold close_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve close_a_binding_wrt_a_typ_lc_a_binding : lngen.
#[export] Hint Rewrite close_a_binding_wrt_a_typ_lc_a_binding using solve [auto] : lngen.

(* begin hide *)

Lemma open_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ_mutual :
(forall T2 T1 n1,
  degree_a_typ_wrt_a_typ n1 T2 ->
  open_a_typ_wrt_a_typ_rec n1 T1 T2 = T2).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ :
forall T2 T1 n1,
  degree_a_typ_wrt_a_typ n1 T2 ->
  open_a_typ_wrt_a_typ_rec n1 T1 T2 = T2.
Proof.
pose proof open_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_typ_wrt_a_typ_rec_degree_a_typ_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ_open_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_mutual :
(forall a_body1 T1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  open_a_body_wrt_a_typ_rec n1 T1 a_body1 = a_body1) /\
(forall e1 T1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  open_a_exp_wrt_a_typ_rec n1 T1 e1 = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ :
forall a_body1 T1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  open_a_body_wrt_a_typ_rec n1 T1 a_body1 = a_body1.
Proof.
pose proof open_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ_open_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ :
forall e1 T1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  open_a_exp_wrt_a_typ_rec n1 T1 e1 = e1.
Proof.
pose proof open_a_body_wrt_a_typ_rec_degree_a_body_wrt_a_typ_open_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_typ_rec_degree_a_exp_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp_open_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_mutual :
(forall a_body1 e1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  open_a_body_wrt_a_exp_rec n1 e1 a_body1 = a_body1) /\
(forall e2 e1 n1,
  degree_a_exp_wrt_a_exp n1 e2 ->
  open_a_exp_wrt_a_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp :
forall a_body1 e1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  open_a_body_wrt_a_exp_rec n1 e1 a_body1 = a_body1.
Proof.
pose proof open_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp_open_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp :
forall e2 e1 n1,
  degree_a_exp_wrt_a_exp n1 e2 ->
  open_a_exp_wrt_a_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_a_body_wrt_a_exp_rec_degree_a_body_wrt_a_exp_open_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_exp_rec_degree_a_exp_wrt_a_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ_mutual :
(forall b1 T1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  open_a_binding_wrt_a_typ_rec n1 T1 b1 = b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ :
forall b1 T1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  open_a_binding_wrt_a_typ_rec n1 T1 b1 = b1.
Proof.
pose proof open_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ : lngen.
#[export] Hint Rewrite open_a_binding_wrt_a_typ_rec_degree_a_binding_wrt_a_typ using solve [auto] : lngen.

(* end hide *)

Lemma open_a_typ_wrt_a_typ_lc_a_typ :
forall T2 T1,
  lc_a_typ T2 ->
  open_a_typ_wrt_a_typ T2 T1 = T2.
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_typ_wrt_a_typ_lc_a_typ : lngen.
#[export] Hint Rewrite open_a_typ_wrt_a_typ_lc_a_typ using solve [auto] : lngen.

Lemma open_a_body_wrt_a_typ_lc_a_body :
forall a_body1 T1,
  lc_a_body a_body1 ->
  open_a_body_wrt_a_typ a_body1 T1 = a_body1.
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_typ_lc_a_body : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_typ_lc_a_body using solve [auto] : lngen.

Lemma open_a_exp_wrt_a_typ_lc_a_exp :
forall e1 T1,
  lc_a_exp e1 ->
  open_a_exp_wrt_a_typ e1 T1 = e1.
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_typ_lc_a_exp : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_typ_lc_a_exp using solve [auto] : lngen.

Lemma open_a_body_wrt_a_exp_lc_a_body :
forall a_body1 e1,
  lc_a_body a_body1 ->
  open_a_body_wrt_a_exp a_body1 e1 = a_body1.
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve open_a_body_wrt_a_exp_lc_a_body : lngen.
#[export] Hint Rewrite open_a_body_wrt_a_exp_lc_a_body using solve [auto] : lngen.

Lemma open_a_exp_wrt_a_exp_lc_a_exp :
forall e2 e1,
  lc_a_exp e2 ->
  open_a_exp_wrt_a_exp e2 e1 = e2.
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve open_a_exp_wrt_a_exp_lc_a_exp : lngen.
#[export] Hint Rewrite open_a_exp_wrt_a_exp_lc_a_exp using solve [auto] : lngen.

Lemma open_a_binding_wrt_a_typ_lc_a_binding :
forall b1 T1,
  lc_a_binding b1 ->
  open_a_binding_wrt_a_typ b1 T1 = b1.
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve open_a_binding_wrt_a_typ_lc_a_binding : lngen.
#[export] Hint Rewrite open_a_binding_wrt_a_typ_lc_a_binding using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftv_in_a_typ_close_a_typ_wrt_a_typ_rec_mutual :
(forall T1 X1 n1,
  ftv_in_a_typ (close_a_typ_wrt_a_typ_rec n1 X1 T1) [=] remove X1 (ftv_in_a_typ T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_typ_close_a_typ_wrt_a_typ_rec :
forall T1 X1 n1,
  ftv_in_a_typ (close_a_typ_wrt_a_typ_rec n1 X1 T1) [=] remove X1 (ftv_in_a_typ T1).
Proof.
pose proof ftv_in_a_typ_close_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_close_a_typ_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite ftv_in_a_typ_close_a_typ_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_close_a_body_wrt_a_typ_rec_ftv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1,
  ftv_in_a_body (close_a_body_wrt_a_typ_rec n1 X1 a_body1) [=] remove X1 (ftv_in_a_body a_body1)) /\
(forall e1 X1 n1,
  ftv_in_a_exp (close_a_exp_wrt_a_typ_rec n1 X1 e1) [=] remove X1 (ftv_in_a_exp e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_close_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1,
  ftv_in_a_body (close_a_body_wrt_a_typ_rec n1 X1 a_body1) [=] remove X1 (ftv_in_a_body a_body1).
Proof.
pose proof ftv_in_a_body_close_a_body_wrt_a_typ_rec_ftv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_close_a_body_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite ftv_in_a_body_close_a_body_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_exp_close_a_exp_wrt_a_typ_rec :
forall e1 X1 n1,
  ftv_in_a_exp (close_a_exp_wrt_a_typ_rec n1 X1 e1) [=] remove X1 (ftv_in_a_exp e1).
Proof.
pose proof ftv_in_a_body_close_a_body_wrt_a_typ_rec_ftv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_close_a_exp_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite ftv_in_a_exp_close_a_exp_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_close_a_body_wrt_a_exp_rec_ftv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1,
  ftv_in_a_body (close_a_body_wrt_a_exp_rec n1 x1 a_body1) [=] ftv_in_a_body a_body1) /\
(forall e1 x1 n1,
  ftv_in_a_exp (close_a_exp_wrt_a_exp_rec n1 x1 e1) [=] ftv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_close_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1,
  ftv_in_a_body (close_a_body_wrt_a_exp_rec n1 x1 a_body1) [=] ftv_in_a_body a_body1.
Proof.
pose proof ftv_in_a_body_close_a_body_wrt_a_exp_rec_ftv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_close_a_body_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite ftv_in_a_body_close_a_body_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_exp_close_a_exp_wrt_a_exp_rec :
forall e1 x1 n1,
  ftv_in_a_exp (close_a_exp_wrt_a_exp_rec n1 x1 e1) [=] ftv_in_a_exp e1.
Proof.
pose proof ftv_in_a_body_close_a_body_wrt_a_exp_rec_ftv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_close_a_exp_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite ftv_in_a_exp_close_a_exp_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_close_a_body_wrt_a_typ_rec_fv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 X1 n1,
  fv_in_a_body (close_a_body_wrt_a_typ_rec n1 X1 a_body1) [=] fv_in_a_body a_body1) /\
(forall e1 X1 n1,
  fv_in_a_exp (close_a_exp_wrt_a_typ_rec n1 X1 e1) [=] fv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_close_a_body_wrt_a_typ_rec :
forall a_body1 X1 n1,
  fv_in_a_body (close_a_body_wrt_a_typ_rec n1 X1 a_body1) [=] fv_in_a_body a_body1.
Proof.
pose proof fv_in_a_body_close_a_body_wrt_a_typ_rec_fv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_close_a_body_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite fv_in_a_body_close_a_body_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_exp_close_a_exp_wrt_a_typ_rec :
forall e1 X1 n1,
  fv_in_a_exp (close_a_exp_wrt_a_typ_rec n1 X1 e1) [=] fv_in_a_exp e1.
Proof.
pose proof fv_in_a_body_close_a_body_wrt_a_typ_rec_fv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_close_a_exp_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite fv_in_a_exp_close_a_exp_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_close_a_body_wrt_a_exp_rec_fv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 x1 n1,
  fv_in_a_body (close_a_body_wrt_a_exp_rec n1 x1 a_body1) [=] remove x1 (fv_in_a_body a_body1)) /\
(forall e1 x1 n1,
  fv_in_a_exp (close_a_exp_wrt_a_exp_rec n1 x1 e1) [=] remove x1 (fv_in_a_exp e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_close_a_body_wrt_a_exp_rec :
forall a_body1 x1 n1,
  fv_in_a_body (close_a_body_wrt_a_exp_rec n1 x1 a_body1) [=] remove x1 (fv_in_a_body a_body1).
Proof.
pose proof fv_in_a_body_close_a_body_wrt_a_exp_rec_fv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_close_a_body_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite fv_in_a_body_close_a_body_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_exp_close_a_exp_wrt_a_exp_rec :
forall e1 x1 n1,
  fv_in_a_exp (close_a_exp_wrt_a_exp_rec n1 x1 e1) [=] remove x1 (fv_in_a_exp e1).
Proof.
pose proof fv_in_a_body_close_a_body_wrt_a_exp_rec_fv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_close_a_exp_wrt_a_exp_rec : lngen.
#[export] Hint Rewrite fv_in_a_exp_close_a_exp_wrt_a_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_binding_close_a_binding_wrt_a_typ_rec_mutual :
(forall b1 X1 n1,
  ftv_in_a_binding (close_a_binding_wrt_a_typ_rec n1 X1 b1) [=] remove X1 (ftv_in_a_binding b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_binding_close_a_binding_wrt_a_typ_rec :
forall b1 X1 n1,
  ftv_in_a_binding (close_a_binding_wrt_a_typ_rec n1 X1 b1) [=] remove X1 (ftv_in_a_binding b1).
Proof.
pose proof ftv_in_a_binding_close_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_close_a_binding_wrt_a_typ_rec : lngen.
#[export] Hint Rewrite ftv_in_a_binding_close_a_binding_wrt_a_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftv_in_a_typ_close_a_typ_wrt_a_typ :
forall T1 X1,
  ftv_in_a_typ (close_a_typ_wrt_a_typ X1 T1) [=] remove X1 (ftv_in_a_typ T1).
Proof.
unfold close_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_typ_close_a_typ_wrt_a_typ : lngen.
#[export] Hint Rewrite ftv_in_a_typ_close_a_typ_wrt_a_typ using solve [auto] : lngen.

Lemma ftv_in_a_body_close_a_body_wrt_a_typ :
forall a_body1 X1,
  ftv_in_a_body (close_a_body_wrt_a_typ X1 a_body1) [=] remove X1 (ftv_in_a_body a_body1).
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_body_close_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite ftv_in_a_body_close_a_body_wrt_a_typ using solve [auto] : lngen.

Lemma ftv_in_a_exp_close_a_exp_wrt_a_typ :
forall e1 X1,
  ftv_in_a_exp (close_a_exp_wrt_a_typ X1 e1) [=] remove X1 (ftv_in_a_exp e1).
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_exp_close_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite ftv_in_a_exp_close_a_exp_wrt_a_typ using solve [auto] : lngen.

Lemma ftv_in_a_body_close_a_body_wrt_a_exp :
forall a_body1 x1,
  ftv_in_a_body (close_a_body_wrt_a_exp x1 a_body1) [=] ftv_in_a_body a_body1.
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_body_close_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite ftv_in_a_body_close_a_body_wrt_a_exp using solve [auto] : lngen.

Lemma ftv_in_a_exp_close_a_exp_wrt_a_exp :
forall e1 x1,
  ftv_in_a_exp (close_a_exp_wrt_a_exp x1 e1) [=] ftv_in_a_exp e1.
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_exp_close_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite ftv_in_a_exp_close_a_exp_wrt_a_exp using solve [auto] : lngen.

Lemma fv_in_a_body_close_a_body_wrt_a_typ :
forall a_body1 X1,
  fv_in_a_body (close_a_body_wrt_a_typ X1 a_body1) [=] fv_in_a_body a_body1.
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_body_close_a_body_wrt_a_typ : lngen.
#[export] Hint Rewrite fv_in_a_body_close_a_body_wrt_a_typ using solve [auto] : lngen.

Lemma fv_in_a_exp_close_a_exp_wrt_a_typ :
forall e1 X1,
  fv_in_a_exp (close_a_exp_wrt_a_typ X1 e1) [=] fv_in_a_exp e1.
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_exp_close_a_exp_wrt_a_typ : lngen.
#[export] Hint Rewrite fv_in_a_exp_close_a_exp_wrt_a_typ using solve [auto] : lngen.

Lemma fv_in_a_body_close_a_body_wrt_a_exp :
forall a_body1 x1,
  fv_in_a_body (close_a_body_wrt_a_exp x1 a_body1) [=] remove x1 (fv_in_a_body a_body1).
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_body_close_a_body_wrt_a_exp : lngen.
#[export] Hint Rewrite fv_in_a_body_close_a_body_wrt_a_exp using solve [auto] : lngen.

Lemma fv_in_a_exp_close_a_exp_wrt_a_exp :
forall e1 x1,
  fv_in_a_exp (close_a_exp_wrt_a_exp x1 e1) [=] remove x1 (fv_in_a_exp e1).
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_exp_close_a_exp_wrt_a_exp : lngen.
#[export] Hint Rewrite fv_in_a_exp_close_a_exp_wrt_a_exp using solve [auto] : lngen.

Lemma ftv_in_a_binding_close_a_binding_wrt_a_typ :
forall b1 X1,
  ftv_in_a_binding (close_a_binding_wrt_a_typ X1 b1) [=] remove X1 (ftv_in_a_binding b1).
Proof.
unfold close_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_binding_close_a_binding_wrt_a_typ : lngen.
#[export] Hint Rewrite ftv_in_a_binding_close_a_binding_wrt_a_typ using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_lower_mutual :
(forall T1 T2 n1,
  ftv_in_a_typ T1 [<=] ftv_in_a_typ (open_a_typ_wrt_a_typ_rec n1 T2 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_lower :
forall T1 T2 n1,
  ftv_in_a_typ T1 [<=] ftv_in_a_typ (open_a_typ_wrt_a_typ_rec n1 T2 T1).
Proof.
pose proof ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_typ_rec_lower_ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower_mutual :
(forall a_body1 T1 n1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1)) /\
(forall e1 T1 n1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_typ_rec_lower :
forall a_body1 T1 n1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1).
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_typ_rec_lower_ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower :
forall e1 T1 n1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1).
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_typ_rec_lower_ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_exp_rec_lower_ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower_mutual :
(forall a_body1 e1 n1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1)) /\
(forall e1 e2 n1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_exp_rec_lower :
forall a_body1 e1 n1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1).
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_exp_rec_lower_ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower :
forall e1 e2 n1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1).
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_exp_rec_lower_ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_typ_rec_lower_fv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower_mutual :
(forall a_body1 T1 n1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1)) /\
(forall e1 T1 n1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_typ_rec_lower :
forall a_body1 T1 n1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1).
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_typ_rec_lower_fv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower :
forall e1 T1 n1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1).
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_typ_rec_lower_fv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_exp_rec_lower_fv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower_mutual :
(forall a_body1 e1 n1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1)) /\
(forall e1 e2 n1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_exp_rec_lower :
forall a_body1 e1 n1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1).
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_exp_rec_lower_fv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower :
forall e1 e2 n1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1).
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_exp_rec_lower_fv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_lower_mutual :
(forall b1 T1 n1,
  ftv_in_a_binding b1 [<=] ftv_in_a_binding (open_a_binding_wrt_a_typ_rec n1 T1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_lower :
forall b1 T1 n1,
  ftv_in_a_binding b1 [<=] ftv_in_a_binding (open_a_binding_wrt_a_typ_rec n1 T1 b1).
Proof.
pose proof ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_lower : lngen.

(* end hide *)

Lemma ftv_in_a_typ_open_a_typ_wrt_a_typ_lower :
forall T1 T2,
  ftv_in_a_typ T1 [<=] ftv_in_a_typ (open_a_typ_wrt_a_typ T1 T2).
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_typ_open_a_typ_wrt_a_typ_lower : lngen.

Lemma ftv_in_a_body_open_a_body_wrt_a_typ_lower :
forall a_body1 T1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (open_a_body_wrt_a_typ a_body1 T1).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_typ_lower : lngen.

Lemma ftv_in_a_exp_open_a_exp_wrt_a_typ_lower :
forall e1 T1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (open_a_exp_wrt_a_typ e1 T1).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_typ_lower : lngen.

Lemma ftv_in_a_body_open_a_body_wrt_a_exp_lower :
forall a_body1 e1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (open_a_body_wrt_a_exp a_body1 e1).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_exp_lower : lngen.

Lemma ftv_in_a_exp_open_a_exp_wrt_a_exp_lower :
forall e1 e2,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (open_a_exp_wrt_a_exp e1 e2).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_exp_lower : lngen.

Lemma fv_in_a_body_open_a_body_wrt_a_typ_lower :
forall a_body1 T1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (open_a_body_wrt_a_typ a_body1 T1).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_typ_lower : lngen.

Lemma fv_in_a_exp_open_a_exp_wrt_a_typ_lower :
forall e1 T1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (open_a_exp_wrt_a_typ e1 T1).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_typ_lower : lngen.

Lemma fv_in_a_body_open_a_body_wrt_a_exp_lower :
forall a_body1 e1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (open_a_body_wrt_a_exp a_body1 e1).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_exp_lower : lngen.

Lemma fv_in_a_exp_open_a_exp_wrt_a_exp_lower :
forall e1 e2,
  fv_in_a_exp e1 [<=] fv_in_a_exp (open_a_exp_wrt_a_exp e1 e2).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_exp_lower : lngen.

Lemma ftv_in_a_binding_open_a_binding_wrt_a_typ_lower :
forall b1 T1,
  ftv_in_a_binding b1 [<=] ftv_in_a_binding (open_a_binding_wrt_a_typ b1 T1).
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_binding_open_a_binding_wrt_a_typ_lower : lngen.

(* begin hide *)

Lemma ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_upper_mutual :
(forall T1 T2 n1,
  ftv_in_a_typ (open_a_typ_wrt_a_typ_rec n1 T2 T1) [<=] ftv_in_a_typ T2 `union` ftv_in_a_typ T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_upper :
forall T1 T2 n1,
  ftv_in_a_typ (open_a_typ_wrt_a_typ_rec n1 T2 T1) [<=] ftv_in_a_typ T2 `union` ftv_in_a_typ T1.
Proof.
pose proof ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_open_a_typ_wrt_a_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_typ_rec_upper_ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper_mutual :
(forall a_body1 T1 n1,
  ftv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_body a_body1) /\
(forall e1 T1 n1,
  ftv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_typ_rec_upper :
forall a_body1 T1 n1,
  ftv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_body a_body1.
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_typ_rec_upper_ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper :
forall e1 T1 n1,
  ftv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_exp e1.
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_typ_rec_upper_ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_exp_rec_upper_ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper_mutual :
(forall a_body1 e1 n1,
  ftv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1) [<=] ftv_in_a_exp e1 `union` ftv_in_a_body a_body1) /\
(forall e1 e2 n1,
  ftv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1) [<=] ftv_in_a_exp e2 `union` ftv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_body_open_a_body_wrt_a_exp_rec_upper :
forall a_body1 e1 n1,
  ftv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1) [<=] ftv_in_a_exp e1 `union` ftv_in_a_body a_body1.
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_exp_rec_upper_ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper :
forall e1 e2 n1,
  ftv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1) [<=] ftv_in_a_exp e2 `union` ftv_in_a_exp e1.
Proof.
pose proof ftv_in_a_body_open_a_body_wrt_a_exp_rec_upper_ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_typ_rec_upper_fv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper_mutual :
(forall a_body1 T1 n1,
  fv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1) [<=] fv_in_a_body a_body1) /\
(forall e1 T1 n1,
  fv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1) [<=] fv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_typ_rec_upper :
forall a_body1 T1 n1,
  fv_in_a_body (open_a_body_wrt_a_typ_rec n1 T1 a_body1) [<=] fv_in_a_body a_body1.
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_typ_rec_upper_fv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper :
forall e1 T1 n1,
  fv_in_a_exp (open_a_exp_wrt_a_typ_rec n1 T1 e1) [<=] fv_in_a_exp e1.
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_typ_rec_upper_fv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_exp_rec_upper_fv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper_mutual :
(forall a_body1 e1 n1,
  fv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1) [<=] fv_in_a_exp e1 `union` fv_in_a_body a_body1) /\
(forall e1 e2 n1,
  fv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1) [<=] fv_in_a_exp e2 `union` fv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_body_open_a_body_wrt_a_exp_rec_upper :
forall a_body1 e1 n1,
  fv_in_a_body (open_a_body_wrt_a_exp_rec n1 e1 a_body1) [<=] fv_in_a_exp e1 `union` fv_in_a_body a_body1.
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_exp_rec_upper_fv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper :
forall e1 e2 n1,
  fv_in_a_exp (open_a_exp_wrt_a_exp_rec n1 e2 e1) [<=] fv_in_a_exp e2 `union` fv_in_a_exp e1.
Proof.
pose proof fv_in_a_body_open_a_body_wrt_a_exp_rec_upper_fv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_upper_mutual :
(forall b1 T1 n1,
  ftv_in_a_binding (open_a_binding_wrt_a_typ_rec n1 T1 b1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_binding b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_upper :
forall b1 T1 n1,
  ftv_in_a_binding (open_a_binding_wrt_a_typ_rec n1 T1 b1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_binding b1.
Proof.
pose proof ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_open_a_binding_wrt_a_typ_rec_upper : lngen.

(* end hide *)

Lemma ftv_in_a_typ_open_a_typ_wrt_a_typ_upper :
forall T1 T2,
  ftv_in_a_typ (open_a_typ_wrt_a_typ T1 T2) [<=] ftv_in_a_typ T2 `union` ftv_in_a_typ T1.
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_typ_open_a_typ_wrt_a_typ_upper : lngen.

Lemma ftv_in_a_body_open_a_body_wrt_a_typ_upper :
forall a_body1 T1,
  ftv_in_a_body (open_a_body_wrt_a_typ a_body1 T1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_body a_body1.
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_typ_upper : lngen.

Lemma ftv_in_a_exp_open_a_exp_wrt_a_typ_upper :
forall e1 T1,
  ftv_in_a_exp (open_a_exp_wrt_a_typ e1 T1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_exp e1.
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_typ_upper : lngen.

Lemma ftv_in_a_body_open_a_body_wrt_a_exp_upper :
forall a_body1 e1,
  ftv_in_a_body (open_a_body_wrt_a_exp a_body1 e1) [<=] ftv_in_a_exp e1 `union` ftv_in_a_body a_body1.
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_body_open_a_body_wrt_a_exp_upper : lngen.

Lemma ftv_in_a_exp_open_a_exp_wrt_a_exp_upper :
forall e1 e2,
  ftv_in_a_exp (open_a_exp_wrt_a_exp e1 e2) [<=] ftv_in_a_exp e2 `union` ftv_in_a_exp e1.
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_exp_open_a_exp_wrt_a_exp_upper : lngen.

Lemma fv_in_a_body_open_a_body_wrt_a_typ_upper :
forall a_body1 T1,
  fv_in_a_body (open_a_body_wrt_a_typ a_body1 T1) [<=] fv_in_a_body a_body1.
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_typ_upper : lngen.

Lemma fv_in_a_exp_open_a_exp_wrt_a_typ_upper :
forall e1 T1,
  fv_in_a_exp (open_a_exp_wrt_a_typ e1 T1) [<=] fv_in_a_exp e1.
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_typ_upper : lngen.

Lemma fv_in_a_body_open_a_body_wrt_a_exp_upper :
forall a_body1 e1,
  fv_in_a_body (open_a_body_wrt_a_exp a_body1 e1) [<=] fv_in_a_exp e1 `union` fv_in_a_body a_body1.
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_body_open_a_body_wrt_a_exp_upper : lngen.

Lemma fv_in_a_exp_open_a_exp_wrt_a_exp_upper :
forall e1 e2,
  fv_in_a_exp (open_a_exp_wrt_a_exp e1 e2) [<=] fv_in_a_exp e2 `union` fv_in_a_exp e1.
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve fv_in_a_exp_open_a_exp_wrt_a_exp_upper : lngen.

Lemma ftv_in_a_binding_open_a_binding_wrt_a_typ_upper :
forall b1 T1,
  ftv_in_a_binding (open_a_binding_wrt_a_typ b1 T1) [<=] ftv_in_a_typ T1 `union` ftv_in_a_binding b1.
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve ftv_in_a_binding_open_a_binding_wrt_a_typ_upper : lngen.

(* begin hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_fresh_mutual :
(forall T1 T2 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1) [=] ftv_in_a_typ T1).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_fresh :
forall T1 T2 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1) [=] ftv_in_a_typ T1.
Proof.
pose proof ftv_in_a_typ_a_subst_tv_in_a_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_a_subst_tv_in_a_typ_fresh : lngen.
#[export] Hint Rewrite ftv_in_a_typ_a_subst_tv_in_a_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_fresh_ftv_in_a_exp_a_subst_tv_in_a_exp_fresh_mutual :
(forall a_body1 T1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [=] ftv_in_a_body a_body1) /\
(forall e1 T1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [=] ftv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_fresh :
forall a_body1 T1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [=] ftv_in_a_body a_body1.
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_fresh_ftv_in_a_exp_a_subst_tv_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_tv_in_a_body_fresh : lngen.
#[export] Hint Rewrite ftv_in_a_body_a_subst_tv_in_a_body_fresh using solve [auto] : lngen.

Lemma ftv_in_a_exp_a_subst_tv_in_a_exp_fresh :
forall e1 T1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [=] ftv_in_a_exp e1.
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_fresh_ftv_in_a_exp_a_subst_tv_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_tv_in_a_exp_fresh : lngen.
#[export] Hint Rewrite ftv_in_a_exp_a_subst_tv_in_a_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_fresh_ftv_in_a_exp_a_subst_v_in_a_exp_fresh_mutual :
(forall a_body1 T1 X1,
  fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [=] fv_in_a_body a_body1) /\
(forall e1 T1 X1,
  fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [=] fv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_fresh :
forall a_body1 T1 X1,
  fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [=] fv_in_a_body a_body1.
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_fresh_ftv_in_a_exp_a_subst_v_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_v_in_a_body_fresh : lngen.
#[export] Hint Rewrite ftv_in_a_body_a_subst_v_in_a_body_fresh using solve [auto] : lngen.

Lemma ftv_in_a_exp_a_subst_v_in_a_exp_fresh :
forall e1 T1 X1,
  fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [=] fv_in_a_exp e1.
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_fresh_ftv_in_a_exp_a_subst_v_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_v_in_a_exp_fresh : lngen.
#[export] Hint Rewrite ftv_in_a_exp_a_subst_v_in_a_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_fresh_fv_in_a_exp_a_subst_v_in_a_exp_fresh_mutual :
(forall a_body1 e1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1) [=] fv_in_a_body a_body1) /\
(forall e1 e2 x1,
  x1 `notin` fv_in_a_exp e1 ->
  fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1) [=] fv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_fresh :
forall a_body1 e1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1) [=] fv_in_a_body a_body1.
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_fresh_fv_in_a_exp_a_subst_v_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_v_in_a_body_fresh : lngen.
#[export] Hint Rewrite fv_in_a_body_a_subst_v_in_a_body_fresh using solve [auto] : lngen.

Lemma fv_in_a_exp_a_subst_v_in_a_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_in_a_exp e1 ->
  fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1) [=] fv_in_a_exp e1.
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_fresh_fv_in_a_exp_a_subst_v_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_v_in_a_exp_fresh : lngen.
#[export] Hint Rewrite fv_in_a_exp_a_subst_v_in_a_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_fresh_mutual :
(forall b1 T1 X1,
  X1 `notin` ftv_in_a_binding b1 ->
  ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1) [=] ftv_in_a_binding b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_fresh :
forall b1 T1 X1,
  X1 `notin` ftv_in_a_binding b1 ->
  ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1) [=] ftv_in_a_binding b1.
Proof.
pose proof ftv_in_a_binding_a_subst_tv_in_a_binding_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_a_subst_tv_in_a_binding_fresh : lngen.
#[export] Hint Rewrite ftv_in_a_binding_a_subst_tv_in_a_binding_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_lower_mutual :
(forall T1 T2 X1,
  remove X1 (ftv_in_a_typ T1) [<=] ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_lower :
forall T1 T2 X1,
  remove X1 (ftv_in_a_typ T1) [<=] ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1).
Proof.
pose proof ftv_in_a_typ_a_subst_tv_in_a_typ_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_a_subst_tv_in_a_typ_lower : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_lower_ftv_in_a_exp_a_subst_tv_in_a_exp_lower_mutual :
(forall a_body1 T1 X1,
  remove X1 (ftv_in_a_body a_body1) [<=] ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1,
  remove X1 (ftv_in_a_exp e1) [<=] ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_lower :
forall a_body1 T1 X1,
  remove X1 (ftv_in_a_body a_body1) [<=] ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_lower_ftv_in_a_exp_a_subst_tv_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_tv_in_a_body_lower : lngen.

Lemma ftv_in_a_exp_a_subst_tv_in_a_exp_lower :
forall e1 T1 X1,
  remove X1 (ftv_in_a_exp e1) [<=] ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_lower_ftv_in_a_exp_a_subst_tv_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_tv_in_a_exp_lower : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_lower_ftv_in_a_exp_a_subst_v_in_a_exp_lower_mutual :
(forall a_body1 e1 x1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 x1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_lower :
forall a_body1 e1 x1,
  ftv_in_a_body a_body1 [<=] ftv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_lower_ftv_in_a_exp_a_subst_v_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_v_in_a_body_lower : lngen.

Lemma ftv_in_a_exp_a_subst_v_in_a_exp_lower :
forall e1 e2 x1,
  ftv_in_a_exp e1 [<=] ftv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_lower_ftv_in_a_exp_a_subst_v_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_v_in_a_exp_lower : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_tv_in_a_body_lower_fv_in_a_exp_a_subst_tv_in_a_exp_lower_mutual :
(forall a_body1 T1 X1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_tv_in_a_body_lower :
forall a_body1 T1 X1,
  fv_in_a_body a_body1 [<=] fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof fv_in_a_body_a_subst_tv_in_a_body_lower_fv_in_a_exp_a_subst_tv_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_tv_in_a_body_lower : lngen.

Lemma fv_in_a_exp_a_subst_tv_in_a_exp_lower :
forall e1 T1 X1,
  fv_in_a_exp e1 [<=] fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof fv_in_a_body_a_subst_tv_in_a_body_lower_fv_in_a_exp_a_subst_tv_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_tv_in_a_exp_lower : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_lower_fv_in_a_exp_a_subst_v_in_a_exp_lower_mutual :
(forall a_body1 e1 x1,
  remove x1 (fv_in_a_body a_body1) [<=] fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 x1,
  remove x1 (fv_in_a_exp e1) [<=] fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_lower :
forall a_body1 e1 x1,
  remove x1 (fv_in_a_body a_body1) [<=] fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_lower_fv_in_a_exp_a_subst_v_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_v_in_a_body_lower : lngen.

Lemma fv_in_a_exp_a_subst_v_in_a_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_in_a_exp e1) [<=] fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_lower_fv_in_a_exp_a_subst_v_in_a_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_v_in_a_exp_lower : lngen.

(* begin hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_lower_mutual :
(forall b1 T1 X1,
  remove X1 (ftv_in_a_binding b1) [<=] ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_lower :
forall b1 T1 X1,
  remove X1 (ftv_in_a_binding b1) [<=] ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof ftv_in_a_binding_a_subst_tv_in_a_binding_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_a_subst_tv_in_a_binding_lower : lngen.

(* begin hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_notin_mutual :
(forall T1 T2 X1 X2,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_typ T2 ->
  X2 `notin` ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_notin :
forall T1 T2 X1 X2,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_typ T2 ->
  X2 `notin` ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1).
Proof.
pose proof ftv_in_a_typ_a_subst_tv_in_a_typ_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_a_subst_tv_in_a_typ_notin : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_notin_ftv_in_a_exp_a_subst_tv_in_a_exp_notin_mutual :
(forall a_body1 T1 X1 X2,
  X2 `notin` ftv_in_a_body a_body1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1 X2,
  X2 `notin` ftv_in_a_exp e1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_notin :
forall a_body1 T1 X1 X2,
  X2 `notin` ftv_in_a_body a_body1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_notin_ftv_in_a_exp_a_subst_tv_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_tv_in_a_body_notin : lngen.

Lemma ftv_in_a_exp_a_subst_tv_in_a_exp_notin :
forall e1 T1 X1 X2,
  X2 `notin` ftv_in_a_exp e1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_notin_ftv_in_a_exp_a_subst_tv_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_tv_in_a_exp_notin : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_notin_ftv_in_a_exp_a_subst_v_in_a_exp_notin_mutual :
(forall a_body1 e1 x1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  X1 `notin` ftv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 x1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_notin :
forall a_body1 e1 x1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  X1 `notin` ftv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_notin_ftv_in_a_exp_a_subst_v_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_v_in_a_body_notin : lngen.

Lemma ftv_in_a_exp_a_subst_v_in_a_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_notin_ftv_in_a_exp_a_subst_v_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_v_in_a_exp_notin : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_tv_in_a_body_notin_fv_in_a_exp_a_subst_tv_in_a_exp_notin_mutual :
(forall a_body1 T1 X1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  x1 `notin` fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_tv_in_a_body_notin :
forall a_body1 T1 X1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  x1 `notin` fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof fv_in_a_body_a_subst_tv_in_a_body_notin_fv_in_a_exp_a_subst_tv_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_tv_in_a_body_notin : lngen.

Lemma fv_in_a_exp_a_subst_tv_in_a_exp_notin :
forall e1 T1 X1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof fv_in_a_body_a_subst_tv_in_a_body_notin_fv_in_a_exp_a_subst_tv_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_tv_in_a_exp_notin : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_notin_fv_in_a_exp_a_subst_v_in_a_exp_notin_mutual :
(forall a_body1 e1 x1 x2,
  x2 `notin` fv_in_a_body a_body1 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 `notin` fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 x1 x2,
  x2 `notin` fv_in_a_exp e1 ->
  x2 `notin` fv_in_a_exp e2 ->
  x2 `notin` fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_notin :
forall a_body1 e1 x1 x2,
  x2 `notin` fv_in_a_body a_body1 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 `notin` fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_notin_fv_in_a_exp_a_subst_v_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_v_in_a_body_notin : lngen.

Lemma fv_in_a_exp_a_subst_v_in_a_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_in_a_exp e1 ->
  x2 `notin` fv_in_a_exp e2 ->
  x2 `notin` fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_notin_fv_in_a_exp_a_subst_v_in_a_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_v_in_a_exp_notin : lngen.

(* begin hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_notin_mutual :
(forall b1 T1 X1 X2,
  X2 `notin` ftv_in_a_binding b1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_notin :
forall b1 T1 X1 X2,
  X2 `notin` ftv_in_a_binding b1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 `notin` ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof ftv_in_a_binding_a_subst_tv_in_a_binding_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_a_subst_tv_in_a_binding_notin : lngen.

(* begin hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_upper_mutual :
(forall T1 T2 X1,
  ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1) [<=] ftv_in_a_typ T2 `union` remove X1 (ftv_in_a_typ T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_typ_a_subst_tv_in_a_typ_upper :
forall T1 T2 X1,
  ftv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T1) [<=] ftv_in_a_typ T2 `union` remove X1 (ftv_in_a_typ T1).
Proof.
pose proof ftv_in_a_typ_a_subst_tv_in_a_typ_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_typ_a_subst_tv_in_a_typ_upper : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_upper_ftv_in_a_exp_a_subst_tv_in_a_exp_upper_mutual :
(forall a_body1 T1 X1,
  ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [<=] ftv_in_a_typ T1 `union` remove X1 (ftv_in_a_body a_body1)) /\
(forall e1 T1 X1,
  ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [<=] ftv_in_a_typ T1 `union` remove X1 (ftv_in_a_exp e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_tv_in_a_body_upper :
forall a_body1 T1 X1,
  ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [<=] ftv_in_a_typ T1 `union` remove X1 (ftv_in_a_body a_body1).
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_upper_ftv_in_a_exp_a_subst_tv_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_tv_in_a_body_upper : lngen.

Lemma ftv_in_a_exp_a_subst_tv_in_a_exp_upper :
forall e1 T1 X1,
  ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [<=] ftv_in_a_typ T1 `union` remove X1 (ftv_in_a_exp e1).
Proof.
pose proof ftv_in_a_body_a_subst_tv_in_a_body_upper_ftv_in_a_exp_a_subst_tv_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_tv_in_a_exp_upper : lngen.

(* begin hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_upper_ftv_in_a_exp_a_subst_v_in_a_exp_upper_mutual :
(forall a_body1 e1 x1,
  ftv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1) [<=] ftv_in_a_exp e1 `union` ftv_in_a_body a_body1) /\
(forall e1 e2 x1,
  ftv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1) [<=] ftv_in_a_exp e2 `union` ftv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_body_a_subst_v_in_a_body_upper :
forall a_body1 e1 x1,
  ftv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1) [<=] ftv_in_a_exp e1 `union` ftv_in_a_body a_body1.
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_upper_ftv_in_a_exp_a_subst_v_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_body_a_subst_v_in_a_body_upper : lngen.

Lemma ftv_in_a_exp_a_subst_v_in_a_exp_upper :
forall e1 e2 x1,
  ftv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1) [<=] ftv_in_a_exp e2 `union` ftv_in_a_exp e1.
Proof.
pose proof ftv_in_a_body_a_subst_v_in_a_body_upper_ftv_in_a_exp_a_subst_v_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_exp_a_subst_v_in_a_exp_upper : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_tv_in_a_body_upper_fv_in_a_exp_a_subst_tv_in_a_exp_upper_mutual :
(forall a_body1 T1 X1,
  fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [<=] fv_in_a_body a_body1) /\
(forall e1 T1 X1,
  fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [<=] fv_in_a_exp e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_tv_in_a_body_upper :
forall a_body1 T1 X1,
  fv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1) [<=] fv_in_a_body a_body1.
Proof.
pose proof fv_in_a_body_a_subst_tv_in_a_body_upper_fv_in_a_exp_a_subst_tv_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_tv_in_a_body_upper : lngen.

Lemma fv_in_a_exp_a_subst_tv_in_a_exp_upper :
forall e1 T1 X1,
  fv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1) [<=] fv_in_a_exp e1.
Proof.
pose proof fv_in_a_body_a_subst_tv_in_a_body_upper_fv_in_a_exp_a_subst_tv_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_tv_in_a_exp_upper : lngen.

(* begin hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_upper_fv_in_a_exp_a_subst_v_in_a_exp_upper_mutual :
(forall a_body1 e1 x1,
  fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1) [<=] fv_in_a_exp e1 `union` remove x1 (fv_in_a_body a_body1)) /\
(forall e1 e2 x1,
  fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1) [<=] fv_in_a_exp e2 `union` remove x1 (fv_in_a_exp e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_a_body_a_subst_v_in_a_body_upper :
forall a_body1 e1 x1,
  fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1) [<=] fv_in_a_exp e1 `union` remove x1 (fv_in_a_body a_body1).
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_upper_fv_in_a_exp_a_subst_v_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_body_a_subst_v_in_a_body_upper : lngen.

Lemma fv_in_a_exp_a_subst_v_in_a_exp_upper :
forall e1 e2 x1,
  fv_in_a_exp (a_subst_v_in_a_exp e2 x1 e1) [<=] fv_in_a_exp e2 `union` remove x1 (fv_in_a_exp e1).
Proof.
pose proof fv_in_a_body_a_subst_v_in_a_body_upper_fv_in_a_exp_a_subst_v_in_a_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_a_exp_a_subst_v_in_a_exp_upper : lngen.

(* begin hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_upper_mutual :
(forall b1 T1 X1,
  ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1) [<=] ftv_in_a_typ T1 `union` remove X1 (ftv_in_a_binding b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_a_binding_a_subst_tv_in_a_binding_upper :
forall b1 T1 X1,
  ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1) [<=] ftv_in_a_typ T1 `union` remove X1 (ftv_in_a_binding b1).
Proof.
pose proof ftv_in_a_binding_a_subst_tv_in_a_binding_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_a_binding_a_subst_tv_in_a_binding_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec_mutual :
(forall T2 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 (close_a_typ_wrt_a_typ_rec n1 X2 T2) = close_a_typ_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_typ T1 X1 T2)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec :
forall T2 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 (close_a_typ_wrt_a_typ_rec n1 X2 T2) = close_a_typ_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
pose proof a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 (close_a_body_wrt_a_typ_rec n1 X2 a_body1) = close_a_body_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 (close_a_exp_wrt_a_typ_rec n1 X2 e1) = close_a_exp_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec :
forall a_body1 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 (close_a_body_wrt_a_typ_rec n1 X2 a_body1) = close_a_body_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec : lngen.

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec :
forall e1 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 (close_a_exp_wrt_a_typ_rec n1 X2 e1) = close_a_exp_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 T1 x1 X1 n1,
  a_subst_tv_in_a_body T1 x1 (close_a_body_wrt_a_exp_rec n1 X1 a_body1) = close_a_body_wrt_a_exp_rec n1 X1 (a_subst_tv_in_a_body T1 x1 a_body1)) /\
(forall e1 T1 x1 X1 n1,
  a_subst_tv_in_a_exp T1 x1 (close_a_exp_wrt_a_exp_rec n1 X1 e1) = close_a_exp_wrt_a_exp_rec n1 X1 (a_subst_tv_in_a_exp T1 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec :
forall a_body1 T1 x1 X1 n1,
  a_subst_tv_in_a_body T1 x1 (close_a_body_wrt_a_exp_rec n1 X1 a_body1) = close_a_body_wrt_a_exp_rec n1 X1 (a_subst_tv_in_a_body T1 x1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec : lngen.

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec :
forall e1 T1 x1 X1 n1,
  a_subst_tv_in_a_exp T1 x1 (close_a_exp_wrt_a_exp_rec n1 X1 e1) = close_a_exp_wrt_a_exp_rec n1 X1 (a_subst_tv_in_a_exp T1 x1 e1).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 e1 X1 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  x1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 X1 (close_a_body_wrt_a_typ_rec n1 x1 a_body1) = close_a_body_wrt_a_typ_rec n1 x1 (a_subst_v_in_a_body e1 X1 a_body1)) /\
(forall e2 e1 X1 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  x1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_exp e1 X1 (close_a_exp_wrt_a_typ_rec n1 x1 e2) = close_a_exp_wrt_a_typ_rec n1 x1 (a_subst_v_in_a_exp e1 X1 e2)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec :
forall a_body1 e1 X1 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  x1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 X1 (close_a_body_wrt_a_typ_rec n1 x1 a_body1) = close_a_body_wrt_a_typ_rec n1 x1 (a_subst_v_in_a_body e1 X1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec : lngen.

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  x1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_exp e1 X1 (close_a_exp_wrt_a_typ_rec n1 x1 e2) = close_a_exp_wrt_a_typ_rec n1 x1 (a_subst_v_in_a_exp e1 X1 e2).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 e1 x1 x2 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (close_a_body_wrt_a_exp_rec n1 x2 a_body1) = close_a_body_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e2 e1 x1 x2 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (close_a_exp_wrt_a_exp_rec n1 x2 e2) = close_a_exp_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_exp e1 x1 e2)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec :
forall a_body1 e1 x1 x2 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (close_a_body_wrt_a_exp_rec n1 x2 a_body1) = close_a_body_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec : lngen.

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (close_a_exp_wrt_a_exp_rec n1 x2 e2) = close_a_exp_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_exp e1 x1 e2).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec_mutual :
(forall b1 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 (close_a_binding_wrt_a_typ_rec n1 X2 b1) = close_a_binding_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec :
forall b1 T1 X1 X2 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 (close_a_binding_wrt_a_typ_rec n1 X2 b1) = close_a_binding_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec : lngen.

Lemma a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ :
forall T2 T1 X1 X2,
  lc_a_typ T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 (close_a_typ_wrt_a_typ X2 T2) = close_a_typ_wrt_a_typ X2 (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
unfold close_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_typ :
forall a_body1 T1 X1 X2,
  lc_a_typ T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 (close_a_body_wrt_a_typ X2 a_body1) = close_a_body_wrt_a_typ X2 (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ :
forall e1 T1 X1 X2,
  lc_a_typ T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 (close_a_exp_wrt_a_typ X2 e1) = close_a_exp_wrt_a_typ X2 (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_exp :
forall a_body1 T1 x1 X1,
  lc_a_typ T1 ->  a_subst_tv_in_a_body T1 x1 (close_a_body_wrt_a_exp X1 a_body1) = close_a_body_wrt_a_exp X1 (a_subst_tv_in_a_body T1 x1 a_body1).
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp :
forall e1 T1 x1 X1,
  lc_a_typ T1 ->  a_subst_tv_in_a_exp T1 x1 (close_a_exp_wrt_a_exp X1 e1) = close_a_exp_wrt_a_exp X1 (a_subst_tv_in_a_exp T1 x1 e1).
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_typ :
forall a_body1 e1 X1 x1,
  lc_a_exp e1 ->  x1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 X1 (close_a_body_wrt_a_typ x1 a_body1) = close_a_body_wrt_a_typ x1 (a_subst_v_in_a_body e1 X1 a_body1).
Proof.
unfold close_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_typ :
forall e2 e1 X1 x1,
  lc_a_exp e1 ->  x1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_exp e1 X1 (close_a_exp_wrt_a_typ x1 e2) = close_a_exp_wrt_a_typ x1 (a_subst_v_in_a_exp e1 X1 e2).
Proof.
unfold close_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_exp :
forall a_body1 e1 x1 x2,
  lc_a_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (close_a_body_wrt_a_exp x2 a_body1) = close_a_body_wrt_a_exp x2 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
unfold close_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_exp :
forall e2 e1 x1 x2,
  lc_a_exp e1 ->  x1 <> x2 ->
  x2 `notin` fv_in_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (close_a_exp_wrt_a_exp x2 e2) = close_a_exp_wrt_a_exp x2 (a_subst_v_in_a_exp e1 x1 e2).
Proof.
unfold close_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ :
forall b1 T1 X1 X2,
  lc_a_typ T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 (close_a_binding_wrt_a_typ X2 b1) = close_a_binding_wrt_a_typ X2 (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
unfold close_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_degree_a_typ_wrt_a_typ_mutual :
(forall T1 T2 X1 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_typ_wrt_a_typ n1 T2 ->
  degree_a_typ_wrt_a_typ n1 (a_subst_tv_in_a_typ T2 X1 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_degree_a_typ_wrt_a_typ :
forall T1 T2 X1 n1,
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_typ_wrt_a_typ n1 T2 ->
  degree_a_typ_wrt_a_typ n1 (a_subst_tv_in_a_typ T2 X1 T1).
Proof.
pose proof a_subst_tv_in_a_typ_degree_a_typ_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_degree_a_typ_wrt_a_typ : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_degree_a_body_wrt_a_typ_a_subst_tv_in_a_exp_degree_a_exp_wrt_a_typ_mutual :
(forall a_body1 T1 X1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_body_wrt_a_typ n1 (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_exp_wrt_a_typ n1 (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_degree_a_body_wrt_a_typ :
forall a_body1 T1 X1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_body_wrt_a_typ n1 (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_degree_a_body_wrt_a_typ_a_subst_tv_in_a_exp_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_degree_a_body_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_exp_degree_a_exp_wrt_a_typ :
forall e1 T1 X1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_exp_wrt_a_typ n1 (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_degree_a_body_wrt_a_typ_a_subst_tv_in_a_exp_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_degree_a_exp_wrt_a_typ : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_degree_a_body_wrt_a_exp_a_subst_tv_in_a_exp_degree_a_exp_wrt_a_exp_mutual :
(forall a_body1 T1 X1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp n1 (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_degree_a_body_wrt_a_exp :
forall a_body1 T1 X1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_body_wrt_a_exp n1 (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_degree_a_body_wrt_a_exp_a_subst_tv_in_a_exp_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_degree_a_body_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_exp_degree_a_exp_wrt_a_exp :
forall e1 T1 X1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_degree_a_body_wrt_a_exp_a_subst_tv_in_a_exp_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_degree_a_exp_wrt_a_exp : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_degree_a_body_wrt_a_typ_a_subst_v_in_a_exp_degree_a_exp_wrt_a_typ_mutual :
(forall a_body1 e1 x1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_body_wrt_a_typ n1 (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ n1 e2 ->
  degree_a_exp_wrt_a_typ n1 (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_degree_a_body_wrt_a_typ :
forall a_body1 e1 x1 n1,
  degree_a_body_wrt_a_typ n1 a_body1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_body_wrt_a_typ n1 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_degree_a_body_wrt_a_typ_a_subst_v_in_a_exp_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_degree_a_body_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_exp_degree_a_exp_wrt_a_typ :
forall e1 e2 x1 n1,
  degree_a_exp_wrt_a_typ n1 e1 ->
  degree_a_exp_wrt_a_typ n1 e2 ->
  degree_a_exp_wrt_a_typ n1 (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof a_subst_v_in_a_body_degree_a_body_wrt_a_typ_a_subst_v_in_a_exp_degree_a_exp_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_degree_a_exp_wrt_a_typ : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_degree_a_body_wrt_a_exp_a_subst_v_in_a_exp_degree_a_exp_wrt_a_exp_mutual :
(forall a_body1 e1 x1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_body_wrt_a_exp n1 (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 x1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 e2 ->
  degree_a_exp_wrt_a_exp n1 (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_degree_a_body_wrt_a_exp :
forall a_body1 e1 x1 n1,
  degree_a_body_wrt_a_exp n1 a_body1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_body_wrt_a_exp n1 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_degree_a_body_wrt_a_exp_a_subst_v_in_a_exp_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_degree_a_body_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_exp_degree_a_exp_wrt_a_exp :
forall e1 e2 x1 n1,
  degree_a_exp_wrt_a_exp n1 e1 ->
  degree_a_exp_wrt_a_exp n1 e2 ->
  degree_a_exp_wrt_a_exp n1 (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof a_subst_v_in_a_body_degree_a_body_wrt_a_exp_a_subst_v_in_a_exp_degree_a_exp_wrt_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_degree_a_exp_wrt_a_exp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_degree_a_binding_wrt_a_typ_mutual :
(forall b1 T1 X1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_binding_wrt_a_typ n1 (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_degree_a_binding_wrt_a_typ :
forall b1 T1 X1 n1,
  degree_a_binding_wrt_a_typ n1 b1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  degree_a_binding_wrt_a_typ n1 (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof a_subst_tv_in_a_binding_degree_a_binding_wrt_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_degree_a_binding_wrt_a_typ : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_fresh_eq_mutual :
(forall T2 T1 X1,
  X1 `notin` ftv_in_a_typ T2 ->
  a_subst_tv_in_a_typ T1 X1 T2 = T2).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_fresh_eq :
forall T2 T1 X1,
  X1 `notin` ftv_in_a_typ T2 ->
  a_subst_tv_in_a_typ T1 X1 T2 = T2.
Proof.
pose proof a_subst_tv_in_a_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_fresh_eq_a_subst_tv_in_a_exp_fresh_eq_mutual :
(forall a_body1 T1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = a_body1) /\
(forall e1 T1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = e1).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_fresh_eq :
forall a_body1 T1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = a_body1.
Proof.
pose proof a_subst_tv_in_a_body_fresh_eq_a_subst_tv_in_a_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_body_fresh_eq using solve [auto] : lngen.

Lemma a_subst_tv_in_a_exp_fresh_eq :
forall e1 T1 X1,
  X1 `notin` ftv_in_a_exp e1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = e1.
Proof.
pose proof a_subst_tv_in_a_body_fresh_eq_a_subst_tv_in_a_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_fresh_eq_a_subst_v_in_a_exp_fresh_eq_mutual :
(forall a_body1 e1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = a_body1) /\
(forall e2 e1 x1,
  x1 `notin` fv_in_a_exp e2 ->
  a_subst_v_in_a_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_fresh_eq :
forall a_body1 e1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = a_body1.
Proof.
pose proof a_subst_v_in_a_body_fresh_eq_a_subst_v_in_a_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_v_in_a_body_fresh_eq using solve [auto] : lngen.

Lemma a_subst_v_in_a_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_in_a_exp e2 ->
  a_subst_v_in_a_exp e1 x1 e2 = e2.
Proof.
pose proof a_subst_v_in_a_body_fresh_eq_a_subst_v_in_a_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_v_in_a_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_fresh_eq_mutual :
(forall b1 T1 X1,
  X1 `notin` ftv_in_a_binding b1 ->
  a_subst_tv_in_a_binding T1 X1 b1 = b1).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_fresh_eq :
forall b1 T1 X1,
  X1 `notin` ftv_in_a_binding b1 ->
  a_subst_tv_in_a_binding T1 X1 b1 = b1.
Proof.
pose proof a_subst_tv_in_a_binding_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_binding_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_fresh_same_mutual :
(forall T2 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_typ (a_subst_tv_in_a_typ T1 X1 T2)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_fresh_same :
forall T2 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_typ (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
pose proof a_subst_tv_in_a_typ_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_fresh_same_a_subst_tv_in_a_exp_fresh_same_mutual :
(forall a_body1 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_fresh_same :
forall a_body1 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_body (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_fresh_same_a_subst_tv_in_a_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_fresh_same : lngen.

Lemma a_subst_tv_in_a_exp_fresh_same :
forall e1 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_exp (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_fresh_same_a_subst_tv_in_a_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_fresh_same_a_subst_v_in_a_exp_fresh_same_mutual :
(forall a_body1 e1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e2 e1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_exp (a_subst_v_in_a_exp e1 x1 e2)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_fresh_same :
forall a_body1 e1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_body (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_fresh_same_a_subst_v_in_a_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_fresh_same : lngen.

Lemma a_subst_v_in_a_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_exp (a_subst_v_in_a_exp e1 x1 e2).
Proof.
pose proof a_subst_v_in_a_body_fresh_same_a_subst_v_in_a_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_fresh_same_mutual :
(forall b1 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_fresh_same :
forall b1 T1 X1,
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_binding (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof a_subst_tv_in_a_binding_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_fresh_mutual :
(forall T2 T1 X1 X2,
  X1 `notin` ftv_in_a_typ T2 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_typ (a_subst_tv_in_a_typ T1 X2 T2)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_fresh :
forall T2 T1 X1 X2,
  X1 `notin` ftv_in_a_typ T2 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_typ (a_subst_tv_in_a_typ T1 X2 T2).
Proof.
pose proof a_subst_tv_in_a_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_fresh : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_fresh_a_subst_tv_in_a_exp_fresh_mutual :
(forall a_body1 T1 X1 X2,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_body (a_subst_tv_in_a_body T1 X2 a_body1)) /\
(forall e1 T1 X1 X2,
  X1 `notin` ftv_in_a_exp e1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_exp (a_subst_tv_in_a_exp T1 X2 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_fresh :
forall a_body1 T1 X1 X2,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_body (a_subst_tv_in_a_body T1 X2 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_fresh_a_subst_tv_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_fresh : lngen.

Lemma a_subst_tv_in_a_exp_fresh :
forall e1 T1 X1 X2,
  X1 `notin` ftv_in_a_exp e1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_exp (a_subst_tv_in_a_exp T1 X2 e1).
Proof.
pose proof a_subst_tv_in_a_body_fresh_a_subst_tv_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_fresh : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_fresh_a_subst_v_in_a_exp_fresh_mutual :
(forall a_body1 e1 x1 x2,
  x1 `notin` fv_in_a_body a_body1 ->
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_body (a_subst_v_in_a_body e1 x2 a_body1)) /\
(forall e2 e1 x1 x2,
  x1 `notin` fv_in_a_exp e2 ->
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_exp (a_subst_v_in_a_exp e1 x2 e2)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_fresh :
forall a_body1 e1 x1 x2,
  x1 `notin` fv_in_a_body a_body1 ->
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_body (a_subst_v_in_a_body e1 x2 a_body1).
Proof.
pose proof a_subst_v_in_a_body_fresh_a_subst_v_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_fresh : lngen.

Lemma a_subst_v_in_a_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_in_a_exp e2 ->
  x1 `notin` fv_in_a_exp e1 ->
  x1 `notin` fv_in_a_exp (a_subst_v_in_a_exp e1 x2 e2).
Proof.
pose proof a_subst_v_in_a_body_fresh_a_subst_v_in_a_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_fresh : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_fresh_mutual :
(forall b1 T1 X1 X2,
  X1 `notin` ftv_in_a_binding b1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_binding (a_subst_tv_in_a_binding T1 X2 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_fresh :
forall b1 T1 X1 X2,
  X1 `notin` ftv_in_a_binding b1 ->
  X1 `notin` ftv_in_a_typ T1 ->
  X1 `notin` ftv_in_a_binding (a_subst_tv_in_a_binding T1 X2 b1).
Proof.
pose proof a_subst_tv_in_a_binding_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_fresh : lngen.

Lemma a_subst_tv_in_a_typ_lc_a_typ :
forall T1 T2 X1,
  lc_a_typ T1 ->
  lc_a_typ T2 ->
  lc_a_typ (a_subst_tv_in_a_typ T2 X1 T1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_lc_a_typ : lngen.

Lemma a_subst_tv_in_a_body_lc_a_body :
forall a_body1 T1 X1,
  lc_a_body a_body1 ->
  lc_a_typ T1 ->
  lc_a_body (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_lc_a_body : lngen.

Lemma a_subst_tv_in_a_exp_lc_a_exp :
forall e1 T1 X1,
  lc_a_exp e1 ->
  lc_a_typ T1 ->
  lc_a_exp (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_lc_a_exp : lngen.

Lemma a_subst_v_in_a_body_lc_a_body :
forall a_body1 e1 x1,
  lc_a_body a_body1 ->
  lc_a_exp e1 ->
  lc_a_body (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_lc_a_body : lngen.

Lemma a_subst_v_in_a_exp_lc_a_exp :
forall e1 e2 x1,
  lc_a_exp e1 ->
  lc_a_exp e2 ->
  lc_a_exp (a_subst_v_in_a_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_lc_a_exp : lngen.

Lemma a_subst_tv_in_a_binding_lc_a_binding :
forall b1 T1 X1,
  lc_a_binding b1 ->
  lc_a_typ T1 ->
  lc_a_binding (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_lc_a_binding : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ_rec_mutual :
(forall T3 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ_rec n1 T2 T3) = open_a_typ_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_typ T1 X1 T3)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ_rec :
forall T3 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ_rec n1 T2 T3) = open_a_typ_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_typ T1 X1 T3).
Proof.
pose proof a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ_rec n1 T2 a_body1) = open_a_body_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ_rec n1 T2 e1) = open_a_exp_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_typ_rec :
forall a_body1 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ_rec n1 T2 a_body1) = open_a_body_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_open_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_rec :
forall e1 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ_rec n1 T2 e1) = open_a_exp_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_open_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 T1 e1 X1 n1,
  a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp_rec n1 e1 a_body1) = open_a_body_wrt_a_exp_rec n1 (a_subst_tv_in_a_exp T1 X1 e1) (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e2 T1 e1 X1 n1,
  a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp_rec n1 e1 e2) = open_a_exp_wrt_a_exp_rec n1 (a_subst_tv_in_a_exp T1 X1 e1) (a_subst_tv_in_a_exp T1 X1 e2)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_exp_rec :
forall a_body1 T1 e1 X1 n1,
  a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp_rec n1 e1 a_body1) = open_a_body_wrt_a_exp_rec n1 (a_subst_tv_in_a_exp T1 X1 e1) (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_open_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_rec :
forall e2 T1 e1 X1 n1,
  a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp_rec n1 e1 e2) = open_a_exp_wrt_a_exp_rec n1 (a_subst_tv_in_a_exp T1 X1 e1) (a_subst_tv_in_a_exp T1 X1 e2).
Proof.
pose proof a_subst_tv_in_a_body_open_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 e1 T1 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ_rec n1 T1 a_body1) = open_a_body_wrt_a_typ_rec n1 T1 (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e2 e1 T1 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ_rec n1 T1 e2) = open_a_exp_wrt_a_typ_rec n1 T1 (a_subst_v_in_a_exp e1 x1 e2)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_typ_rec :
forall a_body1 e1 T1 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ_rec n1 T1 a_body1) = open_a_body_wrt_a_typ_rec n1 T1 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_open_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_rec :
forall e2 e1 T1 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ_rec n1 T1 e2) = open_a_exp_wrt_a_typ_rec n1 T1 (a_subst_v_in_a_exp e1 x1 e2).
Proof.
pose proof a_subst_v_in_a_body_open_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 e1 e2 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp_rec n1 e2 a_body1) = open_a_body_wrt_a_exp_rec n1 (a_subst_v_in_a_exp e1 x1 e2) (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e3 e1 e2 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp_rec n1 e2 e3) = open_a_exp_wrt_a_exp_rec n1 (a_subst_v_in_a_exp e1 x1 e2) (a_subst_v_in_a_exp e1 x1 e3)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_exp_rec :
forall a_body1 e1 e2 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp_rec n1 e2 a_body1) = open_a_body_wrt_a_exp_rec n1 (a_subst_v_in_a_exp e1 x1 e2) (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_open_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp_rec n1 e2 e3) = open_a_exp_wrt_a_exp_rec n1 (a_subst_v_in_a_exp e1 x1 e2) (a_subst_v_in_a_exp e1 x1 e3).
Proof.
pose proof a_subst_v_in_a_body_open_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ_rec_mutual :
(forall b1 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ_rec n1 T2 b1) = open_a_binding_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ_rec :
forall b1 T1 T2 X1 n1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ_rec n1 T2 b1) = open_a_binding_wrt_a_typ_rec n1 (a_subst_tv_in_a_typ T1 X1 T2) (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ_rec : lngen.

(* end hide *)

Lemma a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ :
forall T3 T1 T2 X1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ T3 T2) = open_a_typ_wrt_a_typ (a_subst_tv_in_a_typ T1 X1 T3) (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_typ :
forall a_body1 T1 T2 X1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ a_body1 T2) = open_a_body_wrt_a_typ (a_subst_tv_in_a_body T1 X1 a_body1) (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_open_a_body_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ :
forall e1 T1 T2 X1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ e1 T2) = open_a_exp_wrt_a_typ (a_subst_tv_in_a_exp T1 X1 e1) (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_exp :
forall a_body1 T1 e1 X1,
  a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp a_body1 e1) = open_a_body_wrt_a_exp (a_subst_tv_in_a_body T1 X1 a_body1) (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_open_a_body_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp :
forall e2 T1 e1 X1,
  a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp e2 e1) = open_a_exp_wrt_a_exp (a_subst_tv_in_a_exp T1 X1 e2) (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_typ :
forall a_body1 e1 T1 x1,
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ a_body1 T1) = open_a_body_wrt_a_typ (a_subst_v_in_a_body e1 x1 a_body1) T1.
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_open_a_body_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_exp_open_a_exp_wrt_a_typ :
forall e2 e1 T1 x1,
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ e2 T1) = open_a_exp_wrt_a_typ (a_subst_v_in_a_exp e1 x1 e2) T1.
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_open_a_exp_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_exp :
forall a_body1 e1 e2 x1,
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp a_body1 e2) = open_a_body_wrt_a_exp (a_subst_v_in_a_body e1 x1 a_body1) (a_subst_v_in_a_exp e1 x1 e2).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_open_a_body_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_exp_open_a_exp_wrt_a_exp :
forall e3 e1 e2 x1,
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp e3 e2) = open_a_exp_wrt_a_exp (a_subst_v_in_a_exp e1 x1 e3) (a_subst_v_in_a_exp e1 x1 e2).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_open_a_exp_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ :
forall b1 T1 T2 X1,
  lc_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ b1 T2) = open_a_binding_wrt_a_typ (a_subst_tv_in_a_binding T1 X1 b1) (a_subst_tv_in_a_typ T1 X1 T2).
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ_var :
forall T2 T1 X1 X2,
  X1 <> X2 ->
  lc_a_typ T1 ->
  open_a_typ_wrt_a_typ (a_subst_tv_in_a_typ T1 X1 T2) (a_typ_tvar_f X2) = a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ T2 (a_typ_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_open_a_typ_wrt_a_typ_var : lngen.

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_typ_var :
forall a_body1 T1 X1 X2,
  X1 <> X2 ->
  lc_a_typ T1 ->
  open_a_body_wrt_a_typ (a_subst_tv_in_a_body T1 X1 a_body1) (a_typ_tvar_f X2) = a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_a_body_open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_open_a_body_wrt_a_typ_var : lngen.

Lemma a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_var :
forall e1 T1 X1 X2,
  X1 <> X2 ->
  lc_a_typ T1 ->
  open_a_exp_wrt_a_typ (a_subst_tv_in_a_exp T1 X1 e1) (a_typ_tvar_f X2) = a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_open_a_exp_wrt_a_typ_var : lngen.

Lemma a_subst_tv_in_a_body_open_a_body_wrt_a_exp_var :
forall a_body1 T1 X1 x1,
  open_a_body_wrt_a_exp (a_subst_tv_in_a_body T1 X1 a_body1) (a_exp_var_f x1) = a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1)).
Proof.
intros; rewrite a_subst_tv_in_a_body_open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_open_a_body_wrt_a_exp_var : lngen.

Lemma a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_var :
forall e1 T1 X1 x1,
  open_a_exp_wrt_a_exp (a_subst_tv_in_a_exp T1 X1 e1) (a_exp_var_f x1) = a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)).
Proof.
intros; rewrite a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_open_a_exp_wrt_a_exp_var : lngen.

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_typ_var :
forall a_body1 e1 x1 X1,
  lc_a_exp e1 ->
  open_a_body_wrt_a_typ (a_subst_v_in_a_body e1 x1 a_body1) (a_typ_tvar_f X1) = a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)).
Proof.
intros; rewrite a_subst_v_in_a_body_open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_open_a_body_wrt_a_typ_var : lngen.

Lemma a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_var :
forall e2 e1 x1 X1,
  lc_a_exp e1 ->
  open_a_exp_wrt_a_typ (a_subst_v_in_a_exp e1 x1 e2) (a_typ_tvar_f X1) = a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ e2 (a_typ_tvar_f X1)).
Proof.
intros; rewrite a_subst_v_in_a_exp_open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_open_a_exp_wrt_a_typ_var : lngen.

Lemma a_subst_v_in_a_body_open_a_body_wrt_a_exp_var :
forall a_body1 e1 x1 x2,
  x1 <> x2 ->
  lc_a_exp e1 ->
  open_a_body_wrt_a_exp (a_subst_v_in_a_body e1 x1 a_body1) (a_exp_var_f x2) = a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x2)).
Proof.
intros; rewrite a_subst_v_in_a_body_open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_open_a_body_wrt_a_exp_var : lngen.

Lemma a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_a_exp e1 ->
  open_a_exp_wrt_a_exp (a_subst_v_in_a_exp e1 x1 e2) (a_exp_var_f x2) = a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp e2 (a_exp_var_f x2)).
Proof.
intros; rewrite a_subst_v_in_a_exp_open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_open_a_exp_wrt_a_exp_var : lngen.

Lemma a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ_var :
forall b1 T1 X1 X2,
  X1 <> X2 ->
  lc_a_typ T1 ->
  open_a_binding_wrt_a_typ (a_subst_tv_in_a_binding T1 X1 b1) (a_typ_tvar_f X2) = a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_open_a_binding_wrt_a_typ_var : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_spec_rec_mutual :
(forall T1 T2 X1 n1,
  a_subst_tv_in_a_typ T2 X1 T1 = open_a_typ_wrt_a_typ_rec n1 T2 (close_a_typ_wrt_a_typ_rec n1 X1 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_typ_spec_rec :
forall T1 T2 X1 n1,
  a_subst_tv_in_a_typ T2 X1 T1 = open_a_typ_wrt_a_typ_rec n1 T2 (close_a_typ_wrt_a_typ_rec n1 X1 T1).
Proof.
pose proof a_subst_tv_in_a_typ_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_spec_rec_a_subst_tv_in_a_exp_spec_rec_mutual :
(forall a_body1 T1 X1 n1,
  a_subst_tv_in_a_body T1 X1 a_body1 = open_a_body_wrt_a_typ_rec n1 T1 (close_a_body_wrt_a_typ_rec n1 X1 a_body1)) /\
(forall e1 T1 X1 n1,
  a_subst_tv_in_a_exp T1 X1 e1 = open_a_exp_wrt_a_typ_rec n1 T1 (close_a_exp_wrt_a_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_spec_rec :
forall a_body1 T1 X1 n1,
  a_subst_tv_in_a_body T1 X1 a_body1 = open_a_body_wrt_a_typ_rec n1 T1 (close_a_body_wrt_a_typ_rec n1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_spec_rec_a_subst_tv_in_a_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_exp_spec_rec :
forall e1 T1 X1 n1,
  a_subst_tv_in_a_exp T1 X1 e1 = open_a_exp_wrt_a_typ_rec n1 T1 (close_a_exp_wrt_a_typ_rec n1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_spec_rec_a_subst_tv_in_a_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_spec_rec_a_subst_v_in_a_exp_spec_rec_mutual :
(forall a_body1 e1 x1 n1,
  a_subst_v_in_a_body e1 x1 a_body1 = open_a_body_wrt_a_exp_rec n1 e1 (close_a_body_wrt_a_exp_rec n1 x1 a_body1)) /\
(forall e1 e2 x1 n1,
  a_subst_v_in_a_exp e2 x1 e1 = open_a_exp_wrt_a_exp_rec n1 e2 (close_a_exp_wrt_a_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_spec_rec :
forall a_body1 e1 x1 n1,
  a_subst_v_in_a_body e1 x1 a_body1 = open_a_body_wrt_a_exp_rec n1 e1 (close_a_body_wrt_a_exp_rec n1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_spec_rec_a_subst_v_in_a_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_exp_spec_rec :
forall e1 e2 x1 n1,
  a_subst_v_in_a_exp e2 x1 e1 = open_a_exp_wrt_a_exp_rec n1 e2 (close_a_exp_wrt_a_exp_rec n1 x1 e1).
Proof.
pose proof a_subst_v_in_a_body_spec_rec_a_subst_v_in_a_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_binding_spec_rec_mutual :
(forall b1 T1 X1 n1,
  a_subst_tv_in_a_binding T1 X1 b1 = open_a_binding_wrt_a_typ_rec n1 T1 (close_a_binding_wrt_a_typ_rec n1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_binding_spec_rec :
forall b1 T1 X1 n1,
  a_subst_tv_in_a_binding T1 X1 b1 = open_a_binding_wrt_a_typ_rec n1 T1 (close_a_binding_wrt_a_typ_rec n1 X1 b1).
Proof.
pose proof a_subst_tv_in_a_binding_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_spec_rec : lngen.

(* end hide *)

Lemma a_subst_tv_in_a_typ_spec :
forall T1 T2 X1,
  a_subst_tv_in_a_typ T2 X1 T1 = open_a_typ_wrt_a_typ (close_a_typ_wrt_a_typ X1 T1) T2.
Proof.
unfold close_a_typ_wrt_a_typ; unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_spec : lngen.

Lemma a_subst_tv_in_a_body_spec :
forall a_body1 T1 X1,
  a_subst_tv_in_a_body T1 X1 a_body1 = open_a_body_wrt_a_typ (close_a_body_wrt_a_typ X1 a_body1) T1.
Proof.
unfold close_a_body_wrt_a_typ; unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_spec : lngen.

Lemma a_subst_tv_in_a_exp_spec :
forall e1 T1 X1,
  a_subst_tv_in_a_exp T1 X1 e1 = open_a_exp_wrt_a_typ (close_a_exp_wrt_a_typ X1 e1) T1.
Proof.
unfold close_a_exp_wrt_a_typ; unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_spec : lngen.

Lemma a_subst_v_in_a_body_spec :
forall a_body1 e1 x1,
  a_subst_v_in_a_body e1 x1 a_body1 = open_a_body_wrt_a_exp (close_a_body_wrt_a_exp x1 a_body1) e1.
Proof.
unfold close_a_body_wrt_a_exp; unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_spec : lngen.

Lemma a_subst_v_in_a_exp_spec :
forall e1 e2 x1,
  a_subst_v_in_a_exp e2 x1 e1 = open_a_exp_wrt_a_exp (close_a_exp_wrt_a_exp x1 e1) e2.
Proof.
unfold close_a_exp_wrt_a_exp; unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_spec : lngen.

Lemma a_subst_tv_in_a_binding_spec :
forall b1 T1 X1,
  a_subst_tv_in_a_binding T1 X1 b1 = open_a_binding_wrt_a_typ (close_a_binding_wrt_a_typ X1 b1) T1.
Proof.
unfold close_a_binding_wrt_a_typ; unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_spec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_a_subst_tv_in_a_typ_mutual :
(forall T1 T2 T3 X2 X1,
  X2 `notin` ftv_in_a_typ T2 ->
  X2 <> X1 ->
  a_subst_tv_in_a_typ T2 X1 (a_subst_tv_in_a_typ T3 X2 T1) = a_subst_tv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T3) X2 (a_subst_tv_in_a_typ T2 X1 T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_a_subst_tv_in_a_typ :
forall T1 T2 T3 X2 X1,
  X2 `notin` ftv_in_a_typ T2 ->
  X2 <> X1 ->
  a_subst_tv_in_a_typ T2 X1 (a_subst_tv_in_a_typ T3 X2 T1) = a_subst_tv_in_a_typ (a_subst_tv_in_a_typ T2 X1 T3) X2 (a_subst_tv_in_a_typ T2 X1 T1).
Proof.
pose proof a_subst_tv_in_a_typ_a_subst_tv_in_a_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_a_subst_tv_in_a_typ : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_a_subst_tv_in_a_body_a_subst_tv_in_a_exp_a_subst_tv_in_a_exp_mutual :
(forall a_body1 T1 T2 X2 X1,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  a_subst_tv_in_a_body T1 X1 (a_subst_tv_in_a_body T2 X2 a_body1) = a_subst_tv_in_a_body (a_subst_tv_in_a_typ T1 X1 T2) X2 (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 T2 X2 X1,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  a_subst_tv_in_a_exp T1 X1 (a_subst_tv_in_a_exp T2 X2 e1) = a_subst_tv_in_a_exp (a_subst_tv_in_a_typ T1 X1 T2) X2 (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_a_subst_tv_in_a_body :
forall a_body1 T1 T2 X2 X1,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  a_subst_tv_in_a_body T1 X1 (a_subst_tv_in_a_body T2 X2 a_body1) = a_subst_tv_in_a_body (a_subst_tv_in_a_typ T1 X1 T2) X2 (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_a_subst_tv_in_a_body_a_subst_tv_in_a_exp_a_subst_tv_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_a_subst_tv_in_a_body : lngen.

Lemma a_subst_tv_in_a_exp_a_subst_tv_in_a_exp :
forall e1 T1 T2 X2 X1,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  a_subst_tv_in_a_exp T1 X1 (a_subst_tv_in_a_exp T2 X2 e1) = a_subst_tv_in_a_exp (a_subst_tv_in_a_typ T1 X1 T2) X2 (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_a_subst_tv_in_a_body_a_subst_tv_in_a_exp_a_subst_tv_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_a_subst_tv_in_a_exp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_a_subst_v_in_a_body_a_subst_tv_in_a_exp_a_subst_v_in_a_exp_mutual :
(forall a_body1 T1 e1 x1 X1,
  a_subst_tv_in_a_body T1 X1 (a_subst_v_in_a_body e1 x1 a_body1) = a_subst_v_in_a_body (a_subst_tv_in_a_exp T1 X1 e1) x1 (a_subst_tv_in_a_body T1 X1 a_body1)) /\
(forall e1 T1 e2 x1 X1,
  a_subst_tv_in_a_exp T1 X1 (a_subst_v_in_a_exp e2 x1 e1) = a_subst_v_in_a_exp (a_subst_tv_in_a_exp T1 X1 e2) x1 (a_subst_tv_in_a_exp T1 X1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_a_subst_v_in_a_body :
forall a_body1 T1 e1 x1 X1,
  a_subst_tv_in_a_body T1 X1 (a_subst_v_in_a_body e1 x1 a_body1) = a_subst_v_in_a_body (a_subst_tv_in_a_exp T1 X1 e1) x1 (a_subst_tv_in_a_body T1 X1 a_body1).
Proof.
pose proof a_subst_tv_in_a_body_a_subst_v_in_a_body_a_subst_tv_in_a_exp_a_subst_v_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_a_subst_v_in_a_body : lngen.

Lemma a_subst_tv_in_a_exp_a_subst_v_in_a_exp :
forall e1 T1 e2 x1 X1,
  a_subst_tv_in_a_exp T1 X1 (a_subst_v_in_a_exp e2 x1 e1) = a_subst_v_in_a_exp (a_subst_tv_in_a_exp T1 X1 e2) x1 (a_subst_tv_in_a_exp T1 X1 e1).
Proof.
pose proof a_subst_tv_in_a_body_a_subst_v_in_a_body_a_subst_tv_in_a_exp_a_subst_v_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_a_subst_v_in_a_exp : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_a_subst_tv_in_a_body_a_subst_v_in_a_exp_a_subst_tv_in_a_exp_mutual :
(forall a_body1 e1 T1 X1 x1,
  X1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (a_subst_tv_in_a_body T1 X1 a_body1) = a_subst_tv_in_a_body T1 X1 (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 T1 X1 x1,
  X1 `notin` ftv_in_a_exp e2 ->
  a_subst_v_in_a_exp e2 x1 (a_subst_tv_in_a_exp T1 X1 e1) = a_subst_tv_in_a_exp T1 X1 (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_a_subst_tv_in_a_body :
forall a_body1 e1 T1 X1 x1,
  X1 `notin` ftv_in_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 (a_subst_tv_in_a_body T1 X1 a_body1) = a_subst_tv_in_a_body T1 X1 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_a_subst_tv_in_a_body_a_subst_v_in_a_exp_a_subst_tv_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_a_subst_tv_in_a_body : lngen.

Lemma a_subst_v_in_a_exp_a_subst_tv_in_a_exp :
forall e1 e2 T1 X1 x1,
  X1 `notin` ftv_in_a_exp e2 ->
  a_subst_v_in_a_exp e2 x1 (a_subst_tv_in_a_exp T1 X1 e1) = a_subst_tv_in_a_exp T1 X1 (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof a_subst_v_in_a_body_a_subst_tv_in_a_body_a_subst_v_in_a_exp_a_subst_tv_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_a_subst_tv_in_a_exp : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_a_subst_v_in_a_body_a_subst_v_in_a_exp_a_subst_v_in_a_exp_mutual :
(forall a_body1 e1 e2 x2 x1,
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  a_subst_v_in_a_body e1 x1 (a_subst_v_in_a_body e2 x2 a_body1) = a_subst_v_in_a_body (a_subst_v_in_a_exp e1 x1 e2) x2 (a_subst_v_in_a_body e1 x1 a_body1)) /\
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_in_a_exp e2 ->
  x2 <> x1 ->
  a_subst_v_in_a_exp e2 x1 (a_subst_v_in_a_exp e3 x2 e1) = a_subst_v_in_a_exp (a_subst_v_in_a_exp e2 x1 e3) x2 (a_subst_v_in_a_exp e2 x1 e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_a_subst_v_in_a_body :
forall a_body1 e1 e2 x2 x1,
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  a_subst_v_in_a_body e1 x1 (a_subst_v_in_a_body e2 x2 a_body1) = a_subst_v_in_a_body (a_subst_v_in_a_exp e1 x1 e2) x2 (a_subst_v_in_a_body e1 x1 a_body1).
Proof.
pose proof a_subst_v_in_a_body_a_subst_v_in_a_body_a_subst_v_in_a_exp_a_subst_v_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_a_subst_v_in_a_body : lngen.

Lemma a_subst_v_in_a_exp_a_subst_v_in_a_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_in_a_exp e2 ->
  x2 <> x1 ->
  a_subst_v_in_a_exp e2 x1 (a_subst_v_in_a_exp e3 x2 e1) = a_subst_v_in_a_exp (a_subst_v_in_a_exp e2 x1 e3) x2 (a_subst_v_in_a_exp e2 x1 e1).
Proof.
pose proof a_subst_v_in_a_body_a_subst_v_in_a_body_a_subst_v_in_a_exp_a_subst_v_in_a_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_a_subst_v_in_a_exp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_a_subst_tv_in_a_binding_mutual :
(forall b1 T1 T2 X2 X1,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  a_subst_tv_in_a_binding T1 X1 (a_subst_tv_in_a_binding T2 X2 b1) = a_subst_tv_in_a_binding (a_subst_tv_in_a_typ T1 X1 T2) X2 (a_subst_tv_in_a_binding T1 X1 b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_a_subst_tv_in_a_binding :
forall b1 T1 T2 X2 X1,
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  a_subst_tv_in_a_binding T1 X1 (a_subst_tv_in_a_binding T2 X2 b1) = a_subst_tv_in_a_binding (a_subst_tv_in_a_typ T1 X1 T2) X2 (a_subst_tv_in_a_binding T1 X1 b1).
Proof.
pose proof a_subst_tv_in_a_binding_a_subst_tv_in_a_binding_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_a_subst_tv_in_a_binding : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec_mutual :
(forall T2 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_typ T2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_typ T1 X1 T2 = close_a_typ_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X2) T2))).
Proof.
apply_mutual_ind a_typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec :
forall T2 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_typ T2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_typ T1 X1 T2 = close_a_typ_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X2) T2)).
Proof.
pose proof a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_rec_open_a_typ_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_body a_body1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = close_a_body_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X2) a_body1))) *
(forall e1 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_exp e1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = close_a_exp_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X2) e1))).
Proof.
apply_mutual_ind a_body_a_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec :
forall a_body1 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_body a_body1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = close_a_body_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X2) a_body1)).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec :
forall e1 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_exp e1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = close_a_exp_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X2) e1)).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 T1 X1 x1 n1,
  x1 `notin` fv_in_a_body a_body1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = close_a_body_wrt_a_exp_rec n1 x1 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1))) *
(forall e1 T1 X1 x1 n1,
  x1 `notin` fv_in_a_exp e1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = close_a_exp_wrt_a_exp_rec n1 x1 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1))).
Proof.
apply_mutual_ind a_body_a_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec :
forall a_body1 T1 X1 x1 n1,
  x1 `notin` fv_in_a_body a_body1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = close_a_body_wrt_a_exp_rec n1 x1 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1)).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec :
forall e1 T1 X1 x1 n1,
  x1 `notin` fv_in_a_exp e1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = close_a_exp_wrt_a_exp_rec n1 x1 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1)).
Proof.
pose proof a_subst_tv_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual :
(forall a_body1 e1 x1 X1 n1,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = close_a_body_wrt_a_typ_rec n1 X1 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1))) *
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp e1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  a_subst_v_in_a_exp e1 x1 e2 = close_a_exp_wrt_a_typ_rec n1 X1 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e2))).
Proof.
apply_mutual_ind a_body_a_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec :
forall a_body1 e1 x1 X1 n1,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = close_a_body_wrt_a_typ_rec n1 X1 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1)).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp e1 ->
  degree_a_exp_wrt_a_typ n1 e1 ->
  a_subst_v_in_a_exp e1 x1 e2 = close_a_exp_wrt_a_typ_rec n1 X1 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e2)).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_typ_rec_open_a_body_wrt_a_typ_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_rec_open_a_exp_wrt_a_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual :
(forall a_body1 e1 x1 x2 n1,
  x2 `notin` fv_in_a_body a_body1 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = close_a_body_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x2) a_body1))) *
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_in_a_exp e2 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  a_subst_v_in_a_exp e1 x1 e2 = close_a_exp_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x2) e2))).
Proof.
apply_mutual_ind a_body_a_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec :
forall a_body1 e1 x1 x2 n1,
  x2 `notin` fv_in_a_body a_body1 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = close_a_body_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x2) a_body1)).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_in_a_exp e2 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  degree_a_exp_wrt_a_exp n1 e1 ->
  a_subst_v_in_a_exp e1 x1 e2 = close_a_exp_wrt_a_exp_rec n1 x2 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x2) e2)).
Proof.
pose proof a_subst_v_in_a_body_close_a_body_wrt_a_exp_rec_open_a_body_wrt_a_exp_rec_a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_rec_open_a_exp_wrt_a_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec_mutual :
(forall b1 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_binding b1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_binding T1 X1 b1 = close_a_binding_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X2) b1))).
Proof.
apply_mutual_ind a_binding_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec :
forall b1 T1 X1 X2 n1,
  X2 `notin` ftv_in_a_binding b1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  degree_a_typ_wrt_a_typ n1 T1 ->
  a_subst_tv_in_a_binding T1 X1 b1 = close_a_binding_wrt_a_typ_rec n1 X2 (a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X2) b1)).
Proof.
pose proof a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_rec_open_a_binding_wrt_a_typ_rec : lngen.

(* end hide *)

Lemma a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ :
forall T2 T1 X1 X2,
  X2 `notin` ftv_in_a_typ T2 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  lc_a_typ T1 ->
  a_subst_tv_in_a_typ T1 X1 T2 = close_a_typ_wrt_a_typ X2 (a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ T2 (a_typ_tvar_f X2))).
Proof.
unfold close_a_typ_wrt_a_typ; unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_close_a_typ_wrt_a_typ_open_a_typ_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_typ_open_a_body_wrt_a_typ :
forall a_body1 T1 X1 X2,
  X2 `notin` ftv_in_a_body a_body1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  lc_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = close_a_body_wrt_a_typ X2 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X2))).
Proof.
unfold close_a_body_wrt_a_typ; unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_typ_open_a_body_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ :
forall e1 T1 X1 X2,
  X2 `notin` ftv_in_a_exp e1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  lc_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = close_a_exp_wrt_a_typ X2 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X2))).
Proof.
unfold close_a_exp_wrt_a_typ; unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_body_close_a_body_wrt_a_exp_open_a_body_wrt_a_exp :
forall a_body1 T1 X1 x1,
  x1 `notin` fv_in_a_body a_body1 ->
  lc_a_typ T1 ->
  a_subst_tv_in_a_body T1 X1 a_body1 = close_a_body_wrt_a_exp x1 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1))).
Proof.
unfold close_a_body_wrt_a_exp; unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_close_a_body_wrt_a_exp_open_a_body_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp :
forall e1 T1 X1 x1,
  x1 `notin` fv_in_a_exp e1 ->
  lc_a_typ T1 ->
  a_subst_tv_in_a_exp T1 X1 e1 = close_a_exp_wrt_a_exp x1 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1))).
Proof.
unfold close_a_exp_wrt_a_exp; unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_typ_open_a_body_wrt_a_typ :
forall a_body1 e1 x1 X1,
  X1 `notin` ftv_in_a_body a_body1 ->
  X1 `notin` ftv_in_a_exp e1 ->
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = close_a_body_wrt_a_typ X1 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1))).
Proof.
unfold close_a_body_wrt_a_typ; unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_typ_open_a_body_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ :
forall e2 e1 x1 X1,
  X1 `notin` ftv_in_a_exp e2 ->
  X1 `notin` ftv_in_a_exp e1 ->
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 e2 = close_a_exp_wrt_a_typ X1 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_typ e2 (a_typ_tvar_f X1))).
Proof.
unfold close_a_exp_wrt_a_typ; unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_typ_open_a_exp_wrt_a_typ : lngen.

Lemma a_subst_v_in_a_body_close_a_body_wrt_a_exp_open_a_body_wrt_a_exp :
forall a_body1 e1 x1 x2,
  x2 `notin` fv_in_a_body a_body1 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  lc_a_exp e1 ->
  a_subst_v_in_a_body e1 x1 a_body1 = close_a_body_wrt_a_exp x2 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x2))).
Proof.
unfold close_a_body_wrt_a_exp; unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_close_a_body_wrt_a_exp_open_a_body_wrt_a_exp : lngen.

Lemma a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp :
forall e2 e1 x1 x2,
  x2 `notin` fv_in_a_exp e2 ->
  x2 `notin` fv_in_a_exp e1 ->
  x2 <> x1 ->
  lc_a_exp e1 ->
  a_subst_v_in_a_exp e1 x1 e2 = close_a_exp_wrt_a_exp x2 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp e2 (a_exp_var_f x2))).
Proof.
unfold close_a_exp_wrt_a_exp; unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_close_a_exp_wrt_a_exp_open_a_exp_wrt_a_exp : lngen.

Lemma a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ :
forall b1 T1 X1 X2,
  X2 `notin` ftv_in_a_binding b1 ->
  X2 `notin` ftv_in_a_typ T1 ->
  X2 <> X1 ->
  lc_a_typ T1 ->
  a_subst_tv_in_a_binding T1 X1 b1 = close_a_binding_wrt_a_typ X2 (a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X2))).
Proof.
unfold close_a_binding_wrt_a_typ; unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_close_a_binding_wrt_a_typ_open_a_binding_wrt_a_typ : lngen.

Lemma a_subst_tv_in_a_typ_a_typ_all :
forall X2 T2 T1 X1,
  lc_a_typ T1 ->
  X2 `notin` ftv_in_a_typ T1 `union` ftv_in_a_typ T2 `union` singleton X1 ->
  a_subst_tv_in_a_typ T1 X1 (a_typ_all T2) = a_typ_all (close_a_typ_wrt_a_typ X2 (a_subst_tv_in_a_typ T1 X1 (open_a_typ_wrt_a_typ T2 (a_typ_tvar_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_a_typ_all : lngen.

Lemma a_subst_tv_in_a_exp_a_exp_abs :
forall x1 e1 T1 X1,
  lc_a_typ T1 ->
  x1 `notin` fv_in_a_exp e1 ->
  a_subst_tv_in_a_exp T1 X1 (a_exp_abs e1) = a_exp_abs (close_a_exp_wrt_a_exp x1 (a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_a_exp_abs : lngen.

Lemma a_subst_tv_in_a_exp_a_exp_tabs :
forall X2 a_body1 T1 X1,
  lc_a_typ T1 ->
  X2 `notin` ftv_in_a_typ T1 `union` ftv_in_a_body a_body1 `union` singleton X1 ->
  a_subst_tv_in_a_exp T1 X1 (a_exp_tabs a_body1) = a_exp_tabs (close_a_body_wrt_a_typ X2 (a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_a_exp_tabs : lngen.

Lemma a_subst_v_in_a_exp_a_exp_abs :
forall x2 e2 e1 x1,
  lc_a_exp e1 ->
  x2 `notin` fv_in_a_exp e1 `union` fv_in_a_exp e2 `union` singleton x1 ->
  a_subst_v_in_a_exp e1 x1 (a_exp_abs e2) = a_exp_abs (close_a_exp_wrt_a_exp x2 (a_subst_v_in_a_exp e1 x1 (open_a_exp_wrt_a_exp e2 (a_exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_a_exp_abs : lngen.

Lemma a_subst_v_in_a_exp_a_exp_tabs :
forall X1 a_body1 e1 x1,
  lc_a_exp e1 ->
  X1 `notin` ftv_in_a_exp e1 `union` ftv_in_a_body a_body1 ->
  a_subst_v_in_a_exp e1 x1 (a_exp_tabs a_body1) = a_exp_tabs (close_a_body_wrt_a_typ X1 (a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_a_exp_tabs : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_typ_intro_rec_mutual :
(forall T1 X1 T2 n1,
  X1 `notin` ftv_in_a_typ T1 ->
  open_a_typ_wrt_a_typ_rec n1 T2 T1 = a_subst_tv_in_a_typ T2 X1 (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1)).
Proof.
apply_mutual_ind a_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_typ_intro_rec :
forall T1 X1 T2 n1,
  X1 `notin` ftv_in_a_typ T1 ->
  open_a_typ_wrt_a_typ_rec n1 T2 T1 = a_subst_tv_in_a_typ T2 X1 (open_a_typ_wrt_a_typ_rec n1 (a_typ_tvar_f X1) T1).
Proof.
pose proof a_subst_tv_in_a_typ_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_body_intro_rec_a_subst_tv_in_a_exp_intro_rec_mutual :
(forall a_body1 X1 T1 n1,
  X1 `notin` ftv_in_a_body a_body1 ->
  open_a_body_wrt_a_typ_rec n1 T1 a_body1 = a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1)) /\
(forall e1 X1 T1 n1,
  X1 `notin` ftv_in_a_exp e1 ->
  open_a_exp_wrt_a_typ_rec n1 T1 e1 = a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_body_intro_rec :
forall a_body1 X1 T1 n1,
  X1 `notin` ftv_in_a_body a_body1 ->
  open_a_body_wrt_a_typ_rec n1 T1 a_body1 = a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ_rec n1 (a_typ_tvar_f X1) a_body1).
Proof.
pose proof a_subst_tv_in_a_body_intro_rec_a_subst_tv_in_a_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_body_intro_rec using solve [auto] : lngen.

Lemma a_subst_tv_in_a_exp_intro_rec :
forall e1 X1 T1 n1,
  X1 `notin` ftv_in_a_exp e1 ->
  open_a_exp_wrt_a_typ_rec n1 T1 e1 = a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ_rec n1 (a_typ_tvar_f X1) e1).
Proof.
pose proof a_subst_tv_in_a_body_intro_rec_a_subst_tv_in_a_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_v_in_a_body_intro_rec_a_subst_v_in_a_exp_intro_rec_mutual :
(forall a_body1 x1 e1 n1,
  x1 `notin` fv_in_a_body a_body1 ->
  open_a_body_wrt_a_exp_rec n1 e1 a_body1 = a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1)) /\
(forall e1 x1 e2 n1,
  x1 `notin` fv_in_a_exp e1 ->
  open_a_exp_wrt_a_exp_rec n1 e2 e1 = a_subst_v_in_a_exp e2 x1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1)).
Proof.
apply_mutual_ind a_body_a_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_a_body_intro_rec :
forall a_body1 x1 e1 n1,
  x1 `notin` fv_in_a_body a_body1 ->
  open_a_body_wrt_a_exp_rec n1 e1 a_body1 = a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp_rec n1 (a_exp_var_f x1) a_body1).
Proof.
pose proof a_subst_v_in_a_body_intro_rec_a_subst_v_in_a_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_intro_rec : lngen.
#[export] Hint Rewrite a_subst_v_in_a_body_intro_rec using solve [auto] : lngen.

Lemma a_subst_v_in_a_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_in_a_exp e1 ->
  open_a_exp_wrt_a_exp_rec n1 e2 e1 = a_subst_v_in_a_exp e2 x1 (open_a_exp_wrt_a_exp_rec n1 (a_exp_var_f x1) e1).
Proof.
pose proof a_subst_v_in_a_body_intro_rec_a_subst_v_in_a_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_intro_rec : lngen.
#[export] Hint Rewrite a_subst_v_in_a_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_a_binding_intro_rec_mutual :
(forall b1 X1 T1 n1,
  X1 `notin` ftv_in_a_binding b1 ->
  open_a_binding_wrt_a_typ_rec n1 T1 b1 = a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1)).
Proof.
apply_mutual_ind a_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_a_binding_intro_rec :
forall b1 X1 T1 n1,
  X1 `notin` ftv_in_a_binding b1 ->
  open_a_binding_wrt_a_typ_rec n1 T1 b1 = a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ_rec n1 (a_typ_tvar_f X1) b1).
Proof.
pose proof a_subst_tv_in_a_binding_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_a_binding_intro_rec using solve [auto] : lngen.

Lemma a_subst_tv_in_a_typ_intro :
forall X1 T1 T2,
  X1 `notin` ftv_in_a_typ T1 ->
  open_a_typ_wrt_a_typ T1 T2 = a_subst_tv_in_a_typ T2 X1 (open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X1)).
Proof.
unfold open_a_typ_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_typ_intro : lngen.

Lemma a_subst_tv_in_a_body_intro :
forall X1 a_body1 T1,
  X1 `notin` ftv_in_a_body a_body1 ->
  open_a_body_wrt_a_typ a_body1 T1 = a_subst_tv_in_a_body T1 X1 (open_a_body_wrt_a_typ a_body1 (a_typ_tvar_f X1)).
Proof.
unfold open_a_body_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_body_intro : lngen.

Lemma a_subst_tv_in_a_exp_intro :
forall X1 e1 T1,
  X1 `notin` ftv_in_a_exp e1 ->
  open_a_exp_wrt_a_typ e1 T1 = a_subst_tv_in_a_exp T1 X1 (open_a_exp_wrt_a_typ e1 (a_typ_tvar_f X1)).
Proof.
unfold open_a_exp_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_exp_intro : lngen.

Lemma a_subst_v_in_a_body_intro :
forall x1 a_body1 e1,
  x1 `notin` fv_in_a_body a_body1 ->
  open_a_body_wrt_a_exp a_body1 e1 = a_subst_v_in_a_body e1 x1 (open_a_body_wrt_a_exp a_body1 (a_exp_var_f x1)).
Proof.
unfold open_a_body_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_body_intro : lngen.

Lemma a_subst_v_in_a_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_in_a_exp e1 ->
  open_a_exp_wrt_a_exp e1 e2 = a_subst_v_in_a_exp e2 x1 (open_a_exp_wrt_a_exp e1 (a_exp_var_f x1)).
Proof.
unfold open_a_exp_wrt_a_exp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_a_exp_intro : lngen.

Lemma a_subst_tv_in_a_binding_intro :
forall X1 b1 T1,
  X1 `notin` ftv_in_a_binding b1 ->
  open_a_binding_wrt_a_typ b1 T1 = a_subst_tv_in_a_binding T1 X1 (open_a_binding_wrt_a_typ b1 (a_typ_tvar_f X1)).
Proof.
unfold open_a_binding_wrt_a_typ; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_a_binding_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
