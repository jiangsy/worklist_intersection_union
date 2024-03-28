Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export uni.def_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme abind_ind' := Induction for abind Sort Prop.

Combined Scheme abind_mutind from abind_ind'.

Scheme abind_rec' := Induction for abind Sort Set.

Combined Scheme abind_mutrec from abind_rec'.

Scheme body_ind' := Induction for body Sort Prop
  with exp_ind' := Induction for exp Sort Prop.

Combined Scheme body_exp_mutind from body_ind',exp_ind'.

Scheme body_rec' := Induction for body Sort Set
  with exp_rec' := Induction for exp Sort Set.

Combined Scheme body_exp_mutrec from body_rec',exp_rec'.

Scheme cont_ind' := Induction for cont Sort Prop
  with contd_ind' := Induction for contd Sort Prop.

Combined Scheme cont_contd_mutind from cont_ind',contd_ind'.

Scheme cont_rec' := Induction for cont Sort Set
  with contd_rec' := Induction for contd Sort Set.

Combined Scheme cont_contd_mutrec from cont_rec',contd_rec'.

Scheme dbind_ind' := Induction for dbind Sort Prop.

Combined Scheme dbind_mutind from dbind_ind'.

Scheme dbind_rec' := Induction for dbind Sort Set.

Combined Scheme dbind_mutrec from dbind_rec'.

Scheme work_ind' := Induction for work Sort Prop.

Combined Scheme work_mutind from work_ind'.

Scheme work_rec' := Induction for work Sort Set.

Combined Scheme work_mutrec from work_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | typ_unit => 1
    | typ_top => 1
    | typ_bot => 1
    | typ_var_f X1 => 1
    | typ_var_b n1 => 1
    | typ_arrow A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_all A2 => 1 + (size_typ A2)
    | typ_union A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_intersection A2 A3 => 1 + (size_typ A2) + (size_typ A3)
  end.

Fixpoint size_abind (ab1 : abind) {struct ab1} : nat :=
  match ab1 with
    | abind_tvar_empty => 1
    | abind_stvar_empty => 1
    | abind_etvar_empty => 1
    | abind_var_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_body (body1 : body) {struct body1} : nat :=
  match body1 with
    | body_anno e1 A1 => 1 + (size_exp e1) + (size_typ A1)
  end

with size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_unit => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_tabs body1 => 1 + (size_body body1)
    | exp_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  end.

Fixpoint size_cont (c1 : cont) {struct c1} : nat :=
  match c1 with
    | cont_infabs cc1 => 1 + (size_contd cc1)
    | cont_inftapp A1 c2 => 1 + (size_typ A1) + (size_cont c2)
    | cont_inftappunion A1 A2 c2 => 1 + (size_typ A1) + (size_typ A2) + (size_cont c2)
    | cont_unioninftapp A1 c2 => 1 + (size_typ A1) + (size_cont c2)
    | cont_sub A1 => 1 + (size_typ A1)
  end

with size_contd (cc1 : contd) {struct cc1} : nat :=
  match cc1 with
    | contd_infabsunion A1 B1 cc2 => 1 + (size_typ A1) + (size_typ B1) + (size_contd cc2)
    | contd_infapp e1 c1 => 1 + (size_exp e1) + (size_cont c1)
    | contd_unioninfabs A1 cc2 => 1 + (size_typ A1) + (size_contd cc2)
  end.

Fixpoint size_dbind (db1 : dbind) {struct db1} : nat :=
  match db1 with
    | dbind_tvar_empty => 1
    | dbind_stvar_empty => 1
    | dbind_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_work (w1 : work) {struct w1} : nat :=
  match w1 with
    | work_infer e1 c1 => 1 + (size_exp e1) + (size_cont c1)
    | work_check e1 A1 => 1 + (size_exp e1) + (size_typ A1)
    | work_infabs A1 cc1 => 1 + (size_typ A1) + (size_contd cc1)
    | work_infabsunion A1 B1 A2 cc1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ A2) + (size_contd cc1)
    | work_infapp A1 B1 e1 c1 => 1 + (size_typ A1) + (size_typ B1) + (size_exp e1) + (size_cont c1)
    | work_inftapp A1 A2 c1 => 1 + (size_typ A1) + (size_typ A2) + (size_cont c1)
    | work_sub A1 A2 => 1 + (size_typ A1) + (size_typ A2)
    | work_inftappunion A1 A2 B1 c1 => 1 + (size_typ A1) + (size_typ A2) + (size_typ B1) + (size_cont c1)
    | work_unioninftapp A1 A2 c1 => 1 + (size_typ A1) + (size_typ A2) + (size_cont c1)
    | work_unioninfabs A1 B1 A2 B2 cc1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ A2) + (size_typ B2) + (size_contd cc1)
    | work_apply c1 A1 => 1 + (size_cont c1) + (size_typ A1)
    | work_apply2 cc1 A1 B1 => 1 + (size_contd cc1) + (size_typ A1) + (size_typ B1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_unit : forall n1,
    degree_typ_wrt_typ n1 (typ_unit)
  | degree_wrt_typ_typ_top : forall n1,
    degree_typ_wrt_typ n1 (typ_top)
  | degree_wrt_typ_typ_bot : forall n1,
    degree_typ_wrt_typ n1 (typ_bot)
  | degree_wrt_typ_typ_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (typ_var_f X1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_arrow : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_arrow A1 A2)
  | degree_wrt_typ_typ_all : forall n1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (typ_all A1)
  | degree_wrt_typ_typ_union : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_union A1 A2)
  | degree_wrt_typ_typ_intersection : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_intersection A1 A2).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

#[export] Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_abind_wrt_typ : nat -> abind -> Prop :=
  | degree_wrt_typ_abind_tvar_empty : forall n1,
    degree_abind_wrt_typ n1 (abind_tvar_empty)
  | degree_wrt_typ_abind_stvar_empty : forall n1,
    degree_abind_wrt_typ n1 (abind_stvar_empty)
  | degree_wrt_typ_abind_etvar_empty : forall n1,
    degree_abind_wrt_typ n1 (abind_etvar_empty)
  | degree_wrt_typ_abind_var_typ : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_abind_wrt_typ n1 (abind_var_typ A1).

Scheme degree_abind_wrt_typ_ind' := Induction for degree_abind_wrt_typ Sort Prop.

Combined Scheme degree_abind_wrt_typ_mutind from degree_abind_wrt_typ_ind'.

#[export] Hint Constructors degree_abind_wrt_typ : core lngen.

Inductive degree_body_wrt_typ : nat -> body -> Prop :=
  | degree_wrt_typ_body_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_body_wrt_typ n1 (body_anno e1 A1)

with degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_exp_unit : forall n1,
    degree_exp_wrt_typ n1 (exp_unit)
  | degree_wrt_typ_exp_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (exp_var_f x1)
  | degree_wrt_typ_exp_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (exp_var_b n2)
  | degree_wrt_typ_exp_abs : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_abs e1)
  | degree_wrt_typ_exp_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_app e1 e2)
  | degree_wrt_typ_exp_tabs : forall n1 body1,
    degree_body_wrt_typ (S n1) body1 ->
    degree_exp_wrt_typ n1 (exp_tabs body1)
  | degree_wrt_typ_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_tapp e1 A1)
  | degree_wrt_typ_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_anno e1 A1).

Inductive degree_body_wrt_exp : nat -> body -> Prop :=
  | degree_wrt_exp_body_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_body_wrt_exp n1 (body_anno e1 A1)

with degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_unit : forall n1,
    degree_exp_wrt_exp n1 (exp_unit)
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_tabs : forall n1 body1,
    degree_body_wrt_exp n1 body1 ->
    degree_exp_wrt_exp n1 (exp_tabs body1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 A1)
  | degree_wrt_exp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_anno e1 A1).

Scheme degree_body_wrt_typ_ind' := Induction for degree_body_wrt_typ Sort Prop
  with degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_body_wrt_typ_degree_exp_wrt_typ_mutind from degree_body_wrt_typ_ind',degree_exp_wrt_typ_ind'.

Scheme degree_body_wrt_exp_ind' := Induction for degree_body_wrt_exp Sort Prop
  with degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_body_wrt_exp_degree_exp_wrt_exp_mutind from degree_body_wrt_exp_ind',degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_body_wrt_typ : core lngen.

#[export] Hint Constructors degree_exp_wrt_typ : core lngen.

#[export] Hint Constructors degree_body_wrt_exp : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.

Inductive degree_cont_wrt_typ : nat -> cont -> Prop :=
  | degree_wrt_typ_cont_infabs : forall n1 cc1,
    degree_contd_wrt_typ n1 cc1 ->
    degree_cont_wrt_typ n1 (cont_infabs cc1)
  | degree_wrt_typ_cont_inftapp : forall n1 A1 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_cont_wrt_typ n1 (cont_inftapp A1 c1)
  | degree_wrt_typ_cont_inftappunion : forall n1 A1 A2 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_cont_wrt_typ n1 (cont_inftappunion A1 A2 c1)
  | degree_wrt_typ_cont_unioninftapp : forall n1 A1 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_cont_wrt_typ n1 (cont_unioninftapp A1 c1)
  | degree_wrt_typ_cont_sub : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_cont_wrt_typ n1 (cont_sub A1)

with degree_contd_wrt_typ : nat -> contd -> Prop :=
  | degree_wrt_typ_contd_infabsunion : forall n1 A1 B1 cc1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_contd_wrt_typ n1 cc1 ->
    degree_contd_wrt_typ n1 (contd_infabsunion A1 B1 cc1)
  | degree_wrt_typ_contd_infapp : forall n1 e1 c1,
    degree_exp_wrt_typ n1 e1 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_contd_wrt_typ n1 (contd_infapp e1 c1)
  | degree_wrt_typ_contd_unioninfabs : forall n1 A1 cc1,
    degree_typ_wrt_typ n1 A1 ->
    degree_contd_wrt_typ n1 cc1 ->
    degree_contd_wrt_typ n1 (contd_unioninfabs A1 cc1).

Inductive degree_cont_wrt_exp : nat -> cont -> Prop :=
  | degree_wrt_exp_cont_infabs : forall n1 cc1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_cont_wrt_exp n1 (cont_infabs cc1)
  | degree_wrt_exp_cont_inftapp : forall n1 A1 c1,
    degree_cont_wrt_exp n1 c1 ->
    degree_cont_wrt_exp n1 (cont_inftapp A1 c1)
  | degree_wrt_exp_cont_inftappunion : forall n1 A1 A2 c1,
    degree_cont_wrt_exp n1 c1 ->
    degree_cont_wrt_exp n1 (cont_inftappunion A1 A2 c1)
  | degree_wrt_exp_cont_unioninftapp : forall n1 A1 c1,
    degree_cont_wrt_exp n1 c1 ->
    degree_cont_wrt_exp n1 (cont_unioninftapp A1 c1)
  | degree_wrt_exp_cont_sub : forall n1 A1,
    degree_cont_wrt_exp n1 (cont_sub A1)

with degree_contd_wrt_exp : nat -> contd -> Prop :=
  | degree_wrt_exp_contd_infabsunion : forall n1 A1 B1 cc1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_contd_wrt_exp n1 (contd_infabsunion A1 B1 cc1)
  | degree_wrt_exp_contd_infapp : forall n1 e1 c1,
    degree_exp_wrt_exp n1 e1 ->
    degree_cont_wrt_exp n1 c1 ->
    degree_contd_wrt_exp n1 (contd_infapp e1 c1)
  | degree_wrt_exp_contd_unioninfabs : forall n1 A1 cc1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_contd_wrt_exp n1 (contd_unioninfabs A1 cc1).

Scheme degree_cont_wrt_typ_ind' := Induction for degree_cont_wrt_typ Sort Prop
  with degree_contd_wrt_typ_ind' := Induction for degree_contd_wrt_typ Sort Prop.

Combined Scheme degree_cont_wrt_typ_degree_contd_wrt_typ_mutind from degree_cont_wrt_typ_ind',degree_contd_wrt_typ_ind'.

Scheme degree_cont_wrt_exp_ind' := Induction for degree_cont_wrt_exp Sort Prop
  with degree_contd_wrt_exp_ind' := Induction for degree_contd_wrt_exp Sort Prop.

Combined Scheme degree_cont_wrt_exp_degree_contd_wrt_exp_mutind from degree_cont_wrt_exp_ind',degree_contd_wrt_exp_ind'.

#[export] Hint Constructors degree_cont_wrt_typ : core lngen.

#[export] Hint Constructors degree_contd_wrt_typ : core lngen.

#[export] Hint Constructors degree_cont_wrt_exp : core lngen.

#[export] Hint Constructors degree_contd_wrt_exp : core lngen.

Inductive degree_dbind_wrt_typ : nat -> dbind -> Prop :=
  | degree_wrt_typ_dbind_tvar_empty : forall n1,
    degree_dbind_wrt_typ n1 (dbind_tvar_empty)
  | degree_wrt_typ_dbind_stvar_empty : forall n1,
    degree_dbind_wrt_typ n1 (dbind_stvar_empty)
  | degree_wrt_typ_dbind_typ : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_dbind_wrt_typ n1 (dbind_typ A1).

Scheme degree_dbind_wrt_typ_ind' := Induction for degree_dbind_wrt_typ Sort Prop.

Combined Scheme degree_dbind_wrt_typ_mutind from degree_dbind_wrt_typ_ind'.

#[export] Hint Constructors degree_dbind_wrt_typ : core lngen.

Inductive degree_work_wrt_typ : nat -> work -> Prop :=
  | degree_wrt_typ_work_infer : forall n1 e1 c1,
    degree_exp_wrt_typ n1 e1 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_work_wrt_typ n1 (work_infer e1 c1)
  | degree_wrt_typ_work_check : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_work_wrt_typ n1 (work_check e1 A1)
  | degree_wrt_typ_work_infabs : forall n1 A1 cc1,
    degree_typ_wrt_typ n1 A1 ->
    degree_contd_wrt_typ n1 cc1 ->
    degree_work_wrt_typ n1 (work_infabs A1 cc1)
  | degree_wrt_typ_work_infabsunion : forall n1 A1 B1 A2 cc1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_contd_wrt_typ n1 cc1 ->
    degree_work_wrt_typ n1 (work_infabsunion A1 B1 A2 cc1)
  | degree_wrt_typ_work_infapp : forall n1 A1 B1 e1 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_work_wrt_typ n1 (work_infapp A1 B1 e1 c1)
  | degree_wrt_typ_work_inftapp : forall n1 A1 A2 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_work_wrt_typ n1 (work_inftapp A1 A2 c1)
  | degree_wrt_typ_work_sub : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_work_wrt_typ n1 (work_sub A1 A2)
  | degree_wrt_typ_work_inftappunion : forall n1 A1 A2 B1 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_work_wrt_typ n1 (work_inftappunion A1 A2 B1 c1)
  | degree_wrt_typ_work_unioninftapp : forall n1 A1 A2 c1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_cont_wrt_typ n1 c1 ->
    degree_work_wrt_typ n1 (work_unioninftapp A1 A2 c1)
  | degree_wrt_typ_work_unioninfabs : forall n1 A1 B1 A2 B2 cc1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 B2 ->
    degree_contd_wrt_typ n1 cc1 ->
    degree_work_wrt_typ n1 (work_unioninfabs A1 B1 A2 B2 cc1)
  | degree_wrt_typ_work_apply : forall n1 c1 A1,
    degree_cont_wrt_typ n1 c1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_work_wrt_typ n1 (work_apply c1 A1)
  | degree_wrt_typ_work_apply2 : forall n1 cc1 A1 B1,
    degree_contd_wrt_typ n1 cc1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_work_wrt_typ n1 (work_apply2 cc1 A1 B1).

Inductive degree_work_wrt_exp : nat -> work -> Prop :=
  | degree_wrt_exp_work_infer : forall n1 e1 c1,
    degree_exp_wrt_exp n1 e1 ->
    degree_cont_wrt_exp n1 c1 ->
    degree_work_wrt_exp n1 (work_infer e1 c1)
  | degree_wrt_exp_work_check : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_work_wrt_exp n1 (work_check e1 A1)
  | degree_wrt_exp_work_infabs : forall n1 A1 cc1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_work_wrt_exp n1 (work_infabs A1 cc1)
  | degree_wrt_exp_work_infabsunion : forall n1 A1 B1 A2 cc1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_work_wrt_exp n1 (work_infabsunion A1 B1 A2 cc1)
  | degree_wrt_exp_work_infapp : forall n1 A1 B1 e1 c1,
    degree_exp_wrt_exp n1 e1 ->
    degree_cont_wrt_exp n1 c1 ->
    degree_work_wrt_exp n1 (work_infapp A1 B1 e1 c1)
  | degree_wrt_exp_work_inftapp : forall n1 A1 A2 c1,
    degree_cont_wrt_exp n1 c1 ->
    degree_work_wrt_exp n1 (work_inftapp A1 A2 c1)
  | degree_wrt_exp_work_sub : forall n1 A1 A2,
    degree_work_wrt_exp n1 (work_sub A1 A2)
  | degree_wrt_exp_work_inftappunion : forall n1 A1 A2 B1 c1,
    degree_cont_wrt_exp n1 c1 ->
    degree_work_wrt_exp n1 (work_inftappunion A1 A2 B1 c1)
  | degree_wrt_exp_work_unioninftapp : forall n1 A1 A2 c1,
    degree_cont_wrt_exp n1 c1 ->
    degree_work_wrt_exp n1 (work_unioninftapp A1 A2 c1)
  | degree_wrt_exp_work_unioninfabs : forall n1 A1 B1 A2 B2 cc1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_work_wrt_exp n1 (work_unioninfabs A1 B1 A2 B2 cc1)
  | degree_wrt_exp_work_apply : forall n1 c1 A1,
    degree_cont_wrt_exp n1 c1 ->
    degree_work_wrt_exp n1 (work_apply c1 A1)
  | degree_wrt_exp_work_apply2 : forall n1 cc1 A1 B1,
    degree_contd_wrt_exp n1 cc1 ->
    degree_work_wrt_exp n1 (work_apply2 cc1 A1 B1).

Scheme degree_work_wrt_typ_ind' := Induction for degree_work_wrt_typ Sort Prop.

Combined Scheme degree_work_wrt_typ_mutind from degree_work_wrt_typ_ind'.

Scheme degree_work_wrt_exp_ind' := Induction for degree_work_wrt_exp Sort Prop.

Combined Scheme degree_work_wrt_exp_mutind from degree_work_wrt_exp_ind'.

#[export] Hint Constructors degree_work_wrt_typ : core lngen.

#[export] Hint Constructors degree_work_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_unit :
    lc_set_typ (typ_unit)
  | lc_set_typ_top :
    lc_set_typ (typ_top)
  | lc_set_typ_bot :
    lc_set_typ (typ_bot)
  | lc_set_typ_var_f : forall X1,
    lc_set_typ (typ_var_f X1)
  | lc_set_typ_arrow : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_arrow A1 A2)
  | lc_set_typ_all : forall A1,
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ A1 (typ_var_f X1))) ->
    lc_set_typ (typ_all A1)
  | lc_set_typ_union : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_union A1 A2)
  | lc_set_typ_intersection : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_intersection A1 A2).

Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

#[export] Hint Constructors lc_typ : core lngen.

#[export] Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_abind : abind -> Set :=
  | lc_set_abind_tvar_empty :
    lc_set_abind (abind_tvar_empty)
  | lc_set_abind_stvar_empty :
    lc_set_abind (abind_stvar_empty)
  | lc_set_abind_etvar_empty :
    lc_set_abind (abind_etvar_empty)
  | lc_set_abind_var_typ : forall A1,
    lc_set_typ A1 ->
    lc_set_abind (abind_var_typ A1).

Scheme lc_abind_ind' := Induction for lc_abind Sort Prop.

Combined Scheme lc_abind_mutind from lc_abind_ind'.

Scheme lc_set_abind_ind' := Induction for lc_set_abind Sort Prop.

Combined Scheme lc_set_abind_mutind from lc_set_abind_ind'.

Scheme lc_set_abind_rec' := Induction for lc_set_abind Sort Set.

Combined Scheme lc_set_abind_mutrec from lc_set_abind_rec'.

#[export] Hint Constructors lc_abind : core lngen.

#[export] Hint Constructors lc_set_abind : core lngen.

Inductive lc_set_body : body -> Set :=
  | lc_set_body_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_body (body_anno e1 A1)

with lc_set_exp : exp -> Set :=
  | lc_set_exp_unit :
    lc_set_exp (exp_unit)
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_tabs : forall body1,
    (forall X1 : typvar, lc_set_body (open_body_wrt_typ body1 (typ_var_f X1))) ->
    lc_set_exp (exp_tabs body1)
  | lc_set_exp_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_tapp e1 A1)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_anno e1 A1).

Scheme lc_body_ind' := Induction for lc_body Sort Prop
  with lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_body_lc_exp_mutind from lc_body_ind',lc_exp_ind'.

Scheme lc_set_body_ind' := Induction for lc_set_body Sort Prop
  with lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_body_lc_set_exp_mutind from lc_set_body_ind',lc_set_exp_ind'.

Scheme lc_set_body_rec' := Induction for lc_set_body Sort Set
  with lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_body_lc_set_exp_mutrec from lc_set_body_rec',lc_set_exp_rec'.

#[export] Hint Constructors lc_body : core lngen.

#[export] Hint Constructors lc_exp : core lngen.

#[export] Hint Constructors lc_set_body : core lngen.

#[export] Hint Constructors lc_set_exp : core lngen.

Inductive lc_set_cont : cont -> Set :=
  | lc_set_cont_infabs : forall cc1,
    lc_set_contd cc1 ->
    lc_set_cont (cont_infabs cc1)
  | lc_set_cont_inftapp : forall A1 c1,
    lc_set_typ A1 ->
    lc_set_cont c1 ->
    lc_set_cont (cont_inftapp A1 c1)
  | lc_set_cont_inftappunion : forall A1 A2 c1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_cont c1 ->
    lc_set_cont (cont_inftappunion A1 A2 c1)
  | lc_set_cont_unioninftapp : forall A1 c1,
    lc_set_typ A1 ->
    lc_set_cont c1 ->
    lc_set_cont (cont_unioninftapp A1 c1)
  | lc_set_cont_sub : forall A1,
    lc_set_typ A1 ->
    lc_set_cont (cont_sub A1)

with lc_set_contd : contd -> Set :=
  | lc_set_contd_infabsunion : forall A1 B1 cc1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_contd cc1 ->
    lc_set_contd (contd_infabsunion A1 B1 cc1)
  | lc_set_contd_infapp : forall e1 c1,
    lc_set_exp e1 ->
    lc_set_cont c1 ->
    lc_set_contd (contd_infapp e1 c1)
  | lc_set_contd_unioninfabs : forall A1 cc1,
    lc_set_typ A1 ->
    lc_set_contd cc1 ->
    lc_set_contd (contd_unioninfabs A1 cc1).

Scheme lc_cont_ind' := Induction for lc_cont Sort Prop
  with lc_contd_ind' := Induction for lc_contd Sort Prop.

Combined Scheme lc_cont_lc_contd_mutind from lc_cont_ind',lc_contd_ind'.

Scheme lc_set_cont_ind' := Induction for lc_set_cont Sort Prop
  with lc_set_contd_ind' := Induction for lc_set_contd Sort Prop.

Combined Scheme lc_set_cont_lc_set_contd_mutind from lc_set_cont_ind',lc_set_contd_ind'.

Scheme lc_set_cont_rec' := Induction for lc_set_cont Sort Set
  with lc_set_contd_rec' := Induction for lc_set_contd Sort Set.

Combined Scheme lc_set_cont_lc_set_contd_mutrec from lc_set_cont_rec',lc_set_contd_rec'.

#[export] Hint Constructors lc_cont : core lngen.

#[export] Hint Constructors lc_contd : core lngen.

#[export] Hint Constructors lc_set_cont : core lngen.

#[export] Hint Constructors lc_set_contd : core lngen.

Inductive lc_set_dbind : dbind -> Set :=
  | lc_set_dbind_tvar_empty :
    lc_set_dbind (dbind_tvar_empty)
  | lc_set_dbind_stvar_empty :
    lc_set_dbind (dbind_stvar_empty)
  | lc_set_dbind_typ : forall A1,
    lc_set_typ A1 ->
    lc_set_dbind (dbind_typ A1).

Scheme lc_dbind_ind' := Induction for lc_dbind Sort Prop.

Combined Scheme lc_dbind_mutind from lc_dbind_ind'.

Scheme lc_set_dbind_ind' := Induction for lc_set_dbind Sort Prop.

Combined Scheme lc_set_dbind_mutind from lc_set_dbind_ind'.

Scheme lc_set_dbind_rec' := Induction for lc_set_dbind Sort Set.

Combined Scheme lc_set_dbind_mutrec from lc_set_dbind_rec'.

#[export] Hint Constructors lc_dbind : core lngen.

#[export] Hint Constructors lc_set_dbind : core lngen.

Inductive lc_set_work : work -> Set :=
  | lc_set_work_infer : forall e1 c1,
    lc_set_exp e1 ->
    lc_set_cont c1 ->
    lc_set_work (work_infer e1 c1)
  | lc_set_work_check : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_work (work_check e1 A1)
  | lc_set_work_infabs : forall A1 cc1,
    lc_set_typ A1 ->
    lc_set_contd cc1 ->
    lc_set_work (work_infabs A1 cc1)
  | lc_set_work_infabsunion : forall A1 B1 A2 cc1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ A2 ->
    lc_set_contd cc1 ->
    lc_set_work (work_infabsunion A1 B1 A2 cc1)
  | lc_set_work_infapp : forall A1 B1 e1 c1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_exp e1 ->
    lc_set_cont c1 ->
    lc_set_work (work_infapp A1 B1 e1 c1)
  | lc_set_work_inftapp : forall A1 A2 c1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_cont c1 ->
    lc_set_work (work_inftapp A1 A2 c1)
  | lc_set_work_sub : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_work (work_sub A1 A2)
  | lc_set_work_inftappunion : forall A1 A2 B1 c1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ B1 ->
    lc_set_cont c1 ->
    lc_set_work (work_inftappunion A1 A2 B1 c1)
  | lc_set_work_unioninftapp : forall A1 A2 c1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_cont c1 ->
    lc_set_work (work_unioninftapp A1 A2 c1)
  | lc_set_work_unioninfabs : forall A1 B1 A2 B2 cc1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ A2 ->
    lc_set_typ B2 ->
    lc_set_contd cc1 ->
    lc_set_work (work_unioninfabs A1 B1 A2 B2 cc1)
  | lc_set_work_apply : forall c1 A1,
    lc_set_cont c1 ->
    lc_set_typ A1 ->
    lc_set_work (work_apply c1 A1)
  | lc_set_work_apply2 : forall cc1 A1 B1,
    lc_set_contd cc1 ->
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_work (work_apply2 cc1 A1 B1).

Scheme lc_work_ind' := Induction for lc_work Sort Prop.

Combined Scheme lc_work_mutind from lc_work_ind'.

Scheme lc_set_work_ind' := Induction for lc_set_work Sort Prop.

Combined Scheme lc_set_work_mutind from lc_set_work_ind'.

Scheme lc_set_work_rec' := Induction for lc_set_work Sort Set.

Combined Scheme lc_set_work_mutrec from lc_set_work_rec'.

#[export] Hint Constructors lc_work : core lngen.

#[export] Hint Constructors lc_set_work : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)).

#[export] Hint Unfold body_typ_wrt_typ : core.

Definition body_abind_wrt_typ ab1 := forall X1, lc_abind (open_abind_wrt_typ ab1 (typ_var_f X1)).

#[export] Hint Unfold body_abind_wrt_typ : core.

Definition body_body_wrt_typ body1 := forall X1, lc_body (open_body_wrt_typ body1 (typ_var_f X1)).

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)).

Definition body_body_wrt_exp body1 := forall x1, lc_body (open_body_wrt_exp body1 (exp_var_f x1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

#[export] Hint Unfold body_body_wrt_typ : core.

#[export] Hint Unfold body_exp_wrt_typ : core.

#[export] Hint Unfold body_body_wrt_exp : core.

#[export] Hint Unfold body_exp_wrt_exp : core.

Definition body_cont_wrt_typ c1 := forall X1, lc_cont (open_cont_wrt_typ c1 (typ_var_f X1)).

Definition body_contd_wrt_typ cc1 := forall X1, lc_contd (open_contd_wrt_typ cc1 (typ_var_f X1)).

Definition body_cont_wrt_exp c1 := forall x1, lc_cont (open_cont_wrt_exp c1 (exp_var_f x1)).

Definition body_contd_wrt_exp cc1 := forall x1, lc_contd (open_contd_wrt_exp cc1 (exp_var_f x1)).

#[export] Hint Unfold body_cont_wrt_typ : core.

#[export] Hint Unfold body_contd_wrt_typ : core.

#[export] Hint Unfold body_cont_wrt_exp : core.

#[export] Hint Unfold body_contd_wrt_exp : core.

Definition body_dbind_wrt_typ db1 := forall X1, lc_dbind (open_dbind_wrt_typ db1 (typ_var_f X1)).

#[export] Hint Unfold body_dbind_wrt_typ : core.

Definition body_work_wrt_typ w1 := forall X1, lc_work (open_work_wrt_typ w1 (typ_var_f X1)).

Definition body_work_wrt_exp w1 := forall x1, lc_work (open_work_wrt_exp w1 (exp_var_f x1)).

#[export] Hint Unfold body_work_wrt_typ : core.

#[export] Hint Unfold body_work_wrt_exp : core.


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

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_abind_min_mutual :
(forall ab1, 1 <= size_abind ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_abind_min :
forall ab1, 1 <= size_abind ab1.
Proof.
pose proof size_abind_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_min : lngen.

(* begin hide *)

Lemma size_body_min_size_exp_min_mutual :
(forall body1, 1 <= size_body body1) /\
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_body_min :
forall body1, 1 <= size_body body1.
Proof.
pose proof size_body_min_size_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_min : lngen.

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_body_min_size_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_cont_min_size_contd_min_mutual :
(forall c1, 1 <= size_cont c1) /\
(forall cc1, 1 <= size_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_cont_min :
forall c1, 1 <= size_cont c1.
Proof.
pose proof size_cont_min_size_contd_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_min : lngen.

Lemma size_contd_min :
forall cc1, 1 <= size_contd cc1.
Proof.
pose proof size_cont_min_size_contd_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_min : lngen.

(* begin hide *)

Lemma size_dbind_min_mutual :
(forall db1, 1 <= size_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dbind_min :
forall db1, 1 <= size_dbind db1.
Proof.
pose proof size_dbind_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_min : lngen.

(* begin hide *)

Lemma size_work_min_mutual :
(forall w1, 1 <= size_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_work_min :
forall w1, 1 <= size_work w1.
Proof.
pose proof size_work_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abind_close_abind_wrt_typ_rec_mutual :
(forall ab1 X1 n1,
  size_abind (close_abind_wrt_typ_rec n1 X1 ab1) = size_abind ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abind_close_abind_wrt_typ_rec :
forall ab1 X1 n1,
  size_abind (close_abind_wrt_typ_rec n1 X1 ab1) = size_abind ab1.
Proof.
pose proof size_abind_close_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_close_abind_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_abind_close_abind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_close_body_wrt_typ_rec_size_exp_close_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1,
  size_body (close_body_wrt_typ_rec n1 X1 body1) = size_body body1) /\
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_body_close_body_wrt_typ_rec :
forall body1 X1 n1,
  size_body (close_body_wrt_typ_rec n1 X1 body1) = size_body body1.
Proof.
pose proof size_body_close_body_wrt_typ_rec_size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_close_body_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_body_close_body_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_body_close_body_wrt_typ_rec_size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_close_body_wrt_exp_rec_size_exp_close_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1,
  size_body (close_body_wrt_exp_rec n1 x1 body1) = size_body body1) /\
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_body_close_body_wrt_exp_rec :
forall body1 x1 n1,
  size_body (close_body_wrt_exp_rec n1 x1 body1) = size_body body1.
Proof.
pose proof size_body_close_body_wrt_exp_rec_size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_close_body_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_body_close_body_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_body_close_body_wrt_exp_rec_size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_cont_close_cont_wrt_typ_rec_size_contd_close_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  size_cont (close_cont_wrt_typ_rec n1 X1 c1) = size_cont c1) /\
(forall cc1 X1 n1,
  size_contd (close_contd_wrt_typ_rec n1 X1 cc1) = size_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_cont_close_cont_wrt_typ_rec :
forall c1 X1 n1,
  size_cont (close_cont_wrt_typ_rec n1 X1 c1) = size_cont c1.
Proof.
pose proof size_cont_close_cont_wrt_typ_rec_size_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_close_cont_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_cont_close_cont_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_close_contd_wrt_typ_rec :
forall cc1 X1 n1,
  size_contd (close_contd_wrt_typ_rec n1 X1 cc1) = size_contd cc1.
Proof.
pose proof size_cont_close_cont_wrt_typ_rec_size_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_cont_close_cont_wrt_exp_rec_size_contd_close_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1,
  size_cont (close_cont_wrt_exp_rec n1 x1 c1) = size_cont c1) /\
(forall cc1 x1 n1,
  size_contd (close_contd_wrt_exp_rec n1 x1 cc1) = size_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_cont_close_cont_wrt_exp_rec :
forall c1 x1 n1,
  size_cont (close_cont_wrt_exp_rec n1 x1 c1) = size_cont c1.
Proof.
pose proof size_cont_close_cont_wrt_exp_rec_size_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_close_cont_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_cont_close_cont_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_close_contd_wrt_exp_rec :
forall cc1 x1 n1,
  size_contd (close_contd_wrt_exp_rec n1 x1 cc1) = size_contd cc1.
Proof.
pose proof size_cont_close_cont_wrt_exp_rec_size_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  size_dbind (close_dbind_wrt_typ_rec n1 X1 db1) = size_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbind_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  size_dbind (close_dbind_wrt_typ_rec n1 X1 db1) = size_dbind db1.
Proof.
pose proof size_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_close_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_dbind_close_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_close_work_wrt_typ_rec_mutual :
(forall w1 X1 n1,
  size_work (close_work_wrt_typ_rec n1 X1 w1) = size_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_close_work_wrt_typ_rec :
forall w1 X1 n1,
  size_work (close_work_wrt_typ_rec n1 X1 w1) = size_work w1.
Proof.
pose proof size_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_close_work_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_work_close_work_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_close_work_wrt_exp_rec_mutual :
(forall w1 x1 n1,
  size_work (close_work_wrt_exp_rec n1 x1 w1) = size_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_close_work_wrt_exp_rec :
forall w1 x1 n1,
  size_work (close_work_wrt_exp_rec n1 x1 w1) = size_work w1.
Proof.
pose proof size_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_close_work_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_work_close_work_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_abind_close_abind_wrt_typ :
forall ab1 X1,
  size_abind (close_abind_wrt_typ X1 ab1) = size_abind ab1.
Proof.
unfold close_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_abind_close_abind_wrt_typ : lngen.
#[export] Hint Rewrite size_abind_close_abind_wrt_typ using solve [auto] : lngen.

Lemma size_body_close_body_wrt_typ :
forall body1 X1,
  size_body (close_body_wrt_typ X1 body1) = size_body body1.
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_body_close_body_wrt_typ : lngen.
#[export] Hint Rewrite size_body_close_body_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_body_close_body_wrt_exp :
forall body1 x1,
  size_body (close_body_wrt_exp x1 body1) = size_body body1.
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_body_close_body_wrt_exp : lngen.
#[export] Hint Rewrite size_body_close_body_wrt_exp using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma size_cont_close_cont_wrt_typ :
forall c1 X1,
  size_cont (close_cont_wrt_typ X1 c1) = size_cont c1.
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_cont_close_cont_wrt_typ : lngen.
#[export] Hint Rewrite size_cont_close_cont_wrt_typ using solve [auto] : lngen.

Lemma size_contd_close_contd_wrt_typ :
forall cc1 X1,
  size_contd (close_contd_wrt_typ X1 cc1) = size_contd cc1.
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_typ using solve [auto] : lngen.

Lemma size_cont_close_cont_wrt_exp :
forall c1 x1,
  size_cont (close_cont_wrt_exp x1 c1) = size_cont c1.
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_cont_close_cont_wrt_exp : lngen.
#[export] Hint Rewrite size_cont_close_cont_wrt_exp using solve [auto] : lngen.

Lemma size_contd_close_contd_wrt_exp :
forall cc1 x1,
  size_contd (close_contd_wrt_exp x1 cc1) = size_contd cc1.
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_exp using solve [auto] : lngen.

Lemma size_dbind_close_dbind_wrt_typ :
forall db1 X1,
  size_dbind (close_dbind_wrt_typ X1 db1) = size_dbind db1.
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_dbind_close_dbind_wrt_typ : lngen.
#[export] Hint Rewrite size_dbind_close_dbind_wrt_typ using solve [auto] : lngen.

Lemma size_work_close_work_wrt_typ :
forall w1 X1,
  size_work (close_work_wrt_typ X1 w1) = size_work w1.
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_work_close_work_wrt_typ : lngen.
#[export] Hint Rewrite size_work_close_work_wrt_typ using solve [auto] : lngen.

Lemma size_work_close_work_wrt_exp :
forall w1 x1,
  size_work (close_work_wrt_exp x1 w1) = size_work w1.
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_work_close_work_wrt_exp : lngen.
#[export] Hint Rewrite size_work_close_work_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_typ_rec_mutual :
(forall ab1 A1 n1,
  size_abind ab1 <= size_abind (open_abind_wrt_typ_rec n1 A1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_typ_rec :
forall ab1 A1 n1,
  size_abind ab1 <= size_abind (open_abind_wrt_typ_rec n1 A1 ab1).
Proof.
pose proof size_abind_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_typ_rec_size_exp_open_exp_wrt_typ_rec_mutual :
(forall body1 A1 n1,
  size_body body1 <= size_body (open_body_wrt_typ_rec n1 A1 body1)) /\
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_typ_rec :
forall body1 A1 n1,
  size_body body1 <= size_body (open_body_wrt_typ_rec n1 A1 body1).
Proof.
pose proof size_body_open_body_wrt_typ_rec_size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof size_body_open_body_wrt_typ_rec_size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_exp_rec_size_exp_open_exp_wrt_exp_rec_mutual :
(forall body1 e1 n1,
  size_body body1 <= size_body (open_body_wrt_exp_rec n1 e1 body1)) /\
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_exp_rec :
forall body1 e1 n1,
  size_body body1 <= size_body (open_body_wrt_exp_rec n1 e1 body1).
Proof.
pose proof size_body_open_body_wrt_exp_rec_size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_body_open_body_wrt_exp_rec_size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_typ_rec_size_contd_open_contd_wrt_typ_rec_mutual :
(forall c1 A1 n1,
  size_cont c1 <= size_cont (open_cont_wrt_typ_rec n1 A1 c1)) /\
(forall cc1 A1 n1,
  size_contd cc1 <= size_contd (open_contd_wrt_typ_rec n1 A1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_typ_rec :
forall c1 A1 n1,
  size_cont c1 <= size_cont (open_cont_wrt_typ_rec n1 A1 c1).
Proof.
pose proof size_cont_open_cont_wrt_typ_rec_size_contd_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_typ_rec :
forall cc1 A1 n1,
  size_contd cc1 <= size_contd (open_contd_wrt_typ_rec n1 A1 cc1).
Proof.
pose proof size_cont_open_cont_wrt_typ_rec_size_contd_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_exp_rec_size_contd_open_contd_wrt_exp_rec_mutual :
(forall c1 e1 n1,
  size_cont c1 <= size_cont (open_cont_wrt_exp_rec n1 e1 c1)) /\
(forall cc1 e1 n1,
  size_contd cc1 <= size_contd (open_contd_wrt_exp_rec n1 e1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_exp_rec :
forall c1 e1 n1,
  size_cont c1 <= size_cont (open_cont_wrt_exp_rec n1 e1 c1).
Proof.
pose proof size_cont_open_cont_wrt_exp_rec_size_contd_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_exp_rec :
forall cc1 e1 n1,
  size_contd cc1 <= size_contd (open_contd_wrt_exp_rec n1 e1 cc1).
Proof.
pose proof size_cont_open_cont_wrt_exp_rec_size_contd_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 n1,
  size_dbind db1 <= size_dbind (open_dbind_wrt_typ_rec n1 A1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec :
forall db1 A1 n1,
  size_dbind db1 <= size_dbind (open_dbind_wrt_typ_rec n1 A1 db1).
Proof.
pose proof size_dbind_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_typ_rec_mutual :
(forall w1 A1 n1,
  size_work w1 <= size_work (open_work_wrt_typ_rec n1 A1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; auto 6 with arith lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_typ_rec :
forall w1 A1 n1,
  size_work w1 <= size_work (open_work_wrt_typ_rec n1 A1 w1).
Proof.
pose proof size_work_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_exp_rec_mutual :
(forall w1 e1 n1,
  size_work w1 <= size_work (open_work_wrt_exp_rec n1 e1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_exp_rec :
forall w1 e1 n1,
  size_work w1 <= size_work (open_work_wrt_exp_rec n1 e1 w1).
Proof.
pose proof size_work_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_abind_open_abind_wrt_typ :
forall ab1 A1,
  size_abind ab1 <= size_abind (open_abind_wrt_typ ab1 A1).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_typ : lngen.

Lemma size_body_open_body_wrt_typ :
forall body1 A1,
  size_body body1 <= size_body (open_body_wrt_typ body1 A1).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_typ :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_body_open_body_wrt_exp :
forall body1 e1,
  size_body body1 <= size_body (open_body_wrt_exp body1 e1).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_exp : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

Lemma size_cont_open_cont_wrt_typ :
forall c1 A1,
  size_cont c1 <= size_cont (open_cont_wrt_typ c1 A1).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_typ : lngen.

Lemma size_contd_open_contd_wrt_typ :
forall cc1 A1,
  size_contd cc1 <= size_contd (open_contd_wrt_typ cc1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ : lngen.

Lemma size_cont_open_cont_wrt_exp :
forall c1 e1,
  size_cont c1 <= size_cont (open_cont_wrt_exp c1 e1).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_exp : lngen.

Lemma size_contd_open_contd_wrt_exp :
forall cc1 e1,
  size_contd cc1 <= size_contd (open_contd_wrt_exp cc1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp : lngen.

Lemma size_dbind_open_dbind_wrt_typ :
forall db1 A1,
  size_dbind db1 <= size_dbind (open_dbind_wrt_typ db1 A1).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ : lngen.

Lemma size_work_open_work_wrt_typ :
forall w1 A1,
  size_work w1 <= size_work (open_work_wrt_typ w1 A1).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_typ : lngen.

Lemma size_work_open_work_wrt_exp :
forall w1 e1,
  size_work w1 <= size_work (open_work_wrt_exp w1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_exp : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_typ_rec_var_mutual :
(forall ab1 X1 n1,
  size_abind (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1) = size_abind ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_typ_rec_var :
forall ab1 X1 n1,
  size_abind (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1) = size_abind ab1.
Proof.
pose proof size_abind_open_abind_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_abind_open_abind_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_typ_rec_var_size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall body1 X1 n1,
  size_body (open_body_wrt_typ_rec n1 (typ_var_f X1) body1) = size_body body1) /\
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_typ_rec_var :
forall body1 X1 n1,
  size_body (open_body_wrt_typ_rec n1 (typ_var_f X1) body1) = size_body body1.
Proof.
pose proof size_body_open_body_wrt_typ_rec_var_size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_body_open_body_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_body_open_body_wrt_typ_rec_var_size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_exp_rec_var_size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall body1 x1 n1,
  size_body (open_body_wrt_exp_rec n1 (exp_var_f x1) body1) = size_body body1) /\
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_body_open_body_wrt_exp_rec_var :
forall body1 x1 n1,
  size_body (open_body_wrt_exp_rec n1 (exp_var_f x1) body1) = size_body body1.
Proof.
pose proof size_body_open_body_wrt_exp_rec_var_size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_body_open_body_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_body_open_body_wrt_exp_rec_var_size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_typ_rec_var_size_contd_open_contd_wrt_typ_rec_var_mutual :
(forall c1 X1 n1,
  size_cont (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1) = size_cont c1) /\
(forall cc1 X1 n1,
  size_contd (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1) = size_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_typ_rec_var :
forall c1 X1 n1,
  size_cont (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1) = size_cont c1.
Proof.
pose proof size_cont_open_cont_wrt_typ_rec_var_size_contd_open_contd_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_cont_open_cont_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_typ_rec_var :
forall cc1 X1 n1,
  size_contd (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1) = size_contd cc1.
Proof.
pose proof size_cont_open_cont_wrt_typ_rec_var_size_contd_open_contd_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_exp_rec_var_size_contd_open_contd_wrt_exp_rec_var_mutual :
(forall c1 x1 n1,
  size_cont (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1) = size_cont c1) /\
(forall cc1 x1 n1,
  size_contd (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1) = size_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_cont_open_cont_wrt_exp_rec_var :
forall c1 x1 n1,
  size_cont (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1) = size_cont c1.
Proof.
pose proof size_cont_open_cont_wrt_exp_rec_var_size_contd_open_contd_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_cont_open_cont_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_exp_rec_var :
forall cc1 x1 n1,
  size_contd (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1) = size_contd cc1.
Proof.
pose proof size_cont_open_cont_wrt_exp_rec_var_size_contd_open_contd_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec_var_mutual :
(forall db1 X1 n1,
  size_dbind (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = size_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec_var :
forall db1 X1 n1,
  size_dbind (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = size_dbind db1.
Proof.
pose proof size_dbind_open_dbind_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_dbind_open_dbind_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_typ_rec_var_mutual :
(forall w1 X1 n1,
  size_work (open_work_wrt_typ_rec n1 (typ_var_f X1) w1) = size_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_typ_rec_var :
forall w1 X1 n1,
  size_work (open_work_wrt_typ_rec n1 (typ_var_f X1) w1) = size_work w1.
Proof.
pose proof size_work_open_work_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_work_open_work_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_exp_rec_var_mutual :
(forall w1 x1 n1,
  size_work (open_work_wrt_exp_rec n1 (exp_var_f x1) w1) = size_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_work_open_work_wrt_exp_rec_var :
forall w1 x1 n1,
  size_work (open_work_wrt_exp_rec n1 (exp_var_f x1) w1) = size_work w1.
Proof.
pose proof size_work_open_work_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_work_open_work_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (typ_var_f X1)) = size_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_abind_open_abind_wrt_typ_var :
forall ab1 X1,
  size_abind (open_abind_wrt_typ ab1 (typ_var_f X1)) = size_abind ab1.
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_typ_var : lngen.
#[export] Hint Rewrite size_abind_open_abind_wrt_typ_var using solve [auto] : lngen.

Lemma size_body_open_body_wrt_typ_var :
forall body1 X1,
  size_body (open_body_wrt_typ body1 (typ_var_f X1)) = size_body body1.
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_typ_var : lngen.
#[export] Hint Rewrite size_body_open_body_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (typ_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_body_open_body_wrt_exp_var :
forall body1 x1,
  size_body (open_body_wrt_exp body1 (exp_var_f x1)) = size_body body1.
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_body_open_body_wrt_exp_var : lngen.
#[export] Hint Rewrite size_body_open_body_wrt_exp_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

Lemma size_cont_open_cont_wrt_typ_var :
forall c1 X1,
  size_cont (open_cont_wrt_typ c1 (typ_var_f X1)) = size_cont c1.
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_typ_var : lngen.
#[export] Hint Rewrite size_cont_open_cont_wrt_typ_var using solve [auto] : lngen.

Lemma size_contd_open_contd_wrt_typ_var :
forall cc1 X1,
  size_contd (open_contd_wrt_typ cc1 (typ_var_f X1)) = size_contd cc1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_typ_var using solve [auto] : lngen.

Lemma size_cont_open_cont_wrt_exp_var :
forall c1 x1,
  size_cont (open_cont_wrt_exp c1 (exp_var_f x1)) = size_cont c1.
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_cont_open_cont_wrt_exp_var : lngen.
#[export] Hint Rewrite size_cont_open_cont_wrt_exp_var using solve [auto] : lngen.

Lemma size_contd_open_contd_wrt_exp_var :
forall cc1 x1,
  size_contd (open_contd_wrt_exp cc1 (exp_var_f x1)) = size_contd cc1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_exp_var using solve [auto] : lngen.

Lemma size_dbind_open_dbind_wrt_typ_var :
forall db1 X1,
  size_dbind (open_dbind_wrt_typ db1 (typ_var_f X1)) = size_dbind db1.
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ_var : lngen.
#[export] Hint Rewrite size_dbind_open_dbind_wrt_typ_var using solve [auto] : lngen.

Lemma size_work_open_work_wrt_typ_var :
forall w1 X1,
  size_work (open_work_wrt_typ w1 (typ_var_f X1)) = size_work w1.
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_typ_var : lngen.
#[export] Hint Rewrite size_work_open_work_wrt_typ_var using solve [auto] : lngen.

Lemma size_work_open_work_wrt_exp_var :
forall w1 x1,
  size_work (open_work_wrt_exp w1 (exp_var_f x1)) = size_work w1.
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_work_open_work_wrt_exp_var : lngen.
#[export] Hint Rewrite size_work_open_work_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_abind_wrt_typ_S_mutual :
(forall n1 ab1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_abind_wrt_typ (S n1) ab1).
Proof.
apply_mutual_ind degree_abind_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_abind_wrt_typ_S :
forall n1 ab1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_abind_wrt_typ (S n1) ab1.
Proof.
pose proof degree_abind_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_body_wrt_typ_S_degree_exp_wrt_typ_S_mutual :
(forall n1 body1,
  degree_body_wrt_typ n1 body1 ->
  degree_body_wrt_typ (S n1) body1) /\
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_body_wrt_typ_degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_body_wrt_typ_S :
forall n1 body1,
  degree_body_wrt_typ n1 body1 ->
  degree_body_wrt_typ (S n1) body1.
Proof.
pose proof degree_body_wrt_typ_S_degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_S : lngen.

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_body_wrt_typ_S_degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_body_wrt_exp_S_degree_exp_wrt_exp_S_mutual :
(forall n1 body1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp (S n1) body1) /\
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_body_wrt_exp_degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_body_wrt_exp_S :
forall n1 body1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp (S n1) body1.
Proof.
pose proof degree_body_wrt_exp_S_degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_S : lngen.

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_body_wrt_exp_S_degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_S : lngen.

(* begin hide *)

Lemma degree_cont_wrt_typ_S_degree_contd_wrt_typ_S_mutual :
(forall n1 c1,
  degree_cont_wrt_typ n1 c1 ->
  degree_cont_wrt_typ (S n1) c1) /\
(forall n1 cc1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_contd_wrt_typ (S n1) cc1).
Proof.
apply_mutual_ind degree_cont_wrt_typ_degree_contd_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_cont_wrt_typ_S :
forall n1 c1,
  degree_cont_wrt_typ n1 c1 ->
  degree_cont_wrt_typ (S n1) c1.
Proof.
pose proof degree_cont_wrt_typ_S_degree_contd_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_S : lngen.

Lemma degree_contd_wrt_typ_S :
forall n1 cc1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_contd_wrt_typ (S n1) cc1.
Proof.
pose proof degree_cont_wrt_typ_S_degree_contd_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_cont_wrt_exp_S_degree_contd_wrt_exp_S_mutual :
(forall n1 c1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp (S n1) c1) /\
(forall n1 cc1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp (S n1) cc1).
Proof.
apply_mutual_ind degree_cont_wrt_exp_degree_contd_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_cont_wrt_exp_S :
forall n1 c1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp (S n1) c1.
Proof.
pose proof degree_cont_wrt_exp_S_degree_contd_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_S : lngen.

Lemma degree_contd_wrt_exp_S :
forall n1 cc1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp (S n1) cc1.
Proof.
pose proof degree_cont_wrt_exp_S_degree_contd_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_S : lngen.

(* begin hide *)

Lemma degree_dbind_wrt_typ_S_mutual :
(forall n1 db1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) db1).
Proof.
apply_mutual_ind degree_dbind_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dbind_wrt_typ_S :
forall n1 db1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) db1.
Proof.
pose proof degree_dbind_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_work_wrt_typ_S_mutual :
(forall n1 w1,
  degree_work_wrt_typ n1 w1 ->
  degree_work_wrt_typ (S n1) w1).
Proof.
apply_mutual_ind degree_work_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_work_wrt_typ_S :
forall n1 w1,
  degree_work_wrt_typ n1 w1 ->
  degree_work_wrt_typ (S n1) w1.
Proof.
pose proof degree_work_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_work_wrt_exp_S_mutual :
(forall n1 w1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp (S n1) w1).
Proof.
apply_mutual_ind degree_work_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_work_wrt_exp_S :
forall n1 w1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp (S n1) w1.
Proof.
pose proof degree_work_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_abind_wrt_typ_O :
forall n1 ab1,
  degree_abind_wrt_typ O ab1 ->
  degree_abind_wrt_typ n1 ab1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_O : lngen.

Lemma degree_body_wrt_typ_O :
forall n1 body1,
  degree_body_wrt_typ O body1 ->
  degree_body_wrt_typ n1 body1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_body_wrt_exp_O :
forall n1 body1,
  degree_body_wrt_exp O body1 ->
  degree_body_wrt_exp n1 body1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

Lemma degree_cont_wrt_typ_O :
forall n1 c1,
  degree_cont_wrt_typ O c1 ->
  degree_cont_wrt_typ n1 c1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_O : lngen.

Lemma degree_contd_wrt_typ_O :
forall n1 cc1,
  degree_contd_wrt_typ O cc1 ->
  degree_contd_wrt_typ n1 cc1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_O : lngen.

Lemma degree_cont_wrt_exp_O :
forall n1 c1,
  degree_cont_wrt_exp O c1 ->
  degree_cont_wrt_exp n1 c1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_O : lngen.

Lemma degree_contd_wrt_exp_O :
forall n1 cc1,
  degree_contd_wrt_exp O cc1 ->
  degree_contd_wrt_exp n1 cc1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_O : lngen.

Lemma degree_dbind_wrt_typ_O :
forall n1 db1,
  degree_dbind_wrt_typ O db1 ->
  degree_dbind_wrt_typ n1 db1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_O : lngen.

Lemma degree_work_wrt_typ_O :
forall n1 w1,
  degree_work_wrt_typ O w1 ->
  degree_work_wrt_typ n1 w1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_O : lngen.

Lemma degree_work_wrt_exp_O :
forall n1 w1,
  degree_work_wrt_exp O w1 ->
  degree_work_wrt_exp n1 w1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_close_abind_wrt_typ_rec_mutual :
(forall ab1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_abind_wrt_typ (S n1) (close_abind_wrt_typ_rec n1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_close_abind_wrt_typ_rec :
forall ab1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_abind_wrt_typ (S n1) (close_abind_wrt_typ_rec n1 X1 ab1).
Proof.
pose proof degree_abind_wrt_typ_close_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_close_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_typ_rec_degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_body_wrt_typ (S n1) (close_body_wrt_typ_rec n1 X1 body1)) /\
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_typ_rec :
forall body1 X1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_body_wrt_typ (S n1) (close_body_wrt_typ_rec n1 X1 body1).
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_typ_rec_degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_close_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_typ_rec_degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_exp_rec_degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1 n2,
  degree_body_wrt_typ n2 body1 ->
  degree_body_wrt_typ n2 (close_body_wrt_exp_rec n1 x1 body1)) /\
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_exp_rec :
forall body1 x1 n1 n2,
  degree_body_wrt_typ n2 body1 ->
  degree_body_wrt_typ n2 (close_body_wrt_exp_rec n1 x1 body1).
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_exp_rec_degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_close_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_exp_rec_degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_typ_rec_degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1 n2,
  degree_body_wrt_exp n2 body1 ->
  degree_body_wrt_exp n2 (close_body_wrt_typ_rec n1 X1 body1)) /\
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_typ_rec :
forall body1 X1 n1 n2,
  degree_body_wrt_exp n2 body1 ->
  degree_body_wrt_exp n2 (close_body_wrt_typ_rec n1 X1 body1).
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_typ_rec_degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_close_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_typ_rec_degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_exp_rec_degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp (S n1) (close_body_wrt_exp_rec n1 x1 body1)) /\
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_exp_rec :
forall body1 x1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp (S n1) (close_body_wrt_exp_rec n1 x1 body1).
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_exp_rec_degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_close_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_exp_rec_degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_typ_rec_degree_contd_wrt_typ_close_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_cont_wrt_typ (S n1) (close_cont_wrt_typ_rec n1 X1 c1)) /\
(forall cc1 X1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_typ_rec :
forall c1 X1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_cont_wrt_typ (S n1) (close_cont_wrt_typ_rec n1 X1 c1).
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_typ_rec_degree_contd_wrt_typ_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_close_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_rec :
forall cc1 X1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cc1).
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_typ_rec_degree_contd_wrt_typ_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_exp_rec_degree_contd_wrt_typ_close_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1 n2,
  degree_cont_wrt_typ n2 c1 ->
  degree_cont_wrt_typ n2 (close_cont_wrt_exp_rec n1 x1 c1)) /\
(forall cc1 x1 n1 n2,
  degree_contd_wrt_typ n2 cc1 ->
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_exp_rec :
forall c1 x1 n1 n2,
  degree_cont_wrt_typ n2 c1 ->
  degree_cont_wrt_typ n2 (close_cont_wrt_exp_rec n1 x1 c1).
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_exp_rec_degree_contd_wrt_typ_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_close_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_rec :
forall cc1 x1 n1 n2,
  degree_contd_wrt_typ n2 cc1 ->
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cc1).
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_exp_rec_degree_contd_wrt_typ_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_typ_rec_degree_contd_wrt_exp_close_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1 n2,
  degree_cont_wrt_exp n2 c1 ->
  degree_cont_wrt_exp n2 (close_cont_wrt_typ_rec n1 X1 c1)) /\
(forall cc1 X1 n1 n2,
  degree_contd_wrt_exp n2 cc1 ->
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_typ_rec :
forall c1 X1 n1 n2,
  degree_cont_wrt_exp n2 c1 ->
  degree_cont_wrt_exp n2 (close_cont_wrt_typ_rec n1 X1 c1).
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_typ_rec_degree_contd_wrt_exp_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_close_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_rec :
forall cc1 X1 n1 n2,
  degree_contd_wrt_exp n2 cc1 ->
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cc1).
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_typ_rec_degree_contd_wrt_exp_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_exp_rec_degree_contd_wrt_exp_close_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp (S n1) (close_cont_wrt_exp_rec n1 x1 c1)) /\
(forall cc1 x1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_exp_rec :
forall c1 x1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp (S n1) (close_cont_wrt_exp_rec n1 x1 c1).
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_exp_rec_degree_contd_wrt_exp_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_close_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_rec :
forall cc1 x1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cc1).
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_exp_rec_degree_contd_wrt_exp_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1).
Proof.
pose proof degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_close_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_typ_rec_mutual :
(forall w1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_work_wrt_typ (S n1) (close_work_wrt_typ_rec n1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_typ_rec :
forall w1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_work_wrt_typ (S n1) (close_work_wrt_typ_rec n1 X1 w1).
Proof.
pose proof degree_work_wrt_typ_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_close_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_exp_rec_mutual :
(forall w1 x1 n1 n2,
  degree_work_wrt_typ n2 w1 ->
  degree_work_wrt_typ n2 (close_work_wrt_exp_rec n1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_exp_rec :
forall w1 x1 n1 n2,
  degree_work_wrt_typ n2 w1 ->
  degree_work_wrt_typ n2 (close_work_wrt_exp_rec n1 x1 w1).
Proof.
pose proof degree_work_wrt_typ_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_close_work_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_typ_rec_mutual :
(forall w1 X1 n1 n2,
  degree_work_wrt_exp n2 w1 ->
  degree_work_wrt_exp n2 (close_work_wrt_typ_rec n1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_typ_rec :
forall w1 X1 n1 n2,
  degree_work_wrt_exp n2 w1 ->
  degree_work_wrt_exp n2 (close_work_wrt_typ_rec n1 X1 w1).
Proof.
pose proof degree_work_wrt_exp_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_close_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_exp_rec_mutual :
(forall w1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp (S n1) (close_work_wrt_exp_rec n1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_exp_rec :
forall w1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp (S n1) (close_work_wrt_exp_rec n1 x1 w1).
Proof.
pose proof degree_work_wrt_exp_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_close_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_abind_wrt_typ_close_abind_wrt_typ :
forall ab1 X1,
  degree_abind_wrt_typ 0 ab1 ->
  degree_abind_wrt_typ 1 (close_abind_wrt_typ X1 ab1).
Proof.
unfold close_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_close_abind_wrt_typ : lngen.

Lemma degree_body_wrt_typ_close_body_wrt_typ :
forall body1 X1,
  degree_body_wrt_typ 0 body1 ->
  degree_body_wrt_typ 1 (close_body_wrt_typ X1 body1).
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_close_body_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_body_wrt_typ_close_body_wrt_exp :
forall body1 x1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_body_wrt_typ n1 (close_body_wrt_exp x1 body1).
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_close_body_wrt_exp : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_body_wrt_exp_close_body_wrt_typ :
forall body1 X1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp n1 (close_body_wrt_typ X1 body1).
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_close_body_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_body_wrt_exp_close_body_wrt_exp :
forall body1 x1,
  degree_body_wrt_exp 0 body1 ->
  degree_body_wrt_exp 1 (close_body_wrt_exp x1 body1).
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_close_body_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

Lemma degree_cont_wrt_typ_close_cont_wrt_typ :
forall c1 X1,
  degree_cont_wrt_typ 0 c1 ->
  degree_cont_wrt_typ 1 (close_cont_wrt_typ X1 c1).
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_close_cont_wrt_typ : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_typ :
forall cc1 X1,
  degree_contd_wrt_typ 0 cc1 ->
  degree_contd_wrt_typ 1 (close_contd_wrt_typ X1 cc1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_typ : lngen.

Lemma degree_cont_wrt_typ_close_cont_wrt_exp :
forall c1 x1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_cont_wrt_typ n1 (close_cont_wrt_exp x1 c1).
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_close_cont_wrt_exp : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_exp :
forall cc1 x1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_contd_wrt_typ n1 (close_contd_wrt_exp x1 cc1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_exp : lngen.

Lemma degree_cont_wrt_exp_close_cont_wrt_typ :
forall c1 X1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp n1 (close_cont_wrt_typ X1 c1).
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_close_cont_wrt_typ : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_typ :
forall cc1 X1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp n1 (close_contd_wrt_typ X1 cc1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_typ : lngen.

Lemma degree_cont_wrt_exp_close_cont_wrt_exp :
forall c1 x1,
  degree_cont_wrt_exp 0 c1 ->
  degree_cont_wrt_exp 1 (close_cont_wrt_exp x1 c1).
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_close_cont_wrt_exp : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_exp :
forall cc1 x1,
  degree_contd_wrt_exp 0 cc1 ->
  degree_contd_wrt_exp 1 (close_contd_wrt_exp x1 cc1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_exp : lngen.

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ :
forall db1 X1,
  degree_dbind_wrt_typ 0 db1 ->
  degree_dbind_wrt_typ 1 (close_dbind_wrt_typ X1 db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_close_dbind_wrt_typ : lngen.

Lemma degree_work_wrt_typ_close_work_wrt_typ :
forall w1 X1,
  degree_work_wrt_typ 0 w1 ->
  degree_work_wrt_typ 1 (close_work_wrt_typ X1 w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_close_work_wrt_typ : lngen.

Lemma degree_work_wrt_typ_close_work_wrt_exp :
forall w1 x1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_work_wrt_typ n1 (close_work_wrt_exp x1 w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_close_work_wrt_exp : lngen.

Lemma degree_work_wrt_exp_close_work_wrt_typ :
forall w1 X1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (close_work_wrt_typ X1 w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_close_work_wrt_typ : lngen.

Lemma degree_work_wrt_exp_close_work_wrt_exp :
forall w1 x1,
  degree_work_wrt_exp 0 w1 ->
  degree_work_wrt_exp 1 (close_work_wrt_exp x1 w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_close_work_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_close_abind_wrt_typ_rec_inv_mutual :
(forall ab1 X1 n1,
  degree_abind_wrt_typ (S n1) (close_abind_wrt_typ_rec n1 X1 ab1) ->
  degree_abind_wrt_typ n1 ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_close_abind_wrt_typ_rec_inv :
forall ab1 X1 n1,
  degree_abind_wrt_typ (S n1) (close_abind_wrt_typ_rec n1 X1 ab1) ->
  degree_abind_wrt_typ n1 ab1.
Proof.
pose proof degree_abind_wrt_typ_close_abind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abind_wrt_typ_close_abind_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_typ_rec_inv_degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall body1 X1 n1,
  degree_body_wrt_typ (S n1) (close_body_wrt_typ_rec n1 X1 body1) ->
  degree_body_wrt_typ n1 body1) /\
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_typ_rec_inv :
forall body1 X1 n1,
  degree_body_wrt_typ (S n1) (close_body_wrt_typ_rec n1 X1 body1) ->
  degree_body_wrt_typ n1 body1.
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_typ_rec_inv_degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_close_body_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_typ_rec_inv_degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_exp_rec_inv_degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall body1 x1 n1 n2,
  degree_body_wrt_typ n2 (close_body_wrt_exp_rec n1 x1 body1) ->
  degree_body_wrt_typ n2 body1) /\
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_close_body_wrt_exp_rec_inv :
forall body1 x1 n1 n2,
  degree_body_wrt_typ n2 (close_body_wrt_exp_rec n1 x1 body1) ->
  degree_body_wrt_typ n2 body1.
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_exp_rec_inv_degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_close_body_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_body_wrt_typ_close_body_wrt_exp_rec_inv_degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_typ_rec_inv_degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall body1 X1 n1 n2,
  degree_body_wrt_exp n2 (close_body_wrt_typ_rec n1 X1 body1) ->
  degree_body_wrt_exp n2 body1) /\
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_typ_rec_inv :
forall body1 X1 n1 n2,
  degree_body_wrt_exp n2 (close_body_wrt_typ_rec n1 X1 body1) ->
  degree_body_wrt_exp n2 body1.
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_typ_rec_inv_degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_close_body_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_typ_rec_inv_degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_exp_rec_inv_degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall body1 x1 n1,
  degree_body_wrt_exp (S n1) (close_body_wrt_exp_rec n1 x1 body1) ->
  degree_body_wrt_exp n1 body1) /\
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_close_body_wrt_exp_rec_inv :
forall body1 x1 n1,
  degree_body_wrt_exp (S n1) (close_body_wrt_exp_rec n1 x1 body1) ->
  degree_body_wrt_exp n1 body1.
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_exp_rec_inv_degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_close_body_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_body_wrt_exp_close_body_wrt_exp_rec_inv_degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_typ_rec_inv_degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv_mutual :
(forall c1 X1 n1,
  degree_cont_wrt_typ (S n1) (close_cont_wrt_typ_rec n1 X1 c1) ->
  degree_cont_wrt_typ n1 c1) /\
(forall cc1 X1 n1,
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cc1) ->
  degree_contd_wrt_typ n1 cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_typ_rec_inv :
forall c1 X1 n1,
  degree_cont_wrt_typ (S n1) (close_cont_wrt_typ_rec n1 X1 c1) ->
  degree_cont_wrt_typ n1 c1.
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_typ_rec_inv_degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_close_cont_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv :
forall cc1 X1 n1,
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cc1) ->
  degree_contd_wrt_typ n1 cc1.
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_typ_rec_inv_degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_exp_rec_inv_degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv_mutual :
(forall c1 x1 n1 n2,
  degree_cont_wrt_typ n2 (close_cont_wrt_exp_rec n1 x1 c1) ->
  degree_cont_wrt_typ n2 c1) /\
(forall cc1 x1 n1 n2,
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cc1) ->
  degree_contd_wrt_typ n2 cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_close_cont_wrt_exp_rec_inv :
forall c1 x1 n1 n2,
  degree_cont_wrt_typ n2 (close_cont_wrt_exp_rec n1 x1 c1) ->
  degree_cont_wrt_typ n2 c1.
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_exp_rec_inv_degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_close_cont_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv :
forall cc1 x1 n1 n2,
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cc1) ->
  degree_contd_wrt_typ n2 cc1.
Proof.
pose proof degree_cont_wrt_typ_close_cont_wrt_exp_rec_inv_degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_typ_rec_inv_degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv_mutual :
(forall c1 X1 n1 n2,
  degree_cont_wrt_exp n2 (close_cont_wrt_typ_rec n1 X1 c1) ->
  degree_cont_wrt_exp n2 c1) /\
(forall cc1 X1 n1 n2,
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cc1) ->
  degree_contd_wrt_exp n2 cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_typ_rec_inv :
forall c1 X1 n1 n2,
  degree_cont_wrt_exp n2 (close_cont_wrt_typ_rec n1 X1 c1) ->
  degree_cont_wrt_exp n2 c1.
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_typ_rec_inv_degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_close_cont_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv :
forall cc1 X1 n1 n2,
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cc1) ->
  degree_contd_wrt_exp n2 cc1.
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_typ_rec_inv_degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_exp_rec_inv_degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv_mutual :
(forall c1 x1 n1,
  degree_cont_wrt_exp (S n1) (close_cont_wrt_exp_rec n1 x1 c1) ->
  degree_cont_wrt_exp n1 c1) /\
(forall cc1 x1 n1,
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cc1) ->
  degree_contd_wrt_exp n1 cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_close_cont_wrt_exp_rec_inv :
forall c1 x1 n1,
  degree_cont_wrt_exp (S n1) (close_cont_wrt_exp_rec n1 x1 c1) ->
  degree_cont_wrt_exp n1 c1.
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_exp_rec_inv_degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_close_cont_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv :
forall cc1 x1 n1,
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cc1) ->
  degree_contd_wrt_exp n1 cc1.
Proof.
pose proof degree_cont_wrt_exp_close_cont_wrt_exp_rec_inv_degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv_mutual :
(forall db1 X1 n1,
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1) ->
  degree_dbind_wrt_typ n1 db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv :
forall db1 X1 n1,
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1) ->
  degree_dbind_wrt_typ n1 db1.
Proof.
pose proof degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_typ_rec_inv_mutual :
(forall w1 X1 n1,
  degree_work_wrt_typ (S n1) (close_work_wrt_typ_rec n1 X1 w1) ->
  degree_work_wrt_typ n1 w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_typ_rec_inv :
forall w1 X1 n1,
  degree_work_wrt_typ (S n1) (close_work_wrt_typ_rec n1 X1 w1) ->
  degree_work_wrt_typ n1 w1.
Proof.
pose proof degree_work_wrt_typ_close_work_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_close_work_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_exp_rec_inv_mutual :
(forall w1 x1 n1 n2,
  degree_work_wrt_typ n2 (close_work_wrt_exp_rec n1 x1 w1) ->
  degree_work_wrt_typ n2 w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_close_work_wrt_exp_rec_inv :
forall w1 x1 n1 n2,
  degree_work_wrt_typ n2 (close_work_wrt_exp_rec n1 x1 w1) ->
  degree_work_wrt_typ n2 w1.
Proof.
pose proof degree_work_wrt_typ_close_work_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_close_work_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_typ_rec_inv_mutual :
(forall w1 X1 n1 n2,
  degree_work_wrt_exp n2 (close_work_wrt_typ_rec n1 X1 w1) ->
  degree_work_wrt_exp n2 w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_typ_rec_inv :
forall w1 X1 n1 n2,
  degree_work_wrt_exp n2 (close_work_wrt_typ_rec n1 X1 w1) ->
  degree_work_wrt_exp n2 w1.
Proof.
pose proof degree_work_wrt_exp_close_work_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_close_work_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_exp_rec_inv_mutual :
(forall w1 x1 n1,
  degree_work_wrt_exp (S n1) (close_work_wrt_exp_rec n1 x1 w1) ->
  degree_work_wrt_exp n1 w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_close_work_wrt_exp_rec_inv :
forall w1 x1 n1,
  degree_work_wrt_exp (S n1) (close_work_wrt_exp_rec n1 x1 w1) ->
  degree_work_wrt_exp n1 w1.
Proof.
pose proof degree_work_wrt_exp_close_work_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_close_work_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_abind_wrt_typ_close_abind_wrt_typ_inv :
forall ab1 X1,
  degree_abind_wrt_typ 1 (close_abind_wrt_typ X1 ab1) ->
  degree_abind_wrt_typ 0 ab1.
Proof.
unfold close_abind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abind_wrt_typ_close_abind_wrt_typ_inv : lngen.

Lemma degree_body_wrt_typ_close_body_wrt_typ_inv :
forall body1 X1,
  degree_body_wrt_typ 1 (close_body_wrt_typ X1 body1) ->
  degree_body_wrt_typ 0 body1.
Proof.
unfold close_body_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_close_body_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_body_wrt_typ_close_body_wrt_exp_inv :
forall body1 x1 n1,
  degree_body_wrt_typ n1 (close_body_wrt_exp x1 body1) ->
  degree_body_wrt_typ n1 body1.
Proof.
unfold close_body_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_close_body_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_body_wrt_exp_close_body_wrt_typ_inv :
forall body1 X1 n1,
  degree_body_wrt_exp n1 (close_body_wrt_typ X1 body1) ->
  degree_body_wrt_exp n1 body1.
Proof.
unfold close_body_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_close_body_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_body_wrt_exp_close_body_wrt_exp_inv :
forall body1 x1,
  degree_body_wrt_exp 1 (close_body_wrt_exp x1 body1) ->
  degree_body_wrt_exp 0 body1.
Proof.
unfold close_body_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_close_body_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

Lemma degree_cont_wrt_typ_close_cont_wrt_typ_inv :
forall c1 X1,
  degree_cont_wrt_typ 1 (close_cont_wrt_typ X1 c1) ->
  degree_cont_wrt_typ 0 c1.
Proof.
unfold close_cont_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_close_cont_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_inv :
forall cc1 X1,
  degree_contd_wrt_typ 1 (close_contd_wrt_typ X1 cc1) ->
  degree_contd_wrt_typ 0 cc1.
Proof.
unfold close_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_typ_inv : lngen.

Lemma degree_cont_wrt_typ_close_cont_wrt_exp_inv :
forall c1 x1 n1,
  degree_cont_wrt_typ n1 (close_cont_wrt_exp x1 c1) ->
  degree_cont_wrt_typ n1 c1.
Proof.
unfold close_cont_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_close_cont_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_inv :
forall cc1 x1 n1,
  degree_contd_wrt_typ n1 (close_contd_wrt_exp x1 cc1) ->
  degree_contd_wrt_typ n1 cc1.
Proof.
unfold close_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_exp_inv : lngen.

Lemma degree_cont_wrt_exp_close_cont_wrt_typ_inv :
forall c1 X1 n1,
  degree_cont_wrt_exp n1 (close_cont_wrt_typ X1 c1) ->
  degree_cont_wrt_exp n1 c1.
Proof.
unfold close_cont_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_close_cont_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_inv :
forall cc1 X1 n1,
  degree_contd_wrt_exp n1 (close_contd_wrt_typ X1 cc1) ->
  degree_contd_wrt_exp n1 cc1.
Proof.
unfold close_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_typ_inv : lngen.

Lemma degree_cont_wrt_exp_close_cont_wrt_exp_inv :
forall c1 x1,
  degree_cont_wrt_exp 1 (close_cont_wrt_exp x1 c1) ->
  degree_cont_wrt_exp 0 c1.
Proof.
unfold close_cont_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_close_cont_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_inv :
forall cc1 x1,
  degree_contd_wrt_exp 1 (close_contd_wrt_exp x1 cc1) ->
  degree_contd_wrt_exp 0 cc1.
Proof.
unfold close_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_exp_inv : lngen.

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_inv :
forall db1 X1,
  degree_dbind_wrt_typ 1 (close_dbind_wrt_typ X1 db1) ->
  degree_dbind_wrt_typ 0 db1.
Proof.
unfold close_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_close_dbind_wrt_typ_inv : lngen.

Lemma degree_work_wrt_typ_close_work_wrt_typ_inv :
forall w1 X1,
  degree_work_wrt_typ 1 (close_work_wrt_typ X1 w1) ->
  degree_work_wrt_typ 0 w1.
Proof.
unfold close_work_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_close_work_wrt_typ_inv : lngen.

Lemma degree_work_wrt_typ_close_work_wrt_exp_inv :
forall w1 x1 n1,
  degree_work_wrt_typ n1 (close_work_wrt_exp x1 w1) ->
  degree_work_wrt_typ n1 w1.
Proof.
unfold close_work_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_close_work_wrt_exp_inv : lngen.

Lemma degree_work_wrt_exp_close_work_wrt_typ_inv :
forall w1 X1 n1,
  degree_work_wrt_exp n1 (close_work_wrt_typ X1 w1) ->
  degree_work_wrt_exp n1 w1.
Proof.
unfold close_work_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_close_work_wrt_typ_inv : lngen.

Lemma degree_work_wrt_exp_close_work_wrt_exp_inv :
forall w1 x1,
  degree_work_wrt_exp 1 (close_work_wrt_exp x1 w1) ->
  degree_work_wrt_exp 0 w1.
Proof.
unfold close_work_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_close_work_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_open_abind_wrt_typ_rec_mutual :
(forall ab1 A1 n1,
  degree_abind_wrt_typ (S n1) ab1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_abind_wrt_typ n1 (open_abind_wrt_typ_rec n1 A1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_open_abind_wrt_typ_rec :
forall ab1 A1 n1,
  degree_abind_wrt_typ (S n1) ab1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_abind_wrt_typ n1 (open_abind_wrt_typ_rec n1 A1 ab1).
Proof.
pose proof degree_abind_wrt_typ_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_open_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_typ_rec_degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall body1 A1 n1,
  degree_body_wrt_typ (S n1) body1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_body_wrt_typ n1 (open_body_wrt_typ_rec n1 A1 body1)) /\
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_typ_rec :
forall body1 A1 n1,
  degree_body_wrt_typ (S n1) body1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_body_wrt_typ n1 (open_body_wrt_typ_rec n1 A1 body1).
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_typ_rec_degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_typ_rec_degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_exp_rec_degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall body1 e1 n1 n2,
  degree_body_wrt_typ n1 body1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_body_wrt_typ n1 (open_body_wrt_exp_rec n2 e1 body1)) /\
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_exp_rec :
forall body1 e1 n1 n2,
  degree_body_wrt_typ n1 body1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_body_wrt_typ n1 (open_body_wrt_exp_rec n2 e1 body1).
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_exp_rec_degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_exp_rec_degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_typ_rec_degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall body1 A1 n1 n2,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp n1 (open_body_wrt_typ_rec n2 A1 body1)) /\
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_typ_rec :
forall body1 A1 n1 n2,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp n1 (open_body_wrt_typ_rec n2 A1 body1).
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_typ_rec_degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_typ_rec_degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_exp_rec_degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall body1 e1 n1,
  degree_body_wrt_exp (S n1) body1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_body_wrt_exp n1 (open_body_wrt_exp_rec n1 e1 body1)) /\
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_exp_rec :
forall body1 e1 n1,
  degree_body_wrt_exp (S n1) body1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_body_wrt_exp n1 (open_body_wrt_exp_rec n1 e1 body1).
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_exp_rec_degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_exp_rec_degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_typ_rec_degree_contd_wrt_typ_open_contd_wrt_typ_rec_mutual :
(forall c1 A1 n1,
  degree_cont_wrt_typ (S n1) c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_cont_wrt_typ n1 (open_cont_wrt_typ_rec n1 A1 c1)) /\
(forall cc1 A1 n1,
  degree_contd_wrt_typ (S n1) cc1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_typ_rec :
forall c1 A1 n1,
  degree_cont_wrt_typ (S n1) c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_cont_wrt_typ n1 (open_cont_wrt_typ_rec n1 A1 c1).
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_typ_rec_degree_contd_wrt_typ_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_rec :
forall cc1 A1 n1,
  degree_contd_wrt_typ (S n1) cc1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cc1).
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_typ_rec_degree_contd_wrt_typ_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_exp_rec_degree_contd_wrt_typ_open_contd_wrt_exp_rec_mutual :
(forall c1 e1 n1 n2,
  degree_cont_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_cont_wrt_typ n1 (open_cont_wrt_exp_rec n2 e1 c1)) /\
(forall cc1 e1 n1 n2,
  degree_contd_wrt_typ n1 cc1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_exp_rec :
forall c1 e1 n1 n2,
  degree_cont_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_cont_wrt_typ n1 (open_cont_wrt_exp_rec n2 e1 c1).
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_exp_rec_degree_contd_wrt_typ_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_rec :
forall cc1 e1 n1 n2,
  degree_contd_wrt_typ n1 cc1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cc1).
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_exp_rec_degree_contd_wrt_typ_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_typ_rec_degree_contd_wrt_exp_open_contd_wrt_typ_rec_mutual :
(forall c1 A1 n1 n2,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp n1 (open_cont_wrt_typ_rec n2 A1 c1)) /\
(forall cc1 A1 n1 n2,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_typ_rec :
forall c1 A1 n1 n2,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp n1 (open_cont_wrt_typ_rec n2 A1 c1).
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_typ_rec_degree_contd_wrt_exp_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_rec :
forall cc1 A1 n1 n2,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cc1).
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_typ_rec_degree_contd_wrt_exp_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_exp_rec_degree_contd_wrt_exp_open_contd_wrt_exp_rec_mutual :
(forall c1 e1 n1,
  degree_cont_wrt_exp (S n1) c1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_cont_wrt_exp n1 (open_cont_wrt_exp_rec n1 e1 c1)) /\
(forall cc1 e1 n1,
  degree_contd_wrt_exp (S n1) cc1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_exp_rec :
forall c1 e1 n1,
  degree_cont_wrt_exp (S n1) c1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_cont_wrt_exp n1 (open_cont_wrt_exp_rec n1 e1 c1).
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_exp_rec_degree_contd_wrt_exp_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_rec :
forall cc1 e1 n1,
  degree_contd_wrt_exp (S n1) cc1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cc1).
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_exp_rec_degree_contd_wrt_exp_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 n1,
  degree_dbind_wrt_typ (S n1) db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec :
forall db1 A1 n1,
  degree_dbind_wrt_typ (S n1) db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1).
Proof.
pose proof degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_typ_rec_mutual :
(forall w1 A1 n1,
  degree_work_wrt_typ (S n1) w1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_work_wrt_typ n1 (open_work_wrt_typ_rec n1 A1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_typ_rec :
forall w1 A1 n1,
  degree_work_wrt_typ (S n1) w1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_work_wrt_typ n1 (open_work_wrt_typ_rec n1 A1 w1).
Proof.
pose proof degree_work_wrt_typ_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_exp_rec_mutual :
(forall w1 e1 n1 n2,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (open_work_wrt_exp_rec n2 e1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_exp_rec :
forall w1 e1 n1 n2,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (open_work_wrt_exp_rec n2 e1 w1).
Proof.
pose proof degree_work_wrt_typ_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_open_work_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_typ_rec_mutual :
(forall w1 A1 n1 n2,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (open_work_wrt_typ_rec n2 A1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_typ_rec :
forall w1 A1 n1 n2,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (open_work_wrt_typ_rec n2 A1 w1).
Proof.
pose proof degree_work_wrt_exp_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_exp_rec_mutual :
(forall w1 e1 n1,
  degree_work_wrt_exp (S n1) w1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_work_wrt_exp n1 (open_work_wrt_exp_rec n1 e1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_exp_rec :
forall w1 e1 n1,
  degree_work_wrt_exp (S n1) w1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_work_wrt_exp n1 (open_work_wrt_exp_rec n1 e1 w1).
Proof.
pose proof degree_work_wrt_exp_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_open_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_abind_wrt_typ_open_abind_wrt_typ :
forall ab1 A1,
  degree_abind_wrt_typ 1 ab1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_abind_wrt_typ 0 (open_abind_wrt_typ ab1 A1).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_open_abind_wrt_typ : lngen.

Lemma degree_body_wrt_typ_open_body_wrt_typ :
forall body1 A1,
  degree_body_wrt_typ 1 body1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_body_wrt_typ 0 (open_body_wrt_typ body1 A1).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_open_body_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_body_wrt_typ_open_body_wrt_exp :
forall body1 e1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_body_wrt_typ n1 (open_body_wrt_exp body1 e1).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_open_body_wrt_exp : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_body_wrt_exp_open_body_wrt_typ :
forall body1 A1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp n1 (open_body_wrt_typ body1 A1).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_open_body_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

Lemma degree_body_wrt_exp_open_body_wrt_exp :
forall body1 e1,
  degree_body_wrt_exp 1 body1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_body_wrt_exp 0 (open_body_wrt_exp body1 e1).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_open_body_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma degree_cont_wrt_typ_open_cont_wrt_typ :
forall c1 A1,
  degree_cont_wrt_typ 1 c1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_cont_wrt_typ 0 (open_cont_wrt_typ c1 A1).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_open_cont_wrt_typ : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_typ :
forall cc1 A1,
  degree_contd_wrt_typ 1 cc1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_contd_wrt_typ 0 (open_contd_wrt_typ cc1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_typ : lngen.

Lemma degree_cont_wrt_typ_open_cont_wrt_exp :
forall c1 e1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_cont_wrt_typ n1 (open_cont_wrt_exp c1 e1).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_open_cont_wrt_exp : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_exp :
forall cc1 e1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_exp cc1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_exp : lngen.

Lemma degree_cont_wrt_exp_open_cont_wrt_typ :
forall c1 A1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp n1 (open_cont_wrt_typ c1 A1).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_open_cont_wrt_typ : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_typ :
forall cc1 A1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_typ cc1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_typ : lngen.

Lemma degree_cont_wrt_exp_open_cont_wrt_exp :
forall c1 e1,
  degree_cont_wrt_exp 1 c1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_cont_wrt_exp 0 (open_cont_wrt_exp c1 e1).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_open_cont_wrt_exp : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_exp :
forall cc1 e1,
  degree_contd_wrt_exp 1 cc1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_contd_wrt_exp 0 (open_contd_wrt_exp cc1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_exp : lngen.

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 A1,
  degree_dbind_wrt_typ 1 db1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_dbind_wrt_typ 0 (open_dbind_wrt_typ db1 A1).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_open_dbind_wrt_typ : lngen.

Lemma degree_work_wrt_typ_open_work_wrt_typ :
forall w1 A1,
  degree_work_wrt_typ 1 w1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_work_wrt_typ 0 (open_work_wrt_typ w1 A1).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_open_work_wrt_typ : lngen.

Lemma degree_work_wrt_typ_open_work_wrt_exp :
forall w1 e1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (open_work_wrt_exp w1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_open_work_wrt_exp : lngen.

Lemma degree_work_wrt_exp_open_work_wrt_typ :
forall w1 A1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (open_work_wrt_typ w1 A1).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_open_work_wrt_typ : lngen.

Lemma degree_work_wrt_exp_open_work_wrt_exp :
forall w1 e1,
  degree_work_wrt_exp 1 w1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_work_wrt_exp 0 (open_work_wrt_exp w1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_open_work_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_open_abind_wrt_typ_rec_inv_mutual :
(forall ab1 A1 n1,
  degree_abind_wrt_typ n1 (open_abind_wrt_typ_rec n1 A1 ab1) ->
  degree_abind_wrt_typ (S n1) ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_typ_open_abind_wrt_typ_rec_inv :
forall ab1 A1 n1,
  degree_abind_wrt_typ n1 (open_abind_wrt_typ_rec n1 A1 ab1) ->
  degree_abind_wrt_typ (S n1) ab1.
Proof.
pose proof degree_abind_wrt_typ_open_abind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abind_wrt_typ_open_abind_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_typ_rec_inv_degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall body1 A1 n1,
  degree_body_wrt_typ n1 (open_body_wrt_typ_rec n1 A1 body1) ->
  degree_body_wrt_typ (S n1) body1) /\
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_typ_rec_inv :
forall body1 A1 n1,
  degree_body_wrt_typ n1 (open_body_wrt_typ_rec n1 A1 body1) ->
  degree_body_wrt_typ (S n1) body1.
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_typ_rec_inv_degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_open_body_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_typ_rec_inv_degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_exp_rec_inv_degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall body1 e1 n1 n2,
  degree_body_wrt_typ n1 (open_body_wrt_exp_rec n2 e1 body1) ->
  degree_body_wrt_typ n1 body1) /\
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_typ_open_body_wrt_exp_rec_inv :
forall body1 e1 n1 n2,
  degree_body_wrt_typ n1 (open_body_wrt_exp_rec n2 e1 body1) ->
  degree_body_wrt_typ n1 body1.
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_exp_rec_inv_degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_open_body_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_body_wrt_typ_open_body_wrt_exp_rec_inv_degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_typ_rec_inv_degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall body1 A1 n1 n2,
  degree_body_wrt_exp n1 (open_body_wrt_typ_rec n2 A1 body1) ->
  degree_body_wrt_exp n1 body1) /\
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_typ_rec_inv :
forall body1 A1 n1 n2,
  degree_body_wrt_exp n1 (open_body_wrt_typ_rec n2 A1 body1) ->
  degree_body_wrt_exp n1 body1.
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_typ_rec_inv_degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_open_body_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_typ_rec_inv_degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_exp_rec_inv_degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall body1 e1 n1,
  degree_body_wrt_exp n1 (open_body_wrt_exp_rec n1 e1 body1) ->
  degree_body_wrt_exp (S n1) body1) /\
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_body_wrt_exp_open_body_wrt_exp_rec_inv :
forall body1 e1 n1,
  degree_body_wrt_exp n1 (open_body_wrt_exp_rec n1 e1 body1) ->
  degree_body_wrt_exp (S n1) body1.
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_exp_rec_inv_degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_open_body_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_body_wrt_exp_open_body_wrt_exp_rec_inv_degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_typ_rec_inv_degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv_mutual :
(forall c1 A1 n1,
  degree_cont_wrt_typ n1 (open_cont_wrt_typ_rec n1 A1 c1) ->
  degree_cont_wrt_typ (S n1) c1) /\
(forall cc1 A1 n1,
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cc1) ->
  degree_contd_wrt_typ (S n1) cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_typ_rec_inv :
forall c1 A1 n1,
  degree_cont_wrt_typ n1 (open_cont_wrt_typ_rec n1 A1 c1) ->
  degree_cont_wrt_typ (S n1) c1.
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_typ_rec_inv_degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_open_cont_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv :
forall cc1 A1 n1,
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cc1) ->
  degree_contd_wrt_typ (S n1) cc1.
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_typ_rec_inv_degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_exp_rec_inv_degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv_mutual :
(forall c1 e1 n1 n2,
  degree_cont_wrt_typ n1 (open_cont_wrt_exp_rec n2 e1 c1) ->
  degree_cont_wrt_typ n1 c1) /\
(forall cc1 e1 n1 n2,
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cc1) ->
  degree_contd_wrt_typ n1 cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_typ_open_cont_wrt_exp_rec_inv :
forall c1 e1 n1 n2,
  degree_cont_wrt_typ n1 (open_cont_wrt_exp_rec n2 e1 c1) ->
  degree_cont_wrt_typ n1 c1.
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_exp_rec_inv_degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_open_cont_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv :
forall cc1 e1 n1 n2,
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cc1) ->
  degree_contd_wrt_typ n1 cc1.
Proof.
pose proof degree_cont_wrt_typ_open_cont_wrt_exp_rec_inv_degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_typ_rec_inv_degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv_mutual :
(forall c1 A1 n1 n2,
  degree_cont_wrt_exp n1 (open_cont_wrt_typ_rec n2 A1 c1) ->
  degree_cont_wrt_exp n1 c1) /\
(forall cc1 A1 n1 n2,
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cc1) ->
  degree_contd_wrt_exp n1 cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_typ_rec_inv :
forall c1 A1 n1 n2,
  degree_cont_wrt_exp n1 (open_cont_wrt_typ_rec n2 A1 c1) ->
  degree_cont_wrt_exp n1 c1.
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_typ_rec_inv_degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_open_cont_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv :
forall cc1 A1 n1 n2,
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cc1) ->
  degree_contd_wrt_exp n1 cc1.
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_typ_rec_inv_degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_exp_rec_inv_degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv_mutual :
(forall c1 e1 n1,
  degree_cont_wrt_exp n1 (open_cont_wrt_exp_rec n1 e1 c1) ->
  degree_cont_wrt_exp (S n1) c1) /\
(forall cc1 e1 n1,
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cc1) ->
  degree_contd_wrt_exp (S n1) cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_cont_wrt_exp_open_cont_wrt_exp_rec_inv :
forall c1 e1 n1,
  degree_cont_wrt_exp n1 (open_cont_wrt_exp_rec n1 e1 c1) ->
  degree_cont_wrt_exp (S n1) c1.
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_exp_rec_inv_degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_open_cont_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv :
forall cc1 e1 n1,
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cc1) ->
  degree_contd_wrt_exp (S n1) cc1.
Proof.
pose proof degree_cont_wrt_exp_open_cont_wrt_exp_rec_inv_degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv_mutual :
(forall db1 A1 n1,
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1) ->
  degree_dbind_wrt_typ (S n1) db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv :
forall db1 A1 n1,
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1) ->
  degree_dbind_wrt_typ (S n1) db1.
Proof.
pose proof degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_typ_rec_inv_mutual :
(forall w1 A1 n1,
  degree_work_wrt_typ n1 (open_work_wrt_typ_rec n1 A1 w1) ->
  degree_work_wrt_typ (S n1) w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_typ_rec_inv :
forall w1 A1 n1,
  degree_work_wrt_typ n1 (open_work_wrt_typ_rec n1 A1 w1) ->
  degree_work_wrt_typ (S n1) w1.
Proof.
pose proof degree_work_wrt_typ_open_work_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_open_work_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_exp_rec_inv_mutual :
(forall w1 e1 n1 n2,
  degree_work_wrt_typ n1 (open_work_wrt_exp_rec n2 e1 w1) ->
  degree_work_wrt_typ n1 w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_typ_open_work_wrt_exp_rec_inv :
forall w1 e1 n1 n2,
  degree_work_wrt_typ n1 (open_work_wrt_exp_rec n2 e1 w1) ->
  degree_work_wrt_typ n1 w1.
Proof.
pose proof degree_work_wrt_typ_open_work_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_open_work_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_typ_rec_inv_mutual :
(forall w1 A1 n1 n2,
  degree_work_wrt_exp n1 (open_work_wrt_typ_rec n2 A1 w1) ->
  degree_work_wrt_exp n1 w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_typ_rec_inv :
forall w1 A1 n1 n2,
  degree_work_wrt_exp n1 (open_work_wrt_typ_rec n2 A1 w1) ->
  degree_work_wrt_exp n1 w1.
Proof.
pose proof degree_work_wrt_exp_open_work_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_open_work_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_exp_rec_inv_mutual :
(forall w1 e1 n1,
  degree_work_wrt_exp n1 (open_work_wrt_exp_rec n1 e1 w1) ->
  degree_work_wrt_exp (S n1) w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_work_wrt_exp_open_work_wrt_exp_rec_inv :
forall w1 e1 n1,
  degree_work_wrt_exp n1 (open_work_wrt_exp_rec n1 e1 w1) ->
  degree_work_wrt_exp (S n1) w1.
Proof.
pose proof degree_work_wrt_exp_open_work_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_open_work_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_abind_wrt_typ_open_abind_wrt_typ_inv :
forall ab1 A1,
  degree_abind_wrt_typ 0 (open_abind_wrt_typ ab1 A1) ->
  degree_abind_wrt_typ 1 ab1.
Proof.
unfold open_abind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abind_wrt_typ_open_abind_wrt_typ_inv : lngen.

Lemma degree_body_wrt_typ_open_body_wrt_typ_inv :
forall body1 A1,
  degree_body_wrt_typ 0 (open_body_wrt_typ body1 A1) ->
  degree_body_wrt_typ 1 body1.
Proof.
unfold open_body_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_open_body_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_body_wrt_typ_open_body_wrt_exp_inv :
forall body1 e1 n1,
  degree_body_wrt_typ n1 (open_body_wrt_exp body1 e1) ->
  degree_body_wrt_typ n1 body1.
Proof.
unfold open_body_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_typ_open_body_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_body_wrt_exp_open_body_wrt_typ_inv :
forall body1 A1 n1,
  degree_body_wrt_exp n1 (open_body_wrt_typ body1 A1) ->
  degree_body_wrt_exp n1 body1.
Proof.
unfold open_body_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_open_body_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_body_wrt_exp_open_body_wrt_exp_inv :
forall body1 e1,
  degree_body_wrt_exp 0 (open_body_wrt_exp body1 e1) ->
  degree_body_wrt_exp 1 body1.
Proof.
unfold open_body_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_body_wrt_exp_open_body_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.

Lemma degree_cont_wrt_typ_open_cont_wrt_typ_inv :
forall c1 A1,
  degree_cont_wrt_typ 0 (open_cont_wrt_typ c1 A1) ->
  degree_cont_wrt_typ 1 c1.
Proof.
unfold open_cont_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_open_cont_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_inv :
forall cc1 A1,
  degree_contd_wrt_typ 0 (open_contd_wrt_typ cc1 A1) ->
  degree_contd_wrt_typ 1 cc1.
Proof.
unfold open_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_typ_inv : lngen.

Lemma degree_cont_wrt_typ_open_cont_wrt_exp_inv :
forall c1 e1 n1,
  degree_cont_wrt_typ n1 (open_cont_wrt_exp c1 e1) ->
  degree_cont_wrt_typ n1 c1.
Proof.
unfold open_cont_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_typ_open_cont_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_inv :
forall cc1 e1 n1,
  degree_contd_wrt_typ n1 (open_contd_wrt_exp cc1 e1) ->
  degree_contd_wrt_typ n1 cc1.
Proof.
unfold open_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_exp_inv : lngen.

Lemma degree_cont_wrt_exp_open_cont_wrt_typ_inv :
forall c1 A1 n1,
  degree_cont_wrt_exp n1 (open_cont_wrt_typ c1 A1) ->
  degree_cont_wrt_exp n1 c1.
Proof.
unfold open_cont_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_open_cont_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_inv :
forall cc1 A1 n1,
  degree_contd_wrt_exp n1 (open_contd_wrt_typ cc1 A1) ->
  degree_contd_wrt_exp n1 cc1.
Proof.
unfold open_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_typ_inv : lngen.

Lemma degree_cont_wrt_exp_open_cont_wrt_exp_inv :
forall c1 e1,
  degree_cont_wrt_exp 0 (open_cont_wrt_exp c1 e1) ->
  degree_cont_wrt_exp 1 c1.
Proof.
unfold open_cont_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_cont_wrt_exp_open_cont_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_inv :
forall cc1 e1,
  degree_contd_wrt_exp 0 (open_contd_wrt_exp cc1 e1) ->
  degree_contd_wrt_exp 1 cc1.
Proof.
unfold open_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_exp_inv : lngen.

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_inv :
forall db1 A1,
  degree_dbind_wrt_typ 0 (open_dbind_wrt_typ db1 A1) ->
  degree_dbind_wrt_typ 1 db1.
Proof.
unfold open_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_open_dbind_wrt_typ_inv : lngen.

Lemma degree_work_wrt_typ_open_work_wrt_typ_inv :
forall w1 A1,
  degree_work_wrt_typ 0 (open_work_wrt_typ w1 A1) ->
  degree_work_wrt_typ 1 w1.
Proof.
unfold open_work_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_open_work_wrt_typ_inv : lngen.

Lemma degree_work_wrt_typ_open_work_wrt_exp_inv :
forall w1 e1 n1,
  degree_work_wrt_typ n1 (open_work_wrt_exp w1 e1) ->
  degree_work_wrt_typ n1 w1.
Proof.
unfold open_work_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_typ_open_work_wrt_exp_inv : lngen.

Lemma degree_work_wrt_exp_open_work_wrt_typ_inv :
forall w1 A1 n1,
  degree_work_wrt_exp n1 (open_work_wrt_typ w1 A1) ->
  degree_work_wrt_exp n1 w1.
Proof.
unfold open_work_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_open_work_wrt_typ_inv : lngen.

Lemma degree_work_wrt_exp_open_work_wrt_exp_inv :
forall w1 e1,
  degree_work_wrt_exp 0 (open_work_wrt_exp w1 e1) ->
  degree_work_wrt_exp 1 w1.
Proof.
unfold open_work_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_work_wrt_exp_open_work_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_typ_rec_inj_mutual :
(forall ab1 ab2 X1 n1,
  close_abind_wrt_typ_rec n1 X1 ab1 = close_abind_wrt_typ_rec n1 X1 ab2 ->
  ab1 = ab2).
Proof.
apply_mutual_ind abind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_typ_rec_inj :
forall ab1 ab2 X1 n1,
  close_abind_wrt_typ_rec n1 X1 ab1 = close_abind_wrt_typ_rec n1 X1 ab2 ->
  ab1 = ab2.
Proof.
pose proof close_abind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_abind_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_typ_rec_inj_close_exp_wrt_typ_rec_inj_mutual :
(forall body1 body2 X1 n1,
  close_body_wrt_typ_rec n1 X1 body1 = close_body_wrt_typ_rec n1 X1 body2 ->
  body1 = body2) /\
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind body_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_typ_rec_inj :
forall body1 body2 X1 n1,
  close_body_wrt_typ_rec n1 X1 body1 = close_body_wrt_typ_rec n1 X1 body2 ->
  body1 = body2.
Proof.
pose proof close_body_wrt_typ_rec_inj_close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_body_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_body_wrt_typ_rec_inj_close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_exp_rec_inj_close_exp_wrt_exp_rec_inj_mutual :
(forall body1 body2 x1 n1,
  close_body_wrt_exp_rec n1 x1 body1 = close_body_wrt_exp_rec n1 x1 body2 ->
  body1 = body2) /\
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind body_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_exp_rec_inj :
forall body1 body2 x1 n1,
  close_body_wrt_exp_rec n1 x1 body1 = close_body_wrt_exp_rec n1 x1 body2 ->
  body1 = body2.
Proof.
pose proof close_body_wrt_exp_rec_inj_close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_body_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_body_wrt_exp_rec_inj_close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_typ_rec_inj_close_contd_wrt_typ_rec_inj_mutual :
(forall c1 c2 X1 n1,
  close_cont_wrt_typ_rec n1 X1 c1 = close_cont_wrt_typ_rec n1 X1 c2 ->
  c1 = c2) /\
(forall cc1 cc2 X1 n1,
  close_contd_wrt_typ_rec n1 X1 cc1 = close_contd_wrt_typ_rec n1 X1 cc2 ->
  cc1 = cc2).
Proof.
apply_mutual_ind cont_contd_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_typ_rec_inj :
forall c1 c2 X1 n1,
  close_cont_wrt_typ_rec n1 X1 c1 = close_cont_wrt_typ_rec n1 X1 c2 ->
  c1 = c2.
Proof.
pose proof close_cont_wrt_typ_rec_inj_close_contd_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_cont_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_inj :
forall cc1 cc2 X1 n1,
  close_contd_wrt_typ_rec n1 X1 cc1 = close_contd_wrt_typ_rec n1 X1 cc2 ->
  cc1 = cc2.
Proof.
pose proof close_cont_wrt_typ_rec_inj_close_contd_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_contd_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_exp_rec_inj_close_contd_wrt_exp_rec_inj_mutual :
(forall c1 c2 x1 n1,
  close_cont_wrt_exp_rec n1 x1 c1 = close_cont_wrt_exp_rec n1 x1 c2 ->
  c1 = c2) /\
(forall cc1 cc2 x1 n1,
  close_contd_wrt_exp_rec n1 x1 cc1 = close_contd_wrt_exp_rec n1 x1 cc2 ->
  cc1 = cc2).
Proof.
apply_mutual_ind cont_contd_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_exp_rec_inj :
forall c1 c2 x1 n1,
  close_cont_wrt_exp_rec n1 x1 c1 = close_cont_wrt_exp_rec n1 x1 c2 ->
  c1 = c2.
Proof.
pose proof close_cont_wrt_exp_rec_inj_close_contd_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_cont_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_inj :
forall cc1 cc2 x1 n1,
  close_contd_wrt_exp_rec n1 x1 cc1 = close_contd_wrt_exp_rec n1 x1 cc2 ->
  cc1 = cc2.
Proof.
pose proof close_cont_wrt_exp_rec_inj_close_contd_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_contd_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_inj_mutual :
(forall db1 db2 X1 n1,
  close_dbind_wrt_typ_rec n1 X1 db1 = close_dbind_wrt_typ_rec n1 X1 db2 ->
  db1 = db2).
Proof.
apply_mutual_ind dbind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_inj :
forall db1 db2 X1 n1,
  close_dbind_wrt_typ_rec n1 X1 db1 = close_dbind_wrt_typ_rec n1 X1 db2 ->
  db1 = db2.
Proof.
pose proof close_dbind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dbind_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_typ_rec_inj_mutual :
(forall w1 w2 X1 n1,
  close_work_wrt_typ_rec n1 X1 w1 = close_work_wrt_typ_rec n1 X1 w2 ->
  w1 = w2).
Proof.
apply_mutual_ind work_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_typ_rec_inj :
forall w1 w2 X1 n1,
  close_work_wrt_typ_rec n1 X1 w1 = close_work_wrt_typ_rec n1 X1 w2 ->
  w1 = w2.
Proof.
pose proof close_work_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_work_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_exp_rec_inj_mutual :
(forall w1 w2 x1 n1,
  close_work_wrt_exp_rec n1 x1 w1 = close_work_wrt_exp_rec n1 x1 w2 ->
  w1 = w2).
Proof.
apply_mutual_ind work_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_exp_rec_inj :
forall w1 w2 x1 n1,
  close_work_wrt_exp_rec n1 x1 w1 = close_work_wrt_exp_rec n1 x1 w2 ->
  w1 = w2.
Proof.
pose proof close_work_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_work_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_abind_wrt_typ_inj :
forall ab1 ab2 X1,
  close_abind_wrt_typ X1 ab1 = close_abind_wrt_typ X1 ab2 ->
  ab1 = ab2.
Proof.
unfold close_abind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_abind_wrt_typ_inj : lngen.

Lemma close_body_wrt_typ_inj :
forall body1 body2 X1,
  close_body_wrt_typ X1 body1 = close_body_wrt_typ X1 body2 ->
  body1 = body2.
Proof.
unfold close_body_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_body_wrt_typ_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_body_wrt_exp_inj :
forall body1 body2 x1,
  close_body_wrt_exp x1 body1 = close_body_wrt_exp x1 body2 ->
  body1 = body2.
Proof.
unfold close_body_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_body_wrt_exp_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_cont_wrt_typ_inj :
forall c1 c2 X1,
  close_cont_wrt_typ X1 c1 = close_cont_wrt_typ X1 c2 ->
  c1 = c2.
Proof.
unfold close_cont_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_cont_wrt_typ_inj : lngen.

Lemma close_contd_wrt_typ_inj :
forall cc1 cc2 X1,
  close_contd_wrt_typ X1 cc1 = close_contd_wrt_typ X1 cc2 ->
  cc1 = cc2.
Proof.
unfold close_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_contd_wrt_typ_inj : lngen.

Lemma close_cont_wrt_exp_inj :
forall c1 c2 x1,
  close_cont_wrt_exp x1 c1 = close_cont_wrt_exp x1 c2 ->
  c1 = c2.
Proof.
unfold close_cont_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_cont_wrt_exp_inj : lngen.

Lemma close_contd_wrt_exp_inj :
forall cc1 cc2 x1,
  close_contd_wrt_exp x1 cc1 = close_contd_wrt_exp x1 cc2 ->
  cc1 = cc2.
Proof.
unfold close_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_contd_wrt_exp_inj : lngen.

Lemma close_dbind_wrt_typ_inj :
forall db1 db2 X1,
  close_dbind_wrt_typ X1 db1 = close_dbind_wrt_typ X1 db2 ->
  db1 = db2.
Proof.
unfold close_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_dbind_wrt_typ_inj : lngen.

Lemma close_work_wrt_typ_inj :
forall w1 w2 X1,
  close_work_wrt_typ X1 w1 = close_work_wrt_typ X1 w2 ->
  w1 = w2.
Proof.
unfold close_work_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_work_wrt_typ_inj : lngen.

Lemma close_work_wrt_exp_inj :
forall w1 w2 x1,
  close_work_wrt_exp x1 w1 = close_work_wrt_exp x1 w2 ->
  w1 = w2.
Proof.
unfold close_work_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_work_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_typ_rec_open_abind_wrt_typ_rec_mutual :
(forall ab1 X1 n1,
  X1 `notin` ftvar_in_abind ab1 ->
  close_abind_wrt_typ_rec n1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1) = ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_typ_rec_open_abind_wrt_typ_rec :
forall ab1 X1 n1,
  X1 `notin` ftvar_in_abind ab1 ->
  close_abind_wrt_typ_rec n1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1) = ab1.
Proof.
pose proof close_abind_wrt_typ_rec_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abind_wrt_typ_rec_open_abind_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_abind_wrt_typ_rec_open_abind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_typ_rec_open_body_wrt_typ_rec_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1,
  X1 `notin` ftvar_in_body body1 ->
  close_body_wrt_typ_rec n1 X1 (open_body_wrt_typ_rec n1 (typ_var_f X1) body1) = body1) /\
(forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_typ_rec_open_body_wrt_typ_rec :
forall body1 X1 n1,
  X1 `notin` ftvar_in_body body1 ->
  close_body_wrt_typ_rec n1 X1 (open_body_wrt_typ_rec n1 (typ_var_f X1) body1) = body1.
Proof.
pose proof close_body_wrt_typ_rec_open_body_wrt_typ_rec_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_body_wrt_typ_rec_open_body_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_body_wrt_typ_rec_open_body_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1.
Proof.
pose proof close_body_wrt_typ_rec_open_body_wrt_typ_rec_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_exp_rec_open_body_wrt_exp_rec_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1,
  x1 `notin` fvar_in_body body1 ->
  close_body_wrt_exp_rec n1 x1 (open_body_wrt_exp_rec n1 (exp_var_f x1) body1) = body1) /\
(forall e1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_exp_rec_open_body_wrt_exp_rec :
forall body1 x1 n1,
  x1 `notin` fvar_in_body body1 ->
  close_body_wrt_exp_rec n1 x1 (open_body_wrt_exp_rec n1 (exp_var_f x1) body1) = body1.
Proof.
pose proof close_body_wrt_exp_rec_open_body_wrt_exp_rec_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_body_wrt_exp_rec_open_body_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_body_wrt_exp_rec_open_body_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_body_wrt_exp_rec_open_body_wrt_exp_rec_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  X1 `notin` ftvar_in_cont c1 ->
  close_cont_wrt_typ_rec n1 X1 (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1) = c1) /\
(forall cc1 X1 n1,
  X1 `notin` ftvar_in_contd cc1 ->
  close_contd_wrt_typ_rec n1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1) = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_typ_rec_open_cont_wrt_typ_rec :
forall c1 X1 n1,
  X1 `notin` ftvar_in_cont c1 ->
  close_cont_wrt_typ_rec n1 X1 (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1) = c1.
Proof.
pose proof close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_cont_wrt_typ_rec_open_cont_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_cont_wrt_typ_rec_open_cont_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_open_contd_wrt_typ_rec :
forall cc1 X1 n1,
  X1 `notin` ftvar_in_contd cc1 ->
  close_contd_wrt_typ_rec n1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1) = cc1.
Proof.
pose proof close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_rec_open_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_rec_open_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1,
  x1 `notin` fvar_in_cont c1 ->
  close_cont_wrt_exp_rec n1 x1 (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1) = c1) /\
(forall cc1 x1 n1,
  x1 `notin` fvar_in_contd cc1 ->
  close_contd_wrt_exp_rec n1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1) = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_exp_rec_open_cont_wrt_exp_rec :
forall c1 x1 n1,
  x1 `notin` fvar_in_cont c1 ->
  close_cont_wrt_exp_rec n1 x1 (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1) = c1.
Proof.
pose proof close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_cont_wrt_exp_rec_open_cont_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_cont_wrt_exp_rec_open_cont_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_open_contd_wrt_exp_rec :
forall cc1 x1 n1,
  x1 `notin` fvar_in_contd cc1 ->
  close_contd_wrt_exp_rec n1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1) = cc1.
Proof.
pose proof close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_rec_open_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_rec_open_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec :
forall db1 X1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = db1.
Proof.
pose proof close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual :
(forall w1 X1 n1,
  X1 `notin` ftvar_in_work w1 ->
  close_work_wrt_typ_rec n1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1) = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_typ_rec_open_work_wrt_typ_rec :
forall w1 X1 n1,
  X1 `notin` ftvar_in_work w1 ->
  close_work_wrt_typ_rec n1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1) = w1.
Proof.
pose proof close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_work_wrt_typ_rec_open_work_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_work_wrt_typ_rec_open_work_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual :
(forall w1 x1 n1,
  x1 `notin` fvar_in_work w1 ->
  close_work_wrt_exp_rec n1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1) = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_exp_rec_open_work_wrt_exp_rec :
forall w1 x1 n1,
  x1 `notin` fvar_in_work w1 ->
  close_work_wrt_exp_rec n1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1) = w1.
Proof.
pose proof close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_work_wrt_exp_rec_open_work_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_work_wrt_exp_rec_open_work_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (typ_var_f X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_abind_wrt_typ_open_abind_wrt_typ :
forall ab1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  close_abind_wrt_typ X1 (open_abind_wrt_typ ab1 (typ_var_f X1)) = ab1.
Proof.
unfold close_abind_wrt_typ; unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_abind_wrt_typ_open_abind_wrt_typ : lngen.
#[export] Hint Rewrite close_abind_wrt_typ_open_abind_wrt_typ using solve [auto] : lngen.

Lemma close_body_wrt_typ_open_body_wrt_typ :
forall body1 X1,
  X1 `notin` ftvar_in_body body1 ->
  close_body_wrt_typ X1 (open_body_wrt_typ body1 (typ_var_f X1)) = body1.
Proof.
unfold close_body_wrt_typ; unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_body_wrt_typ_open_body_wrt_typ : lngen.
#[export] Hint Rewrite close_body_wrt_typ_open_body_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (typ_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

Lemma close_body_wrt_exp_open_body_wrt_exp :
forall body1 x1,
  x1 `notin` fvar_in_body body1 ->
  close_body_wrt_exp x1 (open_body_wrt_exp body1 (exp_var_f x1)) = body1.
Proof.
unfold close_body_wrt_exp; unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_body_wrt_exp_open_body_wrt_exp : lngen.
#[export] Hint Rewrite close_body_wrt_exp_open_body_wrt_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

Lemma close_cont_wrt_typ_open_cont_wrt_typ :
forall c1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  close_cont_wrt_typ X1 (open_cont_wrt_typ c1 (typ_var_f X1)) = c1.
Proof.
unfold close_cont_wrt_typ; unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_cont_wrt_typ_open_cont_wrt_typ : lngen.
#[export] Hint Rewrite close_cont_wrt_typ_open_cont_wrt_typ using solve [auto] : lngen.

Lemma close_contd_wrt_typ_open_contd_wrt_typ :
forall cc1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  close_contd_wrt_typ X1 (open_contd_wrt_typ cc1 (typ_var_f X1)) = cc1.
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_open_contd_wrt_typ : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_open_contd_wrt_typ using solve [auto] : lngen.

Lemma close_cont_wrt_exp_open_cont_wrt_exp :
forall c1 x1,
  x1 `notin` fvar_in_cont c1 ->
  close_cont_wrt_exp x1 (open_cont_wrt_exp c1 (exp_var_f x1)) = c1.
Proof.
unfold close_cont_wrt_exp; unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_cont_wrt_exp_open_cont_wrt_exp : lngen.
#[export] Hint Rewrite close_cont_wrt_exp_open_cont_wrt_exp using solve [auto] : lngen.

Lemma close_contd_wrt_exp_open_contd_wrt_exp :
forall cc1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  close_contd_wrt_exp x1 (open_contd_wrt_exp cc1 (exp_var_f x1)) = cc1.
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_open_contd_wrt_exp : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_open_contd_wrt_exp using solve [auto] : lngen.

Lemma close_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ X1 (open_dbind_wrt_typ db1 (typ_var_f X1)) = db1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_open_dbind_wrt_typ : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_open_dbind_wrt_typ using solve [auto] : lngen.

Lemma close_work_wrt_typ_open_work_wrt_typ :
forall w1 X1,
  X1 `notin` ftvar_in_work w1 ->
  close_work_wrt_typ X1 (open_work_wrt_typ w1 (typ_var_f X1)) = w1.
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_work_wrt_typ_open_work_wrt_typ : lngen.
#[export] Hint Rewrite close_work_wrt_typ_open_work_wrt_typ using solve [auto] : lngen.

Lemma close_work_wrt_exp_open_work_wrt_exp :
forall w1 x1,
  x1 `notin` fvar_in_work w1 ->
  close_work_wrt_exp x1 (open_work_wrt_exp w1 (exp_var_f x1)) = w1.
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_work_wrt_exp_open_work_wrt_exp : lngen.
#[export] Hint Rewrite close_work_wrt_exp_open_work_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_typ_rec_close_abind_wrt_typ_rec_mutual :
(forall ab1 X1 n1,
  open_abind_wrt_typ_rec n1 (typ_var_f X1) (close_abind_wrt_typ_rec n1 X1 ab1) = ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_typ_rec_close_abind_wrt_typ_rec :
forall ab1 X1 n1,
  open_abind_wrt_typ_rec n1 (typ_var_f X1) (close_abind_wrt_typ_rec n1 X1 ab1) = ab1.
Proof.
pose proof open_abind_wrt_typ_rec_close_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abind_wrt_typ_rec_close_abind_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_abind_wrt_typ_rec_close_abind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_typ_rec_close_body_wrt_typ_rec_open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1,
  open_body_wrt_typ_rec n1 (typ_var_f X1) (close_body_wrt_typ_rec n1 X1 body1) = body1) /\
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_typ_rec_close_body_wrt_typ_rec :
forall body1 X1 n1,
  open_body_wrt_typ_rec n1 (typ_var_f X1) (close_body_wrt_typ_rec n1 X1 body1) = body1.
Proof.
pose proof open_body_wrt_typ_rec_close_body_wrt_typ_rec_open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_body_wrt_typ_rec_close_body_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_body_wrt_typ_rec_close_body_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_body_wrt_typ_rec_close_body_wrt_typ_rec_open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_exp_rec_close_body_wrt_exp_rec_open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1,
  open_body_wrt_exp_rec n1 (exp_var_f x1) (close_body_wrt_exp_rec n1 x1 body1) = body1) /\
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_exp_rec_close_body_wrt_exp_rec :
forall body1 x1 n1,
  open_body_wrt_exp_rec n1 (exp_var_f x1) (close_body_wrt_exp_rec n1 x1 body1) = body1.
Proof.
pose proof open_body_wrt_exp_rec_close_body_wrt_exp_rec_open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_body_wrt_exp_rec_close_body_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_body_wrt_exp_rec_close_body_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_body_wrt_exp_rec_close_body_wrt_exp_rec_open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_typ_rec_close_cont_wrt_typ_rec_open_contd_wrt_typ_rec_close_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  open_cont_wrt_typ_rec n1 (typ_var_f X1) (close_cont_wrt_typ_rec n1 X1 c1) = c1) /\
(forall cc1 X1 n1,
  open_contd_wrt_typ_rec n1 (typ_var_f X1) (close_contd_wrt_typ_rec n1 X1 cc1) = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_typ_rec_close_cont_wrt_typ_rec :
forall c1 X1 n1,
  open_cont_wrt_typ_rec n1 (typ_var_f X1) (close_cont_wrt_typ_rec n1 X1 c1) = c1.
Proof.
pose proof open_cont_wrt_typ_rec_close_cont_wrt_typ_rec_open_contd_wrt_typ_rec_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_cont_wrt_typ_rec_close_cont_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_cont_wrt_typ_rec_close_cont_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_close_contd_wrt_typ_rec :
forall cc1 X1 n1,
  open_contd_wrt_typ_rec n1 (typ_var_f X1) (close_contd_wrt_typ_rec n1 X1 cc1) = cc1.
Proof.
pose proof open_cont_wrt_typ_rec_close_cont_wrt_typ_rec_open_contd_wrt_typ_rec_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_rec_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_rec_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_exp_rec_close_cont_wrt_exp_rec_open_contd_wrt_exp_rec_close_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1,
  open_cont_wrt_exp_rec n1 (exp_var_f x1) (close_cont_wrt_exp_rec n1 x1 c1) = c1) /\
(forall cc1 x1 n1,
  open_contd_wrt_exp_rec n1 (exp_var_f x1) (close_contd_wrt_exp_rec n1 x1 cc1) = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_exp_rec_close_cont_wrt_exp_rec :
forall c1 x1 n1,
  open_cont_wrt_exp_rec n1 (exp_var_f x1) (close_cont_wrt_exp_rec n1 x1 c1) = c1.
Proof.
pose proof open_cont_wrt_exp_rec_close_cont_wrt_exp_rec_open_contd_wrt_exp_rec_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_cont_wrt_exp_rec_close_cont_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_cont_wrt_exp_rec_close_cont_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_close_contd_wrt_exp_rec :
forall cc1 x1 n1,
  open_contd_wrt_exp_rec n1 (exp_var_f x1) (close_contd_wrt_exp_rec n1 x1 cc1) = cc1.
Proof.
pose proof open_cont_wrt_exp_rec_close_cont_wrt_exp_rec_open_contd_wrt_exp_rec_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_rec_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_rec_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) (close_dbind_wrt_typ_rec n1 X1 db1) = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) (close_dbind_wrt_typ_rec n1 X1 db1) = db1.
Proof.
pose proof open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_typ_rec_close_work_wrt_typ_rec_mutual :
(forall w1 X1 n1,
  open_work_wrt_typ_rec n1 (typ_var_f X1) (close_work_wrt_typ_rec n1 X1 w1) = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_typ_rec_close_work_wrt_typ_rec :
forall w1 X1 n1,
  open_work_wrt_typ_rec n1 (typ_var_f X1) (close_work_wrt_typ_rec n1 X1 w1) = w1.
Proof.
pose proof open_work_wrt_typ_rec_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_work_wrt_typ_rec_close_work_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_work_wrt_typ_rec_close_work_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_exp_rec_close_work_wrt_exp_rec_mutual :
(forall w1 x1 n1,
  open_work_wrt_exp_rec n1 (exp_var_f x1) (close_work_wrt_exp_rec n1 x1 w1) = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_exp_rec_close_work_wrt_exp_rec :
forall w1 x1 n1,
  open_work_wrt_exp_rec n1 (exp_var_f x1) (close_work_wrt_exp_rec n1 x1 w1) = w1.
Proof.
pose proof open_work_wrt_exp_rec_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_work_wrt_exp_rec_close_work_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_work_wrt_exp_rec_close_work_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (typ_var_f X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_abind_wrt_typ_close_abind_wrt_typ :
forall ab1 X1,
  open_abind_wrt_typ (close_abind_wrt_typ X1 ab1) (typ_var_f X1) = ab1.
Proof.
unfold close_abind_wrt_typ; unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_abind_wrt_typ_close_abind_wrt_typ : lngen.
#[export] Hint Rewrite open_abind_wrt_typ_close_abind_wrt_typ using solve [auto] : lngen.

Lemma open_body_wrt_typ_close_body_wrt_typ :
forall body1 X1,
  open_body_wrt_typ (close_body_wrt_typ X1 body1) (typ_var_f X1) = body1.
Proof.
unfold close_body_wrt_typ; unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_body_wrt_typ_close_body_wrt_typ : lngen.
#[export] Hint Rewrite open_body_wrt_typ_close_body_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (typ_var_f X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_body_wrt_exp_close_body_wrt_exp :
forall body1 x1,
  open_body_wrt_exp (close_body_wrt_exp x1 body1) (exp_var_f x1) = body1.
Proof.
unfold close_body_wrt_exp; unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_body_wrt_exp_close_body_wrt_exp : lngen.
#[export] Hint Rewrite open_body_wrt_exp_close_body_wrt_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma open_cont_wrt_typ_close_cont_wrt_typ :
forall c1 X1,
  open_cont_wrt_typ (close_cont_wrt_typ X1 c1) (typ_var_f X1) = c1.
Proof.
unfold close_cont_wrt_typ; unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_cont_wrt_typ_close_cont_wrt_typ : lngen.
#[export] Hint Rewrite open_cont_wrt_typ_close_cont_wrt_typ using solve [auto] : lngen.

Lemma open_contd_wrt_typ_close_contd_wrt_typ :
forall cc1 X1,
  open_contd_wrt_typ (close_contd_wrt_typ X1 cc1) (typ_var_f X1) = cc1.
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_close_contd_wrt_typ using solve [auto] : lngen.

Lemma open_cont_wrt_exp_close_cont_wrt_exp :
forall c1 x1,
  open_cont_wrt_exp (close_cont_wrt_exp x1 c1) (exp_var_f x1) = c1.
Proof.
unfold close_cont_wrt_exp; unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_cont_wrt_exp_close_cont_wrt_exp : lngen.
#[export] Hint Rewrite open_cont_wrt_exp_close_cont_wrt_exp using solve [auto] : lngen.

Lemma open_contd_wrt_exp_close_contd_wrt_exp :
forall cc1 x1,
  open_contd_wrt_exp (close_contd_wrt_exp x1 cc1) (exp_var_f x1) = cc1.
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_close_contd_wrt_exp using solve [auto] : lngen.

Lemma open_dbind_wrt_typ_close_dbind_wrt_typ :
forall db1 X1,
  open_dbind_wrt_typ (close_dbind_wrt_typ X1 db1) (typ_var_f X1) = db1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_close_dbind_wrt_typ : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_close_dbind_wrt_typ using solve [auto] : lngen.

Lemma open_work_wrt_typ_close_work_wrt_typ :
forall w1 X1,
  open_work_wrt_typ (close_work_wrt_typ X1 w1) (typ_var_f X1) = w1.
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_work_wrt_typ_close_work_wrt_typ : lngen.
#[export] Hint Rewrite open_work_wrt_typ_close_work_wrt_typ using solve [auto] : lngen.

Lemma open_work_wrt_exp_close_work_wrt_exp :
forall w1 x1,
  open_work_wrt_exp (close_work_wrt_exp x1 w1) (exp_var_f x1) = w1.
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_work_wrt_exp_close_work_wrt_exp : lngen.
#[export] Hint Rewrite open_work_wrt_exp_close_work_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_typ_rec_inj_mutual :
(forall ab2 ab1 X1 n1,
  X1 `notin` ftvar_in_abind ab2 ->
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ_rec n1 (typ_var_f X1) ab2 = open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1 ->
  ab2 = ab1).
Proof.
apply_mutual_ind abind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_typ_rec_inj :
forall ab2 ab1 X1 n1,
  X1 `notin` ftvar_in_abind ab2 ->
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ_rec n1 (typ_var_f X1) ab2 = open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1 ->
  ab2 = ab1.
Proof.
pose proof open_abind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_abind_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_typ_rec_inj_open_exp_wrt_typ_rec_inj_mutual :
(forall body2 body1 X1 n1,
  X1 `notin` ftvar_in_body body2 ->
  X1 `notin` ftvar_in_body body1 ->
  open_body_wrt_typ_rec n1 (typ_var_f X1) body2 = open_body_wrt_typ_rec n1 (typ_var_f X1) body1 ->
  body2 = body1) /\
(forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind body_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_typ_rec_inj :
forall body2 body1 X1 n1,
  X1 `notin` ftvar_in_body body2 ->
  X1 `notin` ftvar_in_body body1 ->
  open_body_wrt_typ_rec n1 (typ_var_f X1) body2 = open_body_wrt_typ_rec n1 (typ_var_f X1) body1 ->
  body2 = body1.
Proof.
pose proof open_body_wrt_typ_rec_inj_open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_body_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_body_wrt_typ_rec_inj_open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_exp_rec_inj_open_exp_wrt_exp_rec_inj_mutual :
(forall body2 body1 x1 n1,
  x1 `notin` fvar_in_body body2 ->
  x1 `notin` fvar_in_body body1 ->
  open_body_wrt_exp_rec n1 (exp_var_f x1) body2 = open_body_wrt_exp_rec n1 (exp_var_f x1) body1 ->
  body2 = body1) /\
(forall e2 e1 x1 n1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind body_exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_exp_rec_inj :
forall body2 body1 x1 n1,
  x1 `notin` fvar_in_body body2 ->
  x1 `notin` fvar_in_body body1 ->
  open_body_wrt_exp_rec n1 (exp_var_f x1) body2 = open_body_wrt_exp_rec n1 (exp_var_f x1) body1 ->
  body2 = body1.
Proof.
pose proof open_body_wrt_exp_rec_inj_open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_body_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_body_wrt_exp_rec_inj_open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_typ_rec_inj_open_contd_wrt_typ_rec_inj_mutual :
(forall c2 c1 X1 n1,
  X1 `notin` ftvar_in_cont c2 ->
  X1 `notin` ftvar_in_cont c1 ->
  open_cont_wrt_typ_rec n1 (typ_var_f X1) c2 = open_cont_wrt_typ_rec n1 (typ_var_f X1) c1 ->
  c2 = c1) /\
(forall cc2 cc1 X1 n1,
  X1 `notin` ftvar_in_contd cc2 ->
  X1 `notin` ftvar_in_contd cc1 ->
  open_contd_wrt_typ_rec n1 (typ_var_f X1) cc2 = open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1 ->
  cc2 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_typ_rec_inj :
forall c2 c1 X1 n1,
  X1 `notin` ftvar_in_cont c2 ->
  X1 `notin` ftvar_in_cont c1 ->
  open_cont_wrt_typ_rec n1 (typ_var_f X1) c2 = open_cont_wrt_typ_rec n1 (typ_var_f X1) c1 ->
  c2 = c1.
Proof.
pose proof open_cont_wrt_typ_rec_inj_open_contd_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_cont_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_inj :
forall cc2 cc1 X1 n1,
  X1 `notin` ftvar_in_contd cc2 ->
  X1 `notin` ftvar_in_contd cc1 ->
  open_contd_wrt_typ_rec n1 (typ_var_f X1) cc2 = open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1 ->
  cc2 = cc1.
Proof.
pose proof open_cont_wrt_typ_rec_inj_open_contd_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_contd_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_exp_rec_inj_open_contd_wrt_exp_rec_inj_mutual :
(forall c2 c1 x1 n1,
  x1 `notin` fvar_in_cont c2 ->
  x1 `notin` fvar_in_cont c1 ->
  open_cont_wrt_exp_rec n1 (exp_var_f x1) c2 = open_cont_wrt_exp_rec n1 (exp_var_f x1) c1 ->
  c2 = c1) /\
(forall cc2 cc1 x1 n1,
  x1 `notin` fvar_in_contd cc2 ->
  x1 `notin` fvar_in_contd cc1 ->
  open_contd_wrt_exp_rec n1 (exp_var_f x1) cc2 = open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1 ->
  cc2 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_exp_rec_inj :
forall c2 c1 x1 n1,
  x1 `notin` fvar_in_cont c2 ->
  x1 `notin` fvar_in_cont c1 ->
  open_cont_wrt_exp_rec n1 (exp_var_f x1) c2 = open_cont_wrt_exp_rec n1 (exp_var_f x1) c1 ->
  c2 = c1.
Proof.
pose proof open_cont_wrt_exp_rec_inj_open_contd_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_cont_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_inj :
forall cc2 cc1 x1 n1,
  x1 `notin` fvar_in_contd cc2 ->
  x1 `notin` fvar_in_contd cc1 ->
  open_contd_wrt_exp_rec n1 (exp_var_f x1) cc2 = open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1 ->
  cc2 = cc1.
Proof.
pose proof open_cont_wrt_exp_rec_inj_open_contd_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_contd_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_inj_mutual :
(forall db2 db1 X1 n1,
  X1 `notin` ftvar_in_dbind db2 ->
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) db2 = open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1 ->
  db2 = db1).
Proof.
apply_mutual_ind dbind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_inj :
forall db2 db1 X1 n1,
  X1 `notin` ftvar_in_dbind db2 ->
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) db2 = open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1 ->
  db2 = db1.
Proof.
pose proof open_dbind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dbind_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_typ_rec_inj_mutual :
(forall w2 w1 X1 n1,
  X1 `notin` ftvar_in_work w2 ->
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ_rec n1 (typ_var_f X1) w2 = open_work_wrt_typ_rec n1 (typ_var_f X1) w1 ->
  w2 = w1).
Proof.
apply_mutual_ind work_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_typ_rec_inj :
forall w2 w1 X1 n1,
  X1 `notin` ftvar_in_work w2 ->
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ_rec n1 (typ_var_f X1) w2 = open_work_wrt_typ_rec n1 (typ_var_f X1) w1 ->
  w2 = w1.
Proof.
pose proof open_work_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_work_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_exp_rec_inj_mutual :
(forall w2 w1 x1 n1,
  x1 `notin` fvar_in_work w2 ->
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp_rec n1 (exp_var_f x1) w2 = open_work_wrt_exp_rec n1 (exp_var_f x1) w1 ->
  w2 = w1).
Proof.
apply_mutual_ind work_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_exp_rec_inj :
forall w2 w1 x1 n1,
  x1 `notin` fvar_in_work w2 ->
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp_rec n1 (exp_var_f x1) w2 = open_work_wrt_exp_rec n1 (exp_var_f x1) w1 ->
  w2 = w1.
Proof.
pose proof open_work_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_work_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A2 (typ_var_f X1) = open_typ_wrt_typ A1 (typ_var_f X1) ->
  A2 = A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_abind_wrt_typ_inj :
forall ab2 ab1 X1,
  X1 `notin` ftvar_in_abind ab2 ->
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ ab2 (typ_var_f X1) = open_abind_wrt_typ ab1 (typ_var_f X1) ->
  ab2 = ab1.
Proof.
unfold open_abind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_abind_wrt_typ_inj : lngen.

Lemma open_body_wrt_typ_inj :
forall body2 body1 X1,
  X1 `notin` ftvar_in_body body2 ->
  X1 `notin` ftvar_in_body body1 ->
  open_body_wrt_typ body2 (typ_var_f X1) = open_body_wrt_typ body1 (typ_var_f X1) ->
  body2 = body1.
Proof.
unfold open_body_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_body_wrt_typ_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ e2 (typ_var_f X1) = open_exp_wrt_typ e1 (typ_var_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_inj : lngen.

Lemma open_body_wrt_exp_inj :
forall body2 body1 x1,
  x1 `notin` fvar_in_body body2 ->
  x1 `notin` fvar_in_body body1 ->
  open_body_wrt_exp body2 (exp_var_f x1) = open_body_wrt_exp body1 (exp_var_f x1) ->
  body2 = body1.
Proof.
unfold open_body_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_body_wrt_exp_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp e2 (exp_var_f x1) = open_exp_wrt_exp e1 (exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_inj : lngen.

Lemma open_cont_wrt_typ_inj :
forall c2 c1 X1,
  X1 `notin` ftvar_in_cont c2 ->
  X1 `notin` ftvar_in_cont c1 ->
  open_cont_wrt_typ c2 (typ_var_f X1) = open_cont_wrt_typ c1 (typ_var_f X1) ->
  c2 = c1.
Proof.
unfold open_cont_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_cont_wrt_typ_inj : lngen.

Lemma open_contd_wrt_typ_inj :
forall cc2 cc1 X1,
  X1 `notin` ftvar_in_contd cc2 ->
  X1 `notin` ftvar_in_contd cc1 ->
  open_contd_wrt_typ cc2 (typ_var_f X1) = open_contd_wrt_typ cc1 (typ_var_f X1) ->
  cc2 = cc1.
Proof.
unfold open_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_contd_wrt_typ_inj : lngen.

Lemma open_cont_wrt_exp_inj :
forall c2 c1 x1,
  x1 `notin` fvar_in_cont c2 ->
  x1 `notin` fvar_in_cont c1 ->
  open_cont_wrt_exp c2 (exp_var_f x1) = open_cont_wrt_exp c1 (exp_var_f x1) ->
  c2 = c1.
Proof.
unfold open_cont_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_cont_wrt_exp_inj : lngen.

Lemma open_contd_wrt_exp_inj :
forall cc2 cc1 x1,
  x1 `notin` fvar_in_contd cc2 ->
  x1 `notin` fvar_in_contd cc1 ->
  open_contd_wrt_exp cc2 (exp_var_f x1) = open_contd_wrt_exp cc1 (exp_var_f x1) ->
  cc2 = cc1.
Proof.
unfold open_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_contd_wrt_exp_inj : lngen.

Lemma open_dbind_wrt_typ_inj :
forall db2 db1 X1,
  X1 `notin` ftvar_in_dbind db2 ->
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ db2 (typ_var_f X1) = open_dbind_wrt_typ db1 (typ_var_f X1) ->
  db2 = db1.
Proof.
unfold open_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_dbind_wrt_typ_inj : lngen.

Lemma open_work_wrt_typ_inj :
forall w2 w1 X1,
  X1 `notin` ftvar_in_work w2 ->
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ w2 (typ_var_f X1) = open_work_wrt_typ w1 (typ_var_f X1) ->
  w2 = w1.
Proof.
unfold open_work_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_work_wrt_typ_inj : lngen.

Lemma open_work_wrt_exp_inj :
forall w2 w1 x1,
  x1 `notin` fvar_in_work w2 ->
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp w2 (exp_var_f x1) = open_work_wrt_exp w1 (exp_var_f x1) ->
  w2 = w1.
Proof.
unfold open_work_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_work_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_abind_wrt_typ_of_lc_abind_mutual :
(forall ab1,
  lc_abind ab1 ->
  degree_abind_wrt_typ 0 ab1).
Proof.
apply_mutual_ind lc_abind_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_abind_wrt_typ_of_lc_abind :
forall ab1,
  lc_abind ab1 ->
  degree_abind_wrt_typ 0 ab1.
Proof.
pose proof degree_abind_wrt_typ_of_lc_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_typ_of_lc_abind : lngen.

(* begin hide *)

Lemma degree_body_wrt_typ_of_lc_body_degree_exp_wrt_typ_of_lc_exp_mutual :
(forall body1,
  lc_body body1 ->
  degree_body_wrt_typ 0 body1) /\
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_body_lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_body_wrt_typ_of_lc_body :
forall body1,
  lc_body body1 ->
  degree_body_wrt_typ 0 body1.
Proof.
pose proof degree_body_wrt_typ_of_lc_body_degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_typ_of_lc_body : lngen.

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_body_wrt_typ_of_lc_body_degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_body_wrt_exp_of_lc_body_degree_exp_wrt_exp_of_lc_exp_mutual :
(forall body1,
  lc_body body1 ->
  degree_body_wrt_exp 0 body1) /\
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_body_lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_body_wrt_exp_of_lc_body :
forall body1,
  lc_body body1 ->
  degree_body_wrt_exp 0 body1.
Proof.
pose proof degree_body_wrt_exp_of_lc_body_degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_body_wrt_exp_of_lc_body : lngen.

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_body_wrt_exp_of_lc_body_degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_cont_wrt_typ_of_lc_cont_degree_contd_wrt_typ_of_lc_contd_mutual :
(forall c1,
  lc_cont c1 ->
  degree_cont_wrt_typ 0 c1) /\
(forall cc1,
  lc_contd cc1 ->
  degree_contd_wrt_typ 0 cc1).
Proof.
apply_mutual_ind lc_cont_lc_contd_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_cont_wrt_typ_of_lc_cont :
forall c1,
  lc_cont c1 ->
  degree_cont_wrt_typ 0 c1.
Proof.
pose proof degree_cont_wrt_typ_of_lc_cont_degree_contd_wrt_typ_of_lc_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_typ_of_lc_cont : lngen.

Lemma degree_contd_wrt_typ_of_lc_contd :
forall cc1,
  lc_contd cc1 ->
  degree_contd_wrt_typ 0 cc1.
Proof.
pose proof degree_cont_wrt_typ_of_lc_cont_degree_contd_wrt_typ_of_lc_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_of_lc_contd : lngen.

(* begin hide *)

Lemma degree_cont_wrt_exp_of_lc_cont_degree_contd_wrt_exp_of_lc_contd_mutual :
(forall c1,
  lc_cont c1 ->
  degree_cont_wrt_exp 0 c1) /\
(forall cc1,
  lc_contd cc1 ->
  degree_contd_wrt_exp 0 cc1).
Proof.
apply_mutual_ind lc_cont_lc_contd_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_cont_wrt_exp_of_lc_cont :
forall c1,
  lc_cont c1 ->
  degree_cont_wrt_exp 0 c1.
Proof.
pose proof degree_cont_wrt_exp_of_lc_cont_degree_contd_wrt_exp_of_lc_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_cont_wrt_exp_of_lc_cont : lngen.

Lemma degree_contd_wrt_exp_of_lc_contd :
forall cc1,
  lc_contd cc1 ->
  degree_contd_wrt_exp 0 cc1.
Proof.
pose proof degree_cont_wrt_exp_of_lc_cont_degree_contd_wrt_exp_of_lc_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_of_lc_contd : lngen.

(* begin hide *)

Lemma degree_dbind_wrt_typ_of_lc_dbind_mutual :
(forall db1,
  lc_dbind db1 ->
  degree_dbind_wrt_typ 0 db1).
Proof.
apply_mutual_ind lc_dbind_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dbind_wrt_typ_of_lc_dbind :
forall db1,
  lc_dbind db1 ->
  degree_dbind_wrt_typ 0 db1.
Proof.
pose proof degree_dbind_wrt_typ_of_lc_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_of_lc_dbind : lngen.

(* begin hide *)

Lemma degree_work_wrt_typ_of_lc_work_mutual :
(forall w1,
  lc_work w1 ->
  degree_work_wrt_typ 0 w1).
Proof.
apply_mutual_ind lc_work_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_work_wrt_typ_of_lc_work :
forall w1,
  lc_work w1 ->
  degree_work_wrt_typ 0 w1.
Proof.
pose proof degree_work_wrt_typ_of_lc_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_typ_of_lc_work : lngen.

(* begin hide *)

Lemma degree_work_wrt_exp_of_lc_work_mutual :
(forall w1,
  lc_work w1 ->
  degree_work_wrt_exp 0 w1).
Proof.
apply_mutual_ind lc_work_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_work_wrt_exp_of_lc_work :
forall w1,
  lc_work w1 ->
  degree_work_wrt_exp 0 w1.
Proof.
pose proof degree_work_wrt_exp_of_lc_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_work_wrt_exp_of_lc_work : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
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

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_abind_of_degree_size_mutual :
forall i1,
(forall ab1,
  size_abind ab1 = i1 ->
  degree_abind_wrt_typ 0 ab1 ->
  lc_abind ab1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind abind_mutind;
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

Lemma lc_abind_of_degree :
forall ab1,
  degree_abind_wrt_typ 0 ab1 ->
  lc_abind ab1.
Proof.
intros ab1; intros;
pose proof (lc_abind_of_degree_size_mutual (size_abind ab1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_abind_of_degree : lngen.

(* begin hide *)

Lemma lc_body_of_degree_lc_exp_of_degree_size_mutual :
forall i1,
(forall body1,
  size_body body1 = i1 ->
  degree_body_wrt_typ 0 body1 ->
  degree_body_wrt_exp 0 body1 ->
  lc_body body1) /\
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind body_exp_mutind;
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

Lemma lc_body_of_degree :
forall body1,
  degree_body_wrt_typ 0 body1 ->
  degree_body_wrt_exp 0 body1 ->
  lc_body body1.
Proof.
intros body1; intros;
pose proof (lc_body_of_degree_lc_exp_of_degree_size_mutual (size_body body1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_body_of_degree : lngen.

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_body_of_degree_lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_degree : lngen.

(* begin hide *)

Lemma lc_cont_of_degree_lc_contd_of_degree_size_mutual :
forall i1,
(forall c1,
  size_cont c1 = i1 ->
  degree_cont_wrt_typ 0 c1 ->
  degree_cont_wrt_exp 0 c1 ->
  lc_cont c1) /\
(forall cc1,
  size_contd cc1 = i1 ->
  degree_contd_wrt_typ 0 cc1 ->
  degree_contd_wrt_exp 0 cc1 ->
  lc_contd cc1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind cont_contd_mutind;
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

Lemma lc_cont_of_degree :
forall c1,
  degree_cont_wrt_typ 0 c1 ->
  degree_cont_wrt_exp 0 c1 ->
  lc_cont c1.
Proof.
intros c1; intros;
pose proof (lc_cont_of_degree_lc_contd_of_degree_size_mutual (size_cont c1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_cont_of_degree : lngen.

Lemma lc_contd_of_degree :
forall cc1,
  degree_contd_wrt_typ 0 cc1 ->
  degree_contd_wrt_exp 0 cc1 ->
  lc_contd cc1.
Proof.
intros cc1; intros;
pose proof (lc_cont_of_degree_lc_contd_of_degree_size_mutual (size_contd cc1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_contd_of_degree : lngen.

(* begin hide *)

Lemma lc_dbind_of_degree_size_mutual :
forall i1,
(forall db1,
  size_dbind db1 = i1 ->
  degree_dbind_wrt_typ 0 db1 ->
  lc_dbind db1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dbind_mutind;
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

Lemma lc_dbind_of_degree :
forall db1,
  degree_dbind_wrt_typ 0 db1 ->
  lc_dbind db1.
Proof.
intros db1; intros;
pose proof (lc_dbind_of_degree_size_mutual (size_dbind db1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_dbind_of_degree : lngen.

(* begin hide *)

Lemma lc_work_of_degree_size_mutual :
forall i1,
(forall w1,
  size_work w1 = i1 ->
  degree_work_wrt_typ 0 w1 ->
  degree_work_wrt_exp 0 w1 ->
  lc_work w1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind work_mutind;
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

Lemma lc_work_of_degree :
forall w1,
  degree_work_wrt_typ 0 w1 ->
  degree_work_wrt_exp 0 w1 ->
  lc_work w1.
Proof.
intros w1; intros;
pose proof (lc_work_of_degree_size_mutual (size_work w1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_work_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac abind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_abind_wrt_typ_of_lc_abind in J1; clear H
          end).

Ltac body_exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_body_wrt_typ_of_lc_body in J1;
              let J2 := fresh in pose proof H as J2; apply degree_body_wrt_exp_of_lc_body in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Ltac cont_contd_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_cont_wrt_typ_of_lc_cont in J1;
              let J2 := fresh in pose proof H as J2; apply degree_cont_wrt_exp_of_lc_cont in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_contd_wrt_typ_of_lc_contd in J1;
              let J2 := fresh in pose proof H as J2; apply degree_contd_wrt_exp_of_lc_contd in J2; clear H
          end).

Ltac dbind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dbind_wrt_typ_of_lc_dbind in J1; clear H
          end).

Ltac work_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_work_wrt_typ_of_lc_work in J1;
              let J2 := fresh in pose proof H as J2; apply degree_work_wrt_exp_of_lc_work in J2; clear H
          end).

Lemma lc_typ_all_exists :
forall X1 A1,
  lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)) ->
  lc_typ (typ_all A1).
Proof.
intros; typ_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_abs_exists :
forall x1 e1,
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs e1).
Proof.
intros; body_exp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_tabs_exists :
forall X1 body1,
  lc_body (open_body_wrt_typ body1 (typ_var_f X1)) ->
  lc_exp (exp_tabs body1).
Proof.
intros; body_exp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_typ (typ_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_typ_all_exists X1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_exp (exp_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_exp_tabs_exists X1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_abind_wrt_typ :
forall ab1 A1,
  body_abind_wrt_typ ab1 ->
  lc_typ A1 ->
  lc_abind (open_abind_wrt_typ ab1 A1).
Proof.
unfold body_abind_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
abind_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_abind_wrt_typ : lngen.

Lemma lc_body_body_wrt_typ :
forall body1 A1,
  body_body_wrt_typ body1 ->
  lc_typ A1 ->
  lc_body (open_body_wrt_typ body1 A1).
Proof.
unfold body_body_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
body_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_body_wrt_typ : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 A1,
  body_exp_wrt_typ e1 ->
  lc_typ A1 ->
  lc_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold body_exp_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
body_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_typ : lngen.

Lemma lc_body_body_wrt_exp :
forall body1 e1,
  body_body_wrt_exp body1 ->
  lc_exp e1 ->
  lc_body (open_body_wrt_exp body1 e1).
Proof.
unfold body_body_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
body_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_body_wrt_exp : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
body_exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_cont_wrt_typ :
forall c1 A1,
  body_cont_wrt_typ c1 ->
  lc_typ A1 ->
  lc_cont (open_cont_wrt_typ c1 A1).
Proof.
unfold body_cont_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
cont_contd_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_cont_wrt_typ : lngen.

Lemma lc_body_contd_wrt_typ :
forall cc1 A1,
  body_contd_wrt_typ cc1 ->
  lc_typ A1 ->
  lc_contd (open_contd_wrt_typ cc1 A1).
Proof.
unfold body_contd_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
cont_contd_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_contd_wrt_typ : lngen.

Lemma lc_body_cont_wrt_exp :
forall c1 e1,
  body_cont_wrt_exp c1 ->
  lc_exp e1 ->
  lc_cont (open_cont_wrt_exp c1 e1).
Proof.
unfold body_cont_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
cont_contd_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_cont_wrt_exp : lngen.

Lemma lc_body_contd_wrt_exp :
forall cc1 e1,
  body_contd_wrt_exp cc1 ->
  lc_exp e1 ->
  lc_contd (open_contd_wrt_exp cc1 e1).
Proof.
unfold body_contd_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
cont_contd_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_contd_wrt_exp : lngen.

Lemma lc_body_dbind_wrt_typ :
forall db1 A1,
  body_dbind_wrt_typ db1 ->
  lc_typ A1 ->
  lc_dbind (open_dbind_wrt_typ db1 A1).
Proof.
unfold body_dbind_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
dbind_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dbind_wrt_typ : lngen.

Lemma lc_body_work_wrt_typ :
forall w1 A1,
  body_work_wrt_typ w1 ->
  lc_typ A1 ->
  lc_work (open_work_wrt_typ w1 A1).
Proof.
unfold body_work_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
work_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_work_wrt_typ : lngen.

Lemma lc_body_work_wrt_exp :
forall w1 e1,
  body_work_wrt_exp w1 ->
  lc_exp e1 ->
  lc_work (open_work_wrt_exp w1 e1).
Proof.
unfold body_work_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
work_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_work_wrt_exp : lngen.

Lemma lc_body_typ_all_1 :
forall A1,
  lc_typ (typ_all A1) ->
  body_typ_wrt_typ A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_typ_all_1 : lngen.

Lemma lc_body_exp_abs_1 :
forall e1,
  lc_exp (exp_abs e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_abs_1 : lngen.

Lemma lc_body_exp_tabs_1 :
forall body1,
  lc_exp (exp_tabs body1) ->
  body_body_wrt_typ body1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_tabs_1 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_abind_unique_mutual :
(forall ab1 (proof2 proof3 : lc_abind ab1), proof2 = proof3).
Proof.
apply_mutual_ind lc_abind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_abind_unique :
forall ab1 (proof2 proof3 : lc_abind ab1), proof2 = proof3.
Proof.
pose proof lc_abind_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_abind_unique : lngen.

(* begin hide *)

Lemma lc_body_unique_lc_exp_unique_mutual :
(forall body1 (proof2 proof3 : lc_body body1), proof2 = proof3) /\
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_body_lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_body_unique :
forall body1 (proof2 proof3 : lc_body body1), proof2 = proof3.
Proof.
pose proof lc_body_unique_lc_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_body_unique : lngen.

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_body_unique_lc_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_cont_unique_lc_contd_unique_mutual :
(forall c1 (proof2 proof3 : lc_cont c1), proof2 = proof3) /\
(forall cc1 (proof2 proof3 : lc_contd cc1), proof2 = proof3).
Proof.
apply_mutual_ind lc_cont_lc_contd_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_cont_unique :
forall c1 (proof2 proof3 : lc_cont c1), proof2 = proof3.
Proof.
pose proof lc_cont_unique_lc_contd_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_cont_unique : lngen.

Lemma lc_contd_unique :
forall cc1 (proof2 proof3 : lc_contd cc1), proof2 = proof3.
Proof.
pose proof lc_cont_unique_lc_contd_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_contd_unique : lngen.

(* begin hide *)

Lemma lc_dbind_unique_mutual :
(forall db1 (proof2 proof3 : lc_dbind db1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dbind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dbind_unique :
forall db1 (proof2 proof3 : lc_dbind db1), proof2 = proof3.
Proof.
pose proof lc_dbind_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dbind_unique : lngen.

(* begin hide *)

Lemma lc_work_unique_mutual :
(forall w1 (proof2 proof3 : lc_work w1), proof2 = proof3).
Proof.
apply_mutual_ind lc_work_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_work_unique :
forall w1 (proof2 proof3 : lc_work w1), proof2 = proof3.
Proof.
pose proof lc_work_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_work_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_abind_of_lc_set_abind_mutual :
(forall ab1, lc_set_abind ab1 -> lc_abind ab1).
Proof.
apply_mutual_ind lc_set_abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_abind_of_lc_set_abind :
forall ab1, lc_set_abind ab1 -> lc_abind ab1.
Proof.
pose proof lc_abind_of_lc_set_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_abind_of_lc_set_abind : lngen.

(* begin hide *)

Lemma lc_body_of_lc_set_body_lc_exp_of_lc_set_exp_mutual :
(forall body1, lc_set_body body1 -> lc_body body1) /\
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_body_lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_body_of_lc_set_body :
forall body1, lc_set_body body1 -> lc_body body1.
Proof.
pose proof lc_body_of_lc_set_body_lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_body_of_lc_set_body : lngen.

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_body_of_lc_set_body_lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_cont_of_lc_set_cont_lc_contd_of_lc_set_contd_mutual :
(forall c1, lc_set_cont c1 -> lc_cont c1) /\
(forall cc1, lc_set_contd cc1 -> lc_contd cc1).
Proof.
apply_mutual_ind lc_set_cont_lc_set_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_cont_of_lc_set_cont :
forall c1, lc_set_cont c1 -> lc_cont c1.
Proof.
pose proof lc_cont_of_lc_set_cont_lc_contd_of_lc_set_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_cont_of_lc_set_cont : lngen.

Lemma lc_contd_of_lc_set_contd :
forall cc1, lc_set_contd cc1 -> lc_contd cc1.
Proof.
pose proof lc_cont_of_lc_set_cont_lc_contd_of_lc_set_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_contd_of_lc_set_contd : lngen.

(* begin hide *)

Lemma lc_dbind_of_lc_set_dbind_mutual :
(forall db1, lc_set_dbind db1 -> lc_dbind db1).
Proof.
apply_mutual_ind lc_set_dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dbind_of_lc_set_dbind :
forall db1, lc_set_dbind db1 -> lc_dbind db1.
Proof.
pose proof lc_dbind_of_lc_set_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dbind_of_lc_set_dbind : lngen.

(* begin hide *)

Lemma lc_work_of_lc_set_work_mutual :
(forall w1, lc_set_work w1 -> lc_work w1).
Proof.
apply_mutual_ind lc_set_work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_work_of_lc_set_work :
forall w1, lc_set_work w1 -> lc_work w1.
Proof.
pose proof lc_work_of_lc_set_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_work_of_lc_set_work : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
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

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_abind_of_lc_abind_size_mutual :
forall i1,
(forall ab1,
  size_abind ab1 = i1 ->
  lc_abind ab1 ->
  lc_set_abind ab1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind abind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_abind_of_lc_abind];
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

Lemma lc_set_abind_of_lc_abind :
forall ab1,
  lc_abind ab1 ->
  lc_set_abind ab1.
Proof.
intros ab1; intros;
pose proof (lc_set_abind_of_lc_abind_size_mutual (size_abind ab1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_abind_of_lc_abind : lngen.

(* begin hide *)

Lemma lc_set_body_of_lc_body_lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall body1,
  size_body body1 = i1 ->
  lc_body body1 ->
  lc_set_body body1) *
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind body_exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_body_of_lc_body
 | apply lc_set_exp_of_lc_exp
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_body_of_lc_body
 | apply lc_set_exp_of_lc_exp];
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

Lemma lc_set_body_of_lc_body :
forall body1,
  lc_body body1 ->
  lc_set_body body1.
Proof.
intros body1; intros;
pose proof (lc_set_body_of_lc_body_lc_set_exp_of_lc_exp_size_mutual (size_body body1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_body_of_lc_body : lngen.

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_body_of_lc_body_lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_set_cont_of_lc_cont_lc_set_contd_of_lc_contd_size_mutual :
forall i1,
(forall c1,
  size_cont c1 = i1 ->
  lc_cont c1 ->
  lc_set_cont c1) *
(forall cc1,
  size_contd cc1 = i1 ->
  lc_contd cc1 ->
  lc_set_contd cc1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind cont_contd_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_body_of_lc_body
 | apply lc_set_cont_of_lc_cont
 | apply lc_set_contd_of_lc_contd
 | apply lc_set_exp_of_lc_exp
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_body_of_lc_body
 | apply lc_set_cont_of_lc_cont
 | apply lc_set_contd_of_lc_contd
 | apply lc_set_exp_of_lc_exp];
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

Lemma lc_set_cont_of_lc_cont :
forall c1,
  lc_cont c1 ->
  lc_set_cont c1.
Proof.
intros c1; intros;
pose proof (lc_set_cont_of_lc_cont_lc_set_contd_of_lc_contd_size_mutual (size_cont c1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_cont_of_lc_cont : lngen.

Lemma lc_set_contd_of_lc_contd :
forall cc1,
  lc_contd cc1 ->
  lc_set_contd cc1.
Proof.
intros cc1; intros;
pose proof (lc_set_cont_of_lc_cont_lc_set_contd_of_lc_contd_size_mutual (size_contd cc1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_contd_of_lc_contd : lngen.

(* begin hide *)

Lemma lc_set_dbind_of_lc_dbind_size_mutual :
forall i1,
(forall db1,
  size_dbind db1 = i1 ->
  lc_dbind db1 ->
  lc_set_dbind db1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dbind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_dbind_of_lc_dbind];
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

Lemma lc_set_dbind_of_lc_dbind :
forall db1,
  lc_dbind db1 ->
  lc_set_dbind db1.
Proof.
intros db1; intros;
pose proof (lc_set_dbind_of_lc_dbind_size_mutual (size_dbind db1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_dbind_of_lc_dbind : lngen.

(* begin hide *)

Lemma lc_set_work_of_lc_work_size_mutual :
forall i1,
(forall w1,
  size_work w1 = i1 ->
  lc_work w1 ->
  lc_set_work w1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind work_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_body_of_lc_body
 | apply lc_set_cont_of_lc_cont
 | apply lc_set_contd_of_lc_contd
 | apply lc_set_exp_of_lc_exp
 | apply lc_set_work_of_lc_work];
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

Lemma lc_set_work_of_lc_work :
forall w1,
  lc_work w1 ->
  lc_set_work w1.
Proof.
intros w1; intros;
pose proof (lc_set_work_of_lc_work_size_mutual (size_work w1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_work_of_lc_work : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_typ_rec_degree_abind_wrt_typ_mutual :
(forall ab1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  X1 `notin` ftvar_in_abind ab1 ->
  close_abind_wrt_typ_rec n1 X1 ab1 = ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_typ_rec_degree_abind_wrt_typ :
forall ab1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  X1 `notin` ftvar_in_abind ab1 ->
  close_abind_wrt_typ_rec n1 X1 ab1 = ab1.
Proof.
pose proof close_abind_wrt_typ_rec_degree_abind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abind_wrt_typ_rec_degree_abind_wrt_typ : lngen.
#[export] Hint Rewrite close_abind_wrt_typ_rec_degree_abind_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_typ_rec_degree_body_wrt_typ_close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall body1 X1 n1,
  degree_body_wrt_typ n1 body1 ->
  X1 `notin` ftvar_in_body body1 ->
  close_body_wrt_typ_rec n1 X1 body1 = body1) /\
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_typ_rec_degree_body_wrt_typ :
forall body1 X1 n1,
  degree_body_wrt_typ n1 body1 ->
  X1 `notin` ftvar_in_body body1 ->
  close_body_wrt_typ_rec n1 X1 body1 = body1.
Proof.
pose proof close_body_wrt_typ_rec_degree_body_wrt_typ_close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_body_wrt_typ_rec_degree_body_wrt_typ : lngen.
#[export] Hint Rewrite close_body_wrt_typ_rec_degree_body_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_body_wrt_typ_rec_degree_body_wrt_typ_close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_exp_rec_degree_body_wrt_exp_close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall body1 x1 n1,
  degree_body_wrt_exp n1 body1 ->
  x1 `notin` fvar_in_body body1 ->
  close_body_wrt_exp_rec n1 x1 body1 = body1) /\
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_body_wrt_exp_rec_degree_body_wrt_exp :
forall body1 x1 n1,
  degree_body_wrt_exp n1 body1 ->
  x1 `notin` fvar_in_body body1 ->
  close_body_wrt_exp_rec n1 x1 body1 = body1.
Proof.
pose proof close_body_wrt_exp_rec_degree_body_wrt_exp_close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_body_wrt_exp_rec_degree_body_wrt_exp : lngen.
#[export] Hint Rewrite close_body_wrt_exp_rec_degree_body_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_body_wrt_exp_rec_degree_body_wrt_exp_close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_typ_rec_degree_cont_wrt_typ_close_contd_wrt_typ_rec_degree_contd_wrt_typ_mutual :
(forall c1 X1 n1,
  degree_cont_wrt_typ n1 c1 ->
  X1 `notin` ftvar_in_cont c1 ->
  close_cont_wrt_typ_rec n1 X1 c1 = c1) /\
(forall cc1 X1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  X1 `notin` ftvar_in_contd cc1 ->
  close_contd_wrt_typ_rec n1 X1 cc1 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_typ_rec_degree_cont_wrt_typ :
forall c1 X1 n1,
  degree_cont_wrt_typ n1 c1 ->
  X1 `notin` ftvar_in_cont c1 ->
  close_cont_wrt_typ_rec n1 X1 c1 = c1.
Proof.
pose proof close_cont_wrt_typ_rec_degree_cont_wrt_typ_close_contd_wrt_typ_rec_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_cont_wrt_typ_rec_degree_cont_wrt_typ : lngen.
#[export] Hint Rewrite close_cont_wrt_typ_rec_degree_cont_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_degree_contd_wrt_typ :
forall cc1 X1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  X1 `notin` ftvar_in_contd cc1 ->
  close_contd_wrt_typ_rec n1 X1 cc1 = cc1.
Proof.
pose proof close_cont_wrt_typ_rec_degree_cont_wrt_typ_close_contd_wrt_typ_rec_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_rec_degree_contd_wrt_typ : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_rec_degree_contd_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_exp_rec_degree_cont_wrt_exp_close_contd_wrt_exp_rec_degree_contd_wrt_exp_mutual :
(forall c1 x1 n1,
  degree_cont_wrt_exp n1 c1 ->
  x1 `notin` fvar_in_cont c1 ->
  close_cont_wrt_exp_rec n1 x1 c1 = c1) /\
(forall cc1 x1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  x1 `notin` fvar_in_contd cc1 ->
  close_contd_wrt_exp_rec n1 x1 cc1 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_cont_wrt_exp_rec_degree_cont_wrt_exp :
forall c1 x1 n1,
  degree_cont_wrt_exp n1 c1 ->
  x1 `notin` fvar_in_cont c1 ->
  close_cont_wrt_exp_rec n1 x1 c1 = c1.
Proof.
pose proof close_cont_wrt_exp_rec_degree_cont_wrt_exp_close_contd_wrt_exp_rec_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_cont_wrt_exp_rec_degree_cont_wrt_exp : lngen.
#[export] Hint Rewrite close_cont_wrt_exp_rec_degree_cont_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_degree_contd_wrt_exp :
forall cc1 x1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  x1 `notin` fvar_in_contd cc1 ->
  close_contd_wrt_exp_rec n1 x1 cc1 = cc1.
Proof.
pose proof close_cont_wrt_exp_rec_degree_cont_wrt_exp_close_contd_wrt_exp_rec_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_rec_degree_contd_wrt_exp : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_rec_degree_contd_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual :
(forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_degree_dbind_wrt_typ :
forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 db1 = db1.
Proof.
pose proof close_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_rec_degree_dbind_wrt_typ : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_rec_degree_dbind_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_typ_rec_degree_work_wrt_typ_mutual :
(forall w1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  X1 `notin` ftvar_in_work w1 ->
  close_work_wrt_typ_rec n1 X1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_typ_rec_degree_work_wrt_typ :
forall w1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  X1 `notin` ftvar_in_work w1 ->
  close_work_wrt_typ_rec n1 X1 w1 = w1.
Proof.
pose proof close_work_wrt_typ_rec_degree_work_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_work_wrt_typ_rec_degree_work_wrt_typ : lngen.
#[export] Hint Rewrite close_work_wrt_typ_rec_degree_work_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_exp_rec_degree_work_wrt_exp_mutual :
(forall w1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  x1 `notin` fvar_in_work w1 ->
  close_work_wrt_exp_rec n1 x1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_work_wrt_exp_rec_degree_work_wrt_exp :
forall w1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  x1 `notin` fvar_in_work w1 ->
  close_work_wrt_exp_rec n1 x1 w1 = w1.
Proof.
pose proof close_work_wrt_exp_rec_degree_work_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_work_wrt_exp_rec_degree_work_wrt_exp : lngen.
#[export] Hint Rewrite close_work_wrt_exp_rec_degree_work_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_abind_wrt_typ_lc_abind :
forall ab1 X1,
  lc_abind ab1 ->
  X1 `notin` ftvar_in_abind ab1 ->
  close_abind_wrt_typ X1 ab1 = ab1.
Proof.
unfold close_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_abind_wrt_typ_lc_abind : lngen.
#[export] Hint Rewrite close_abind_wrt_typ_lc_abind using solve [auto] : lngen.

Lemma close_body_wrt_typ_lc_body :
forall body1 X1,
  lc_body body1 ->
  X1 `notin` ftvar_in_body body1 ->
  close_body_wrt_typ X1 body1 = body1.
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_body_wrt_typ_lc_body : lngen.
#[export] Hint Rewrite close_body_wrt_typ_lc_body using solve [auto] : lngen.

Lemma close_exp_wrt_typ_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma close_body_wrt_exp_lc_body :
forall body1 x1,
  lc_body body1 ->
  x1 `notin` fvar_in_body body1 ->
  close_body_wrt_exp x1 body1 = body1.
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_body_wrt_exp_lc_body : lngen.
#[export] Hint Rewrite close_body_wrt_exp_lc_body using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma close_cont_wrt_typ_lc_cont :
forall c1 X1,
  lc_cont c1 ->
  X1 `notin` ftvar_in_cont c1 ->
  close_cont_wrt_typ X1 c1 = c1.
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_cont_wrt_typ_lc_cont : lngen.
#[export] Hint Rewrite close_cont_wrt_typ_lc_cont using solve [auto] : lngen.

Lemma close_contd_wrt_typ_lc_contd :
forall cc1 X1,
  lc_contd cc1 ->
  X1 `notin` ftvar_in_contd cc1 ->
  close_contd_wrt_typ X1 cc1 = cc1.
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_lc_contd : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_lc_contd using solve [auto] : lngen.

Lemma close_cont_wrt_exp_lc_cont :
forall c1 x1,
  lc_cont c1 ->
  x1 `notin` fvar_in_cont c1 ->
  close_cont_wrt_exp x1 c1 = c1.
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_cont_wrt_exp_lc_cont : lngen.
#[export] Hint Rewrite close_cont_wrt_exp_lc_cont using solve [auto] : lngen.

Lemma close_contd_wrt_exp_lc_contd :
forall cc1 x1,
  lc_contd cc1 ->
  x1 `notin` fvar_in_contd cc1 ->
  close_contd_wrt_exp x1 cc1 = cc1.
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_lc_contd : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_lc_contd using solve [auto] : lngen.

Lemma close_dbind_wrt_typ_lc_dbind :
forall db1 X1,
  lc_dbind db1 ->
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ X1 db1 = db1.
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_lc_dbind : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_lc_dbind using solve [auto] : lngen.

Lemma close_work_wrt_typ_lc_work :
forall w1 X1,
  lc_work w1 ->
  X1 `notin` ftvar_in_work w1 ->
  close_work_wrt_typ X1 w1 = w1.
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_work_wrt_typ_lc_work : lngen.
#[export] Hint Rewrite close_work_wrt_typ_lc_work using solve [auto] : lngen.

Lemma close_work_wrt_exp_lc_work :
forall w1 x1,
  lc_work w1 ->
  x1 `notin` fvar_in_work w1 ->
  close_work_wrt_exp x1 w1 = w1.
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_work_wrt_exp_lc_work : lngen.
#[export] Hint Rewrite close_work_wrt_exp_lc_work using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_typ_rec_degree_abind_wrt_typ_mutual :
(forall ab1 A1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  open_abind_wrt_typ_rec n1 A1 ab1 = ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_typ_rec_degree_abind_wrt_typ :
forall ab1 A1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  open_abind_wrt_typ_rec n1 A1 ab1 = ab1.
Proof.
pose proof open_abind_wrt_typ_rec_degree_abind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abind_wrt_typ_rec_degree_abind_wrt_typ : lngen.
#[export] Hint Rewrite open_abind_wrt_typ_rec_degree_abind_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_typ_rec_degree_body_wrt_typ_open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall body1 A1 n1,
  degree_body_wrt_typ n1 body1 ->
  open_body_wrt_typ_rec n1 A1 body1 = body1) /\
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_typ_rec_degree_body_wrt_typ :
forall body1 A1 n1,
  degree_body_wrt_typ n1 body1 ->
  open_body_wrt_typ_rec n1 A1 body1 = body1.
Proof.
pose proof open_body_wrt_typ_rec_degree_body_wrt_typ_open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_body_wrt_typ_rec_degree_body_wrt_typ : lngen.
#[export] Hint Rewrite open_body_wrt_typ_rec_degree_body_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1.
Proof.
pose proof open_body_wrt_typ_rec_degree_body_wrt_typ_open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_exp_rec_degree_body_wrt_exp_open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall body1 e1 n1,
  degree_body_wrt_exp n1 body1 ->
  open_body_wrt_exp_rec n1 e1 body1 = body1) /\
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_body_wrt_exp_rec_degree_body_wrt_exp :
forall body1 e1 n1,
  degree_body_wrt_exp n1 body1 ->
  open_body_wrt_exp_rec n1 e1 body1 = body1.
Proof.
pose proof open_body_wrt_exp_rec_degree_body_wrt_exp_open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_body_wrt_exp_rec_degree_body_wrt_exp : lngen.
#[export] Hint Rewrite open_body_wrt_exp_rec_degree_body_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_body_wrt_exp_rec_degree_body_wrt_exp_open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_typ_rec_degree_cont_wrt_typ_open_contd_wrt_typ_rec_degree_contd_wrt_typ_mutual :
(forall c1 A1 n1,
  degree_cont_wrt_typ n1 c1 ->
  open_cont_wrt_typ_rec n1 A1 c1 = c1) /\
(forall cc1 A1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  open_contd_wrt_typ_rec n1 A1 cc1 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_typ_rec_degree_cont_wrt_typ :
forall c1 A1 n1,
  degree_cont_wrt_typ n1 c1 ->
  open_cont_wrt_typ_rec n1 A1 c1 = c1.
Proof.
pose proof open_cont_wrt_typ_rec_degree_cont_wrt_typ_open_contd_wrt_typ_rec_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_cont_wrt_typ_rec_degree_cont_wrt_typ : lngen.
#[export] Hint Rewrite open_cont_wrt_typ_rec_degree_cont_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_degree_contd_wrt_typ :
forall cc1 A1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  open_contd_wrt_typ_rec n1 A1 cc1 = cc1.
Proof.
pose proof open_cont_wrt_typ_rec_degree_cont_wrt_typ_open_contd_wrt_typ_rec_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_rec_degree_contd_wrt_typ : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_rec_degree_contd_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_exp_rec_degree_cont_wrt_exp_open_contd_wrt_exp_rec_degree_contd_wrt_exp_mutual :
(forall c1 e1 n1,
  degree_cont_wrt_exp n1 c1 ->
  open_cont_wrt_exp_rec n1 e1 c1 = c1) /\
(forall cc1 e1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  open_contd_wrt_exp_rec n1 e1 cc1 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_cont_wrt_exp_rec_degree_cont_wrt_exp :
forall c1 e1 n1,
  degree_cont_wrt_exp n1 c1 ->
  open_cont_wrt_exp_rec n1 e1 c1 = c1.
Proof.
pose proof open_cont_wrt_exp_rec_degree_cont_wrt_exp_open_contd_wrt_exp_rec_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_cont_wrt_exp_rec_degree_cont_wrt_exp : lngen.
#[export] Hint Rewrite open_cont_wrt_exp_rec_degree_cont_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_degree_contd_wrt_exp :
forall cc1 e1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  open_contd_wrt_exp_rec n1 e1 cc1 = cc1.
Proof.
pose proof open_cont_wrt_exp_rec_degree_cont_wrt_exp_open_contd_wrt_exp_rec_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_rec_degree_contd_wrt_exp : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_rec_degree_contd_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual :
(forall db1 A1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_degree_dbind_wrt_typ :
forall db1 A1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = db1.
Proof.
pose proof open_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_rec_degree_dbind_wrt_typ : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_rec_degree_dbind_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_typ_rec_degree_work_wrt_typ_mutual :
(forall w1 A1 n1,
  degree_work_wrt_typ n1 w1 ->
  open_work_wrt_typ_rec n1 A1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_typ_rec_degree_work_wrt_typ :
forall w1 A1 n1,
  degree_work_wrt_typ n1 w1 ->
  open_work_wrt_typ_rec n1 A1 w1 = w1.
Proof.
pose proof open_work_wrt_typ_rec_degree_work_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_work_wrt_typ_rec_degree_work_wrt_typ : lngen.
#[export] Hint Rewrite open_work_wrt_typ_rec_degree_work_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_exp_rec_degree_work_wrt_exp_mutual :
(forall w1 e1 n1,
  degree_work_wrt_exp n1 w1 ->
  open_work_wrt_exp_rec n1 e1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_work_wrt_exp_rec_degree_work_wrt_exp :
forall w1 e1 n1,
  degree_work_wrt_exp n1 w1 ->
  open_work_wrt_exp_rec n1 e1 w1 = w1.
Proof.
pose proof open_work_wrt_exp_rec_degree_work_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_work_wrt_exp_rec_degree_work_wrt_exp : lngen.
#[export] Hint Rewrite open_work_wrt_exp_rec_degree_work_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_abind_wrt_typ_lc_abind :
forall ab1 A1,
  lc_abind ab1 ->
  open_abind_wrt_typ ab1 A1 = ab1.
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_abind_wrt_typ_lc_abind : lngen.
#[export] Hint Rewrite open_abind_wrt_typ_lc_abind using solve [auto] : lngen.

Lemma open_body_wrt_typ_lc_body :
forall body1 A1,
  lc_body body1 ->
  open_body_wrt_typ body1 A1 = body1.
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_body_wrt_typ_lc_body : lngen.
#[export] Hint Rewrite open_body_wrt_typ_lc_body using solve [auto] : lngen.

Lemma open_exp_wrt_typ_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 A1 = e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma open_body_wrt_exp_lc_body :
forall body1 e1,
  lc_body body1 ->
  open_body_wrt_exp body1 e1 = body1.
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_body_wrt_exp_lc_body : lngen.
#[export] Hint Rewrite open_body_wrt_exp_lc_body using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma open_cont_wrt_typ_lc_cont :
forall c1 A1,
  lc_cont c1 ->
  open_cont_wrt_typ c1 A1 = c1.
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_cont_wrt_typ_lc_cont : lngen.
#[export] Hint Rewrite open_cont_wrt_typ_lc_cont using solve [auto] : lngen.

Lemma open_contd_wrt_typ_lc_contd :
forall cc1 A1,
  lc_contd cc1 ->
  open_contd_wrt_typ cc1 A1 = cc1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_lc_contd : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_lc_contd using solve [auto] : lngen.

Lemma open_cont_wrt_exp_lc_cont :
forall c1 e1,
  lc_cont c1 ->
  open_cont_wrt_exp c1 e1 = c1.
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_cont_wrt_exp_lc_cont : lngen.
#[export] Hint Rewrite open_cont_wrt_exp_lc_cont using solve [auto] : lngen.

Lemma open_contd_wrt_exp_lc_contd :
forall cc1 e1,
  lc_contd cc1 ->
  open_contd_wrt_exp cc1 e1 = cc1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_lc_contd : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_lc_contd using solve [auto] : lngen.

Lemma open_dbind_wrt_typ_lc_dbind :
forall db1 A1,
  lc_dbind db1 ->
  open_dbind_wrt_typ db1 A1 = db1.
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_lc_dbind : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_lc_dbind using solve [auto] : lngen.

Lemma open_work_wrt_typ_lc_work :
forall w1 A1,
  lc_work w1 ->
  open_work_wrt_typ w1 A1 = w1.
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_work_wrt_typ_lc_work : lngen.
#[export] Hint Rewrite open_work_wrt_typ_lc_work using solve [auto] : lngen.

Lemma open_work_wrt_exp_lc_work :
forall w1 e1,
  lc_work w1 ->
  open_work_wrt_exp w1 e1 = w1.
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_work_wrt_exp_lc_work : lngen.
#[export] Hint Rewrite open_work_wrt_exp_lc_work using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  ftvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  ftvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_abind_close_abind_wrt_typ_rec_mutual :
(forall ab1 X1 n1,
  ftvar_in_abind (close_abind_wrt_typ_rec n1 X1 ab1) [=] remove X1 (ftvar_in_abind ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_abind_close_abind_wrt_typ_rec :
forall ab1 X1 n1,
  ftvar_in_abind (close_abind_wrt_typ_rec n1 X1 ab1) [=] remove X1 (ftvar_in_abind ab1).
Proof.
pose proof ftvar_in_abind_close_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_close_abind_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_abind_close_abind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_close_body_wrt_typ_rec_ftvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1,
  ftvar_in_body (close_body_wrt_typ_rec n1 X1 body1) [=] remove X1 (ftvar_in_body body1)) /\
(forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_close_body_wrt_typ_rec :
forall body1 X1 n1,
  ftvar_in_body (close_body_wrt_typ_rec n1 X1 body1) [=] remove X1 (ftvar_in_body body1).
Proof.
pose proof ftvar_in_body_close_body_wrt_typ_rec_ftvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_close_body_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_body_close_body_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_body_close_body_wrt_typ_rec_ftvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_close_body_wrt_exp_rec_ftvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1,
  ftvar_in_body (close_body_wrt_exp_rec n1 x1 body1) [=] ftvar_in_body body1) /\
(forall e1 x1 n1,
  ftvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_close_body_wrt_exp_rec :
forall body1 x1 n1,
  ftvar_in_body (close_body_wrt_exp_rec n1 x1 body1) [=] ftvar_in_body body1.
Proof.
pose proof ftvar_in_body_close_body_wrt_exp_rec_ftvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_close_body_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_body_close_body_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  ftvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_body_close_body_wrt_exp_rec_ftvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_close_body_wrt_typ_rec_fvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall body1 X1 n1,
  fvar_in_body (close_body_wrt_typ_rec n1 X1 body1) [=] fvar_in_body body1) /\
(forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_close_body_wrt_typ_rec :
forall body1 X1 n1,
  fvar_in_body (close_body_wrt_typ_rec n1 X1 body1) [=] fvar_in_body body1.
Proof.
pose proof fvar_in_body_close_body_wrt_typ_rec_fvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_close_body_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_body_close_body_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_body_close_body_wrt_typ_rec_fvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_close_body_wrt_exp_rec_fvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall body1 x1 n1,
  fvar_in_body (close_body_wrt_exp_rec n1 x1 body1) [=] remove x1 (fvar_in_body body1)) /\
(forall e1 x1 n1,
  fvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fvar_in_exp e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_close_body_wrt_exp_rec :
forall body1 x1 n1,
  fvar_in_body (close_body_wrt_exp_rec n1 x1 body1) [=] remove x1 (fvar_in_body body1).
Proof.
pose proof fvar_in_body_close_body_wrt_exp_rec_fvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_close_body_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_body_close_body_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
pose proof fvar_in_body_close_body_wrt_exp_rec_fvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_close_cont_wrt_typ_rec_ftvar_in_contd_close_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  ftvar_in_cont (close_cont_wrt_typ_rec n1 X1 c1) [=] remove X1 (ftvar_in_cont c1)) /\
(forall cc1 X1 n1,
  ftvar_in_contd (close_contd_wrt_typ_rec n1 X1 cc1) [=] remove X1 (ftvar_in_contd cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_close_cont_wrt_typ_rec :
forall c1 X1 n1,
  ftvar_in_cont (close_cont_wrt_typ_rec n1 X1 c1) [=] remove X1 (ftvar_in_cont c1).
Proof.
pose proof ftvar_in_cont_close_cont_wrt_typ_rec_ftvar_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_close_cont_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_cont_close_cont_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_close_contd_wrt_typ_rec :
forall cc1 X1 n1,
  ftvar_in_contd (close_contd_wrt_typ_rec n1 X1 cc1) [=] remove X1 (ftvar_in_contd cc1).
Proof.
pose proof ftvar_in_cont_close_cont_wrt_typ_rec_ftvar_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_close_cont_wrt_exp_rec_ftvar_in_contd_close_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1,
  ftvar_in_cont (close_cont_wrt_exp_rec n1 x1 c1) [=] ftvar_in_cont c1) /\
(forall cc1 x1 n1,
  ftvar_in_contd (close_contd_wrt_exp_rec n1 x1 cc1) [=] ftvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_close_cont_wrt_exp_rec :
forall c1 x1 n1,
  ftvar_in_cont (close_cont_wrt_exp_rec n1 x1 c1) [=] ftvar_in_cont c1.
Proof.
pose proof ftvar_in_cont_close_cont_wrt_exp_rec_ftvar_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_close_cont_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_cont_close_cont_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_close_contd_wrt_exp_rec :
forall cc1 x1 n1,
  ftvar_in_contd (close_contd_wrt_exp_rec n1 x1 cc1) [=] ftvar_in_contd cc1.
Proof.
pose proof ftvar_in_cont_close_cont_wrt_exp_rec_ftvar_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_close_cont_wrt_typ_rec_fvar_in_contd_close_contd_wrt_typ_rec_mutual :
(forall c1 X1 n1,
  fvar_in_cont (close_cont_wrt_typ_rec n1 X1 c1) [=] fvar_in_cont c1) /\
(forall cc1 X1 n1,
  fvar_in_contd (close_contd_wrt_typ_rec n1 X1 cc1) [=] fvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_close_cont_wrt_typ_rec :
forall c1 X1 n1,
  fvar_in_cont (close_cont_wrt_typ_rec n1 X1 c1) [=] fvar_in_cont c1.
Proof.
pose proof fvar_in_cont_close_cont_wrt_typ_rec_fvar_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_close_cont_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_cont_close_cont_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_close_contd_wrt_typ_rec :
forall cc1 X1 n1,
  fvar_in_contd (close_contd_wrt_typ_rec n1 X1 cc1) [=] fvar_in_contd cc1.
Proof.
pose proof fvar_in_cont_close_cont_wrt_typ_rec_fvar_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_close_cont_wrt_exp_rec_fvar_in_contd_close_contd_wrt_exp_rec_mutual :
(forall c1 x1 n1,
  fvar_in_cont (close_cont_wrt_exp_rec n1 x1 c1) [=] remove x1 (fvar_in_cont c1)) /\
(forall cc1 x1 n1,
  fvar_in_contd (close_contd_wrt_exp_rec n1 x1 cc1) [=] remove x1 (fvar_in_contd cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_close_cont_wrt_exp_rec :
forall c1 x1 n1,
  fvar_in_cont (close_cont_wrt_exp_rec n1 x1 c1) [=] remove x1 (fvar_in_cont c1).
Proof.
pose proof fvar_in_cont_close_cont_wrt_exp_rec_fvar_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_close_cont_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_cont_close_cont_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_close_contd_wrt_exp_rec :
forall cc1 x1 n1,
  fvar_in_contd (close_contd_wrt_exp_rec n1 x1 cc1) [=] remove x1 (fvar_in_contd cc1).
Proof.
pose proof fvar_in_cont_close_cont_wrt_exp_rec_fvar_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  ftvar_in_dbind (close_dbind_wrt_typ_rec n1 X1 db1) [=] remove X1 (ftvar_in_dbind db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  ftvar_in_dbind (close_dbind_wrt_typ_rec n1 X1 db1) [=] remove X1 (ftvar_in_dbind db1).
Proof.
pose proof ftvar_in_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_close_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_dbind_close_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_close_work_wrt_typ_rec_mutual :
(forall w1 X1 n1,
  ftvar_in_work (close_work_wrt_typ_rec n1 X1 w1) [=] remove X1 (ftvar_in_work w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_close_work_wrt_typ_rec :
forall w1 X1 n1,
  ftvar_in_work (close_work_wrt_typ_rec n1 X1 w1) [=] remove X1 (ftvar_in_work w1).
Proof.
pose proof ftvar_in_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_close_work_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_work_close_work_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_close_work_wrt_exp_rec_mutual :
(forall w1 x1 n1,
  ftvar_in_work (close_work_wrt_exp_rec n1 x1 w1) [=] ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_close_work_wrt_exp_rec :
forall w1 x1 n1,
  ftvar_in_work (close_work_wrt_exp_rec n1 x1 w1) [=] ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_close_work_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_work_close_work_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_close_work_wrt_typ_rec_mutual :
(forall w1 X1 n1,
  fvar_in_work (close_work_wrt_typ_rec n1 X1 w1) [=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_close_work_wrt_typ_rec :
forall w1 X1 n1,
  fvar_in_work (close_work_wrt_typ_rec n1 X1 w1) [=] fvar_in_work w1.
Proof.
pose proof fvar_in_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_close_work_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_work_close_work_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_close_work_wrt_exp_rec_mutual :
(forall w1 x1 n1,
  fvar_in_work (close_work_wrt_exp_rec n1 x1 w1) [=] remove x1 (fvar_in_work w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_close_work_wrt_exp_rec :
forall w1 x1 n1,
  fvar_in_work (close_work_wrt_exp_rec n1 x1 w1) [=] remove x1 (fvar_in_work w1).
Proof.
pose proof fvar_in_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_close_work_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_work_close_work_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ :
forall A1 X1,
  ftvar_in_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (ftvar_in_typ A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_abind_close_abind_wrt_typ :
forall ab1 X1,
  ftvar_in_abind (close_abind_wrt_typ X1 ab1) [=] remove X1 (ftvar_in_abind ab1).
Proof.
unfold close_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_abind_close_abind_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_abind_close_abind_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_body_close_body_wrt_typ :
forall body1 X1,
  ftvar_in_body (close_body_wrt_typ X1 body1) [=] remove X1 (ftvar_in_body body1).
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_body_close_body_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_body_close_body_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  ftvar_in_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_body_close_body_wrt_exp :
forall body1 x1,
  ftvar_in_body (close_body_wrt_exp x1 body1) [=] ftvar_in_body body1.
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_body_close_body_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_body_close_body_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  ftvar_in_exp (close_exp_wrt_exp x1 e1) [=] ftvar_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_body_close_body_wrt_typ :
forall body1 X1,
  fvar_in_body (close_body_wrt_typ X1 body1) [=] fvar_in_body body1.
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_body_close_body_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_body_close_body_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  fvar_in_exp (close_exp_wrt_typ X1 e1) [=] fvar_in_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_body_close_body_wrt_exp :
forall body1 x1,
  fvar_in_body (close_body_wrt_exp x1 body1) [=] remove x1 (fvar_in_body body1).
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_body_close_body_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_body_close_body_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fvar_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_cont_close_cont_wrt_typ :
forall c1 X1,
  ftvar_in_cont (close_cont_wrt_typ X1 c1) [=] remove X1 (ftvar_in_cont c1).
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_cont_close_cont_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_cont_close_cont_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_contd_close_contd_wrt_typ :
forall cc1 X1,
  ftvar_in_contd (close_contd_wrt_typ X1 cc1) [=] remove X1 (ftvar_in_contd cc1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_cont_close_cont_wrt_exp :
forall c1 x1,
  ftvar_in_cont (close_cont_wrt_exp x1 c1) [=] ftvar_in_cont c1.
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_cont_close_cont_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_cont_close_cont_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_contd_close_contd_wrt_exp :
forall cc1 x1,
  ftvar_in_contd (close_contd_wrt_exp x1 cc1) [=] ftvar_in_contd cc1.
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_cont_close_cont_wrt_typ :
forall c1 X1,
  fvar_in_cont (close_cont_wrt_typ X1 c1) [=] fvar_in_cont c1.
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_cont_close_cont_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_cont_close_cont_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_contd_close_contd_wrt_typ :
forall cc1 X1,
  fvar_in_contd (close_contd_wrt_typ X1 cc1) [=] fvar_in_contd cc1.
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_cont_close_cont_wrt_exp :
forall c1 x1,
  fvar_in_cont (close_cont_wrt_exp x1 c1) [=] remove x1 (fvar_in_cont c1).
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_cont_close_cont_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_cont_close_cont_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_contd_close_contd_wrt_exp :
forall cc1 x1,
  fvar_in_contd (close_contd_wrt_exp x1 cc1) [=] remove x1 (fvar_in_contd cc1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_dbind_close_dbind_wrt_typ :
forall db1 X1,
  ftvar_in_dbind (close_dbind_wrt_typ X1 db1) [=] remove X1 (ftvar_in_dbind db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_dbind_close_dbind_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_dbind_close_dbind_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_work_close_work_wrt_typ :
forall w1 X1,
  ftvar_in_work (close_work_wrt_typ X1 w1) [=] remove X1 (ftvar_in_work w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_work_close_work_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_work_close_work_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_work_close_work_wrt_exp :
forall w1 x1,
  ftvar_in_work (close_work_wrt_exp x1 w1) [=] ftvar_in_work w1.
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_work_close_work_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_work_close_work_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_work_close_work_wrt_typ :
forall w1 X1,
  fvar_in_work (close_work_wrt_typ X1 w1) [=] fvar_in_work w1.
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_work_close_work_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_work_close_work_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_work_close_work_wrt_exp :
forall w1 x1,
  fvar_in_work (close_work_wrt_exp x1 w1) [=] remove x1 (fvar_in_work w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_work_close_work_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_work_close_work_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof ftvar_in_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_abind_open_abind_wrt_typ_rec_lower_mutual :
(forall ab1 A1 n1,
  ftvar_in_abind ab1 [<=] ftvar_in_abind (open_abind_wrt_typ_rec n1 A1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_abind_open_abind_wrt_typ_rec_lower :
forall ab1 A1 n1,
  ftvar_in_abind ab1 [<=] ftvar_in_abind (open_abind_wrt_typ_rec n1 A1 ab1).
Proof.
pose proof ftvar_in_abind_open_abind_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_open_abind_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_typ_rec_lower_ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall body1 A1 n1,
  ftvar_in_body body1 [<=] ftvar_in_body (open_body_wrt_typ_rec n1 A1 body1)) /\
(forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_typ_rec_lower :
forall body1 A1 n1,
  ftvar_in_body body1 [<=] ftvar_in_body (open_body_wrt_typ_rec n1 A1 body1).
Proof.
pose proof ftvar_in_body_open_body_wrt_typ_rec_lower_ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof ftvar_in_body_open_body_wrt_typ_rec_lower_ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_exp_rec_lower_ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall body1 e1 n1,
  ftvar_in_body body1 [<=] ftvar_in_body (open_body_wrt_exp_rec n1 e1 body1)) /\
(forall e1 e2 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_exp_rec_lower :
forall body1 e1 n1,
  ftvar_in_body body1 [<=] ftvar_in_body (open_body_wrt_exp_rec n1 e1 body1).
Proof.
pose proof ftvar_in_body_open_body_wrt_exp_rec_lower_ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof ftvar_in_body_open_body_wrt_exp_rec_lower_ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_typ_rec_lower_fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall body1 A1 n1,
  fvar_in_body body1 [<=] fvar_in_body (open_body_wrt_typ_rec n1 A1 body1)) /\
(forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_typ_rec_lower :
forall body1 A1 n1,
  fvar_in_body body1 [<=] fvar_in_body (open_body_wrt_typ_rec n1 A1 body1).
Proof.
pose proof fvar_in_body_open_body_wrt_typ_rec_lower_fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof fvar_in_body_open_body_wrt_typ_rec_lower_fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_exp_rec_lower_fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall body1 e1 n1,
  fvar_in_body body1 [<=] fvar_in_body (open_body_wrt_exp_rec n1 e1 body1)) /\
(forall e1 e2 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_exp_rec_lower :
forall body1 e1 n1,
  fvar_in_body body1 [<=] fvar_in_body (open_body_wrt_exp_rec n1 e1 body1).
Proof.
pose proof fvar_in_body_open_body_wrt_exp_rec_lower_fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fvar_in_body_open_body_wrt_exp_rec_lower_fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_typ_rec_lower_ftvar_in_contd_open_contd_wrt_typ_rec_lower_mutual :
(forall c1 A1 n1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1)) /\
(forall cc1 A1 n1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_typ_rec_lower :
forall c1 A1 n1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1).
Proof.
pose proof ftvar_in_cont_open_cont_wrt_typ_rec_lower_ftvar_in_contd_open_contd_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_typ_rec_lower :
forall cc1 A1 n1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1).
Proof.
pose proof ftvar_in_cont_open_cont_wrt_typ_rec_lower_ftvar_in_contd_open_contd_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_exp_rec_lower_ftvar_in_contd_open_contd_wrt_exp_rec_lower_mutual :
(forall c1 e1 n1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1)) /\
(forall cc1 e1 n1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_exp_rec_lower :
forall c1 e1 n1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1).
Proof.
pose proof ftvar_in_cont_open_cont_wrt_exp_rec_lower_ftvar_in_contd_open_contd_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_exp_rec_lower :
forall cc1 e1 n1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1).
Proof.
pose proof ftvar_in_cont_open_cont_wrt_exp_rec_lower_ftvar_in_contd_open_contd_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_typ_rec_lower_fvar_in_contd_open_contd_wrt_typ_rec_lower_mutual :
(forall c1 A1 n1,
  fvar_in_cont c1 [<=] fvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1)) /\
(forall cc1 A1 n1,
  fvar_in_contd cc1 [<=] fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_typ_rec_lower :
forall c1 A1 n1,
  fvar_in_cont c1 [<=] fvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1).
Proof.
pose proof fvar_in_cont_open_cont_wrt_typ_rec_lower_fvar_in_contd_open_contd_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_typ_rec_lower :
forall cc1 A1 n1,
  fvar_in_contd cc1 [<=] fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1).
Proof.
pose proof fvar_in_cont_open_cont_wrt_typ_rec_lower_fvar_in_contd_open_contd_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_exp_rec_lower_fvar_in_contd_open_contd_wrt_exp_rec_lower_mutual :
(forall c1 e1 n1,
  fvar_in_cont c1 [<=] fvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1)) /\
(forall cc1 e1 n1,
  fvar_in_contd cc1 [<=] fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_exp_rec_lower :
forall c1 e1 n1,
  fvar_in_cont c1 [<=] fvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1).
Proof.
pose proof fvar_in_cont_open_cont_wrt_exp_rec_lower_fvar_in_contd_open_contd_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_exp_rec_lower :
forall cc1 e1 n1,
  fvar_in_contd cc1 [<=] fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1).
Proof.
pose proof fvar_in_cont_open_cont_wrt_exp_rec_lower_fvar_in_contd_open_contd_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_lower_mutual :
(forall db1 A1 n1,
  ftvar_in_dbind db1 [<=] ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_lower :
forall db1 A1 n1,
  ftvar_in_dbind db1 [<=] ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1).
Proof.
pose proof ftvar_in_dbind_open_dbind_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_typ_rec_lower_mutual :
(forall w1 A1 n1,
  ftvar_in_work w1 [<=] ftvar_in_work (open_work_wrt_typ_rec n1 A1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_typ_rec_lower :
forall w1 A1 n1,
  ftvar_in_work w1 [<=] ftvar_in_work (open_work_wrt_typ_rec n1 A1 w1).
Proof.
pose proof ftvar_in_work_open_work_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_exp_rec_lower_mutual :
(forall w1 e1 n1,
  ftvar_in_work w1 [<=] ftvar_in_work (open_work_wrt_exp_rec n1 e1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_exp_rec_lower :
forall w1 e1 n1,
  ftvar_in_work w1 [<=] ftvar_in_work (open_work_wrt_exp_rec n1 e1 w1).
Proof.
pose proof ftvar_in_work_open_work_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_typ_rec_lower_mutual :
(forall w1 A1 n1,
  fvar_in_work w1 [<=] fvar_in_work (open_work_wrt_typ_rec n1 A1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_typ_rec_lower :
forall w1 A1 n1,
  fvar_in_work w1 [<=] fvar_in_work (open_work_wrt_typ_rec n1 A1 w1).
Proof.
pose proof fvar_in_work_open_work_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_exp_rec_lower_mutual :
(forall w1 e1 n1,
  fvar_in_work w1 [<=] fvar_in_work (open_work_wrt_exp_rec n1 e1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_exp_rec_lower :
forall w1 e1 n1,
  fvar_in_work w1 [<=] fvar_in_work (open_work_wrt_exp_rec n1 e1 w1).
Proof.
pose proof fvar_in_work_open_work_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_lower : lngen.

Lemma ftvar_in_abind_open_abind_wrt_typ_lower :
forall ab1 A1,
  ftvar_in_abind ab1 [<=] ftvar_in_abind (open_abind_wrt_typ ab1 A1).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_abind_open_abind_wrt_typ_lower : lngen.

Lemma ftvar_in_body_open_body_wrt_typ_lower :
forall body1 A1,
  ftvar_in_body body1 [<=] ftvar_in_body (open_body_wrt_typ body1 A1).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_typ_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma ftvar_in_body_open_body_wrt_exp_lower :
forall body1 e1,
  ftvar_in_body body1 [<=] ftvar_in_body (open_body_wrt_exp body1 e1).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_exp_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fvar_in_body_open_body_wrt_typ_lower :
forall body1 A1,
  fvar_in_body body1 [<=] fvar_in_body (open_body_wrt_typ body1 A1).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_typ_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma fvar_in_body_open_body_wrt_exp_lower :
forall body1 e1,
  fvar_in_body body1 [<=] fvar_in_body (open_body_wrt_exp body1 e1).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_exp_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma ftvar_in_cont_open_cont_wrt_typ_lower :
forall c1 A1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (open_cont_wrt_typ c1 A1).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_typ_lower : lngen.

Lemma ftvar_in_contd_open_contd_wrt_typ_lower :
forall cc1 A1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (open_contd_wrt_typ cc1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_lower : lngen.

Lemma ftvar_in_cont_open_cont_wrt_exp_lower :
forall c1 e1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (open_cont_wrt_exp c1 e1).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_exp_lower : lngen.

Lemma ftvar_in_contd_open_contd_wrt_exp_lower :
forall cc1 e1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (open_contd_wrt_exp cc1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_lower : lngen.

Lemma fvar_in_cont_open_cont_wrt_typ_lower :
forall c1 A1,
  fvar_in_cont c1 [<=] fvar_in_cont (open_cont_wrt_typ c1 A1).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_typ_lower : lngen.

Lemma fvar_in_contd_open_contd_wrt_typ_lower :
forall cc1 A1,
  fvar_in_contd cc1 [<=] fvar_in_contd (open_contd_wrt_typ cc1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_lower : lngen.

Lemma fvar_in_cont_open_cont_wrt_exp_lower :
forall c1 e1,
  fvar_in_cont c1 [<=] fvar_in_cont (open_cont_wrt_exp c1 e1).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_exp_lower : lngen.

Lemma fvar_in_contd_open_contd_wrt_exp_lower :
forall cc1 e1,
  fvar_in_contd cc1 [<=] fvar_in_contd (open_contd_wrt_exp cc1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_lower : lngen.

Lemma ftvar_in_dbind_open_dbind_wrt_typ_lower :
forall db1 A1,
  ftvar_in_dbind db1 [<=] ftvar_in_dbind (open_dbind_wrt_typ db1 A1).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_lower : lngen.

Lemma ftvar_in_work_open_work_wrt_typ_lower :
forall w1 A1,
  ftvar_in_work w1 [<=] ftvar_in_work (open_work_wrt_typ w1 A1).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_typ_lower : lngen.

Lemma ftvar_in_work_open_work_wrt_exp_lower :
forall w1 e1,
  ftvar_in_work w1 [<=] ftvar_in_work (open_work_wrt_exp w1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_exp_lower : lngen.

Lemma fvar_in_work_open_work_wrt_typ_lower :
forall w1 A1,
  fvar_in_work w1 [<=] fvar_in_work (open_work_wrt_typ w1 A1).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_typ_lower : lngen.

Lemma fvar_in_work_open_work_wrt_exp_lower :
forall w1 e1,
  fvar_in_work w1 [<=] fvar_in_work (open_work_wrt_exp w1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_abind_open_abind_wrt_typ_rec_upper_mutual :
(forall ab1 A1 n1,
  ftvar_in_abind (open_abind_wrt_typ_rec n1 A1 ab1) [<=] ftvar_in_typ A1 `union` ftvar_in_abind ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_abind_open_abind_wrt_typ_rec_upper :
forall ab1 A1 n1,
  ftvar_in_abind (open_abind_wrt_typ_rec n1 A1 ab1) [<=] ftvar_in_typ A1 `union` ftvar_in_abind ab1.
Proof.
pose proof ftvar_in_abind_open_abind_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_open_abind_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_typ_rec_upper_ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall body1 A1 n1,
  ftvar_in_body (open_body_wrt_typ_rec n1 A1 body1) [<=] ftvar_in_typ A1 `union` ftvar_in_body body1) /\
(forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_typ_rec_upper :
forall body1 A1 n1,
  ftvar_in_body (open_body_wrt_typ_rec n1 A1 body1) [<=] ftvar_in_typ A1 `union` ftvar_in_body body1.
Proof.
pose proof ftvar_in_body_open_body_wrt_typ_rec_upper_ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_body_open_body_wrt_typ_rec_upper_ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_exp_rec_upper_ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall body1 e1 n1,
  ftvar_in_body (open_body_wrt_exp_rec n1 e1 body1) [<=] ftvar_in_exp e1 `union` ftvar_in_body body1) /\
(forall e1 e2 n1,
  ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_body_open_body_wrt_exp_rec_upper :
forall body1 e1 n1,
  ftvar_in_body (open_body_wrt_exp_rec n1 e1 body1) [<=] ftvar_in_exp e1 `union` ftvar_in_body body1.
Proof.
pose proof ftvar_in_body_open_body_wrt_exp_rec_upper_ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_body_open_body_wrt_exp_rec_upper_ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_typ_rec_upper_fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall body1 A1 n1,
  fvar_in_body (open_body_wrt_typ_rec n1 A1 body1) [<=] fvar_in_body body1) /\
(forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_typ_rec_upper :
forall body1 A1 n1,
  fvar_in_body (open_body_wrt_typ_rec n1 A1 body1) [<=] fvar_in_body body1.
Proof.
pose proof fvar_in_body_open_body_wrt_typ_rec_upper_fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_body_open_body_wrt_typ_rec_upper_fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_exp_rec_upper_fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall body1 e1 n1,
  fvar_in_body (open_body_wrt_exp_rec n1 e1 body1) [<=] fvar_in_exp e1 `union` fvar_in_body body1) /\
(forall e1 e2 n1,
  fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fvar_in_exp e2 `union` fvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_body_open_body_wrt_exp_rec_upper :
forall body1 e1 n1,
  fvar_in_body (open_body_wrt_exp_rec n1 e1 body1) [<=] fvar_in_exp e1 `union` fvar_in_body body1.
Proof.
pose proof fvar_in_body_open_body_wrt_exp_rec_upper_fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
pose proof fvar_in_body_open_body_wrt_exp_rec_upper_fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_typ_rec_upper_ftvar_in_contd_open_contd_wrt_typ_rec_upper_mutual :
(forall c1 A1 n1,
  ftvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1) [<=] ftvar_in_typ A1 `union` ftvar_in_cont c1) /\
(forall cc1 A1 n1,
  ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1) [<=] ftvar_in_typ A1 `union` ftvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_typ_rec_upper :
forall c1 A1 n1,
  ftvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1) [<=] ftvar_in_typ A1 `union` ftvar_in_cont c1.
Proof.
pose proof ftvar_in_cont_open_cont_wrt_typ_rec_upper_ftvar_in_contd_open_contd_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_typ_rec_upper :
forall cc1 A1 n1,
  ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1) [<=] ftvar_in_typ A1 `union` ftvar_in_contd cc1.
Proof.
pose proof ftvar_in_cont_open_cont_wrt_typ_rec_upper_ftvar_in_contd_open_contd_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_exp_rec_upper_ftvar_in_contd_open_contd_wrt_exp_rec_upper_mutual :
(forall c1 e1 n1,
  ftvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1) [<=] ftvar_in_exp e1 `union` ftvar_in_cont c1) /\
(forall cc1 e1 n1,
  ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_cont_open_cont_wrt_exp_rec_upper :
forall c1 e1 n1,
  ftvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1) [<=] ftvar_in_exp e1 `union` ftvar_in_cont c1.
Proof.
pose proof ftvar_in_cont_open_cont_wrt_exp_rec_upper_ftvar_in_contd_open_contd_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_exp_rec_upper :
forall cc1 e1 n1,
  ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cc1.
Proof.
pose proof ftvar_in_cont_open_cont_wrt_exp_rec_upper_ftvar_in_contd_open_contd_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_typ_rec_upper_fvar_in_contd_open_contd_wrt_typ_rec_upper_mutual :
(forall c1 A1 n1,
  fvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1) [<=] fvar_in_cont c1) /\
(forall cc1 A1 n1,
  fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1) [<=] fvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_typ_rec_upper :
forall c1 A1 n1,
  fvar_in_cont (open_cont_wrt_typ_rec n1 A1 c1) [<=] fvar_in_cont c1.
Proof.
pose proof fvar_in_cont_open_cont_wrt_typ_rec_upper_fvar_in_contd_open_contd_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_typ_rec_upper :
forall cc1 A1 n1,
  fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cc1) [<=] fvar_in_contd cc1.
Proof.
pose proof fvar_in_cont_open_cont_wrt_typ_rec_upper_fvar_in_contd_open_contd_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_exp_rec_upper_fvar_in_contd_open_contd_wrt_exp_rec_upper_mutual :
(forall c1 e1 n1,
  fvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1) [<=] fvar_in_exp e1 `union` fvar_in_cont c1) /\
(forall cc1 e1 n1,
  fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1) [<=] fvar_in_exp e1 `union` fvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_cont_open_cont_wrt_exp_rec_upper :
forall c1 e1 n1,
  fvar_in_cont (open_cont_wrt_exp_rec n1 e1 c1) [<=] fvar_in_exp e1 `union` fvar_in_cont c1.
Proof.
pose proof fvar_in_cont_open_cont_wrt_exp_rec_upper_fvar_in_contd_open_contd_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_exp_rec_upper :
forall cc1 e1 n1,
  fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cc1) [<=] fvar_in_exp e1 `union` fvar_in_contd cc1.
Proof.
pose proof fvar_in_cont_open_cont_wrt_exp_rec_upper_fvar_in_contd_open_contd_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_upper_mutual :
(forall db1 A1 n1,
  ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1) [<=] ftvar_in_typ A1 `union` ftvar_in_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_upper :
forall db1 A1 n1,
  ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1) [<=] ftvar_in_typ A1 `union` ftvar_in_dbind db1.
Proof.
pose proof ftvar_in_dbind_open_dbind_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_typ_rec_upper_mutual :
(forall w1 A1 n1,
  ftvar_in_work (open_work_wrt_typ_rec n1 A1 w1) [<=] ftvar_in_typ A1 `union` ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_typ_rec_upper :
forall w1 A1 n1,
  ftvar_in_work (open_work_wrt_typ_rec n1 A1 w1) [<=] ftvar_in_typ A1 `union` ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_open_work_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_exp_rec_upper_mutual :
(forall w1 e1 n1,
  ftvar_in_work (open_work_wrt_exp_rec n1 e1 w1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_work_open_work_wrt_exp_rec_upper :
forall w1 e1 n1,
  ftvar_in_work (open_work_wrt_exp_rec n1 e1 w1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_open_work_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_typ_rec_upper_mutual :
(forall w1 A1 n1,
  fvar_in_work (open_work_wrt_typ_rec n1 A1 w1) [<=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_typ_rec_upper :
forall w1 A1 n1,
  fvar_in_work (open_work_wrt_typ_rec n1 A1 w1) [<=] fvar_in_work w1.
Proof.
pose proof fvar_in_work_open_work_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_exp_rec_upper_mutual :
(forall w1 e1 n1,
  fvar_in_work (open_work_wrt_exp_rec n1 e1 w1) [<=] fvar_in_exp e1 `union` fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_work_open_work_wrt_exp_rec_upper :
forall w1 e1 n1,
  fvar_in_work (open_work_wrt_exp_rec n1 e1 w1) [<=] fvar_in_exp e1 `union` fvar_in_work w1.
Proof.
pose proof fvar_in_work_open_work_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  ftvar_in_typ (open_typ_wrt_typ A1 A2) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_upper : lngen.

Lemma ftvar_in_abind_open_abind_wrt_typ_upper :
forall ab1 A1,
  ftvar_in_abind (open_abind_wrt_typ ab1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_abind ab1.
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_abind_open_abind_wrt_typ_upper : lngen.

Lemma ftvar_in_body_open_body_wrt_typ_upper :
forall body1 A1,
  ftvar_in_body (open_body_wrt_typ body1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_body body1.
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_typ_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  ftvar_in_exp (open_exp_wrt_typ e1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma ftvar_in_body_open_body_wrt_exp_upper :
forall body1 e1,
  ftvar_in_body (open_body_wrt_exp body1 e1) [<=] ftvar_in_exp e1 `union` ftvar_in_body body1.
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_body_open_body_wrt_exp_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  ftvar_in_exp (open_exp_wrt_exp e1 e2) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fvar_in_body_open_body_wrt_typ_upper :
forall body1 A1,
  fvar_in_body (open_body_wrt_typ body1 A1) [<=] fvar_in_body body1.
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_typ_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  fvar_in_exp (open_exp_wrt_typ e1 A1) [<=] fvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma fvar_in_body_open_body_wrt_exp_upper :
forall body1 e1,
  fvar_in_body (open_body_wrt_exp body1 e1) [<=] fvar_in_exp e1 `union` fvar_in_body body1.
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_body_open_body_wrt_exp_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fvar_in_exp (open_exp_wrt_exp e1 e2) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma ftvar_in_cont_open_cont_wrt_typ_upper :
forall c1 A1,
  ftvar_in_cont (open_cont_wrt_typ c1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_cont c1.
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_typ_upper : lngen.

Lemma ftvar_in_contd_open_contd_wrt_typ_upper :
forall cc1 A1,
  ftvar_in_contd (open_contd_wrt_typ cc1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_contd cc1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_upper : lngen.

Lemma ftvar_in_cont_open_cont_wrt_exp_upper :
forall c1 e1,
  ftvar_in_cont (open_cont_wrt_exp c1 e1) [<=] ftvar_in_exp e1 `union` ftvar_in_cont c1.
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_cont_open_cont_wrt_exp_upper : lngen.

Lemma ftvar_in_contd_open_contd_wrt_exp_upper :
forall cc1 e1,
  ftvar_in_contd (open_contd_wrt_exp cc1 e1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cc1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_upper : lngen.

Lemma fvar_in_cont_open_cont_wrt_typ_upper :
forall c1 A1,
  fvar_in_cont (open_cont_wrt_typ c1 A1) [<=] fvar_in_cont c1.
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_typ_upper : lngen.

Lemma fvar_in_contd_open_contd_wrt_typ_upper :
forall cc1 A1,
  fvar_in_contd (open_contd_wrt_typ cc1 A1) [<=] fvar_in_contd cc1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_upper : lngen.

Lemma fvar_in_cont_open_cont_wrt_exp_upper :
forall c1 e1,
  fvar_in_cont (open_cont_wrt_exp c1 e1) [<=] fvar_in_exp e1 `union` fvar_in_cont c1.
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_cont_open_cont_wrt_exp_upper : lngen.

Lemma fvar_in_contd_open_contd_wrt_exp_upper :
forall cc1 e1,
  fvar_in_contd (open_contd_wrt_exp cc1 e1) [<=] fvar_in_exp e1 `union` fvar_in_contd cc1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_upper : lngen.

Lemma ftvar_in_dbind_open_dbind_wrt_typ_upper :
forall db1 A1,
  ftvar_in_dbind (open_dbind_wrt_typ db1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_dbind db1.
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_upper : lngen.

Lemma ftvar_in_work_open_work_wrt_typ_upper :
forall w1 A1,
  ftvar_in_work (open_work_wrt_typ w1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_work w1.
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_typ_upper : lngen.

Lemma ftvar_in_work_open_work_wrt_exp_upper :
forall w1 e1,
  ftvar_in_work (open_work_wrt_exp w1 e1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1.
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_work_open_work_wrt_exp_upper : lngen.

Lemma fvar_in_work_open_work_wrt_typ_upper :
forall w1 A1,
  fvar_in_work (open_work_wrt_typ w1 A1) [<=] fvar_in_work w1.
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_typ_upper : lngen.

Lemma fvar_in_work_open_work_wrt_exp_upper :
forall w1 e1,
  fvar_in_work (open_work_wrt_exp w1 e1) [<=] fvar_in_exp e1 `union` fvar_in_work w1.
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_work_open_work_wrt_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [=] ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_fresh :
forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [=] ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_fresh : lngen.
#[export] Hint Rewrite ftvar_in_typ_subst_tvar_in_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_fresh_mutual :
(forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1) [=] ftvar_in_abind ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_fresh :
forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1) [=] ftvar_in_abind ab1.
Proof.
pose proof ftvar_in_abind_subst_tvar_in_abind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_tvar_in_abind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_abind_subst_tvar_in_abind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_tvar_in_body_fresh_ftvar_in_exp_subst_tvar_in_exp_fresh_mutual :
(forall body1 A1 X1,
  X1 `notin` ftvar_in_body body1 ->
  ftvar_in_body (subst_tvar_in_body A1 X1 body1) [=] ftvar_in_body body1) /\
(forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_tvar_in_exp A1 X1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_tvar_in_body_fresh :
forall body1 A1 X1,
  X1 `notin` ftvar_in_body body1 ->
  ftvar_in_body (subst_tvar_in_body A1 X1 body1) [=] ftvar_in_body body1.
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_fresh_ftvar_in_exp_subst_tvar_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_tvar_in_body_fresh : lngen.
#[export] Hint Rewrite ftvar_in_body_subst_tvar_in_body_fresh using solve [auto] : lngen.

Lemma ftvar_in_exp_subst_tvar_in_exp_fresh :
forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_tvar_in_exp A1 X1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_fresh_ftvar_in_exp_subst_tvar_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_tvar_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_tvar_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_var_in_body_fresh_ftvar_in_exp_subst_var_in_exp_fresh_mutual :
(forall body1 A1 X1,
  fvar_in_body (subst_tvar_in_body A1 X1 body1) [=] fvar_in_body body1) /\
(forall e1 A1 X1,
  fvar_in_exp (subst_tvar_in_exp A1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_var_in_body_fresh :
forall body1 A1 X1,
  fvar_in_body (subst_tvar_in_body A1 X1 body1) [=] fvar_in_body body1.
Proof.
pose proof ftvar_in_body_subst_var_in_body_fresh_ftvar_in_exp_subst_var_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_var_in_body_fresh : lngen.
#[export] Hint Rewrite ftvar_in_body_subst_var_in_body_fresh using solve [auto] : lngen.

Lemma ftvar_in_exp_subst_var_in_exp_fresh :
forall e1 A1 X1,
  fvar_in_exp (subst_tvar_in_exp A1 X1 e1) [=] fvar_in_exp e1.
Proof.
pose proof ftvar_in_body_subst_var_in_body_fresh_ftvar_in_exp_subst_var_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_var_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_var_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_var_in_body_fresh_fvar_in_exp_subst_var_in_exp_fresh_mutual :
(forall body1 e1 x1,
  x1 `notin` fvar_in_body body1 ->
  fvar_in_body (subst_var_in_body e1 x1 body1) [=] fvar_in_body body1) /\
(forall e1 e2 x1,
  x1 `notin` fvar_in_exp e1 ->
  fvar_in_exp (subst_var_in_exp e2 x1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_var_in_body_fresh :
forall body1 e1 x1,
  x1 `notin` fvar_in_body body1 ->
  fvar_in_body (subst_var_in_body e1 x1 body1) [=] fvar_in_body body1.
Proof.
pose proof fvar_in_body_subst_var_in_body_fresh_fvar_in_exp_subst_var_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_var_in_body_fresh : lngen.
#[export] Hint Rewrite fvar_in_body_subst_var_in_body_fresh using solve [auto] : lngen.

Lemma fvar_in_exp_subst_var_in_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fvar_in_exp e1 ->
  fvar_in_exp (subst_var_in_exp e2 x1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_body_subst_var_in_body_fresh_fvar_in_exp_subst_var_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_var_in_exp_fresh : lngen.
#[export] Hint Rewrite fvar_in_exp_subst_var_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_fresh_ftvar_in_contd_subst_tvar_in_contd_fresh_mutual :
(forall c1 A1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  ftvar_in_cont (subst_tvar_in_cont A1 X1 c1) [=] ftvar_in_cont c1) /\
(forall cc1 A1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [=] ftvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_fresh :
forall c1 A1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  ftvar_in_cont (subst_tvar_in_cont A1 X1 c1) [=] ftvar_in_cont c1.
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_fresh_ftvar_in_contd_subst_tvar_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_tvar_in_cont_fresh : lngen.
#[export] Hint Rewrite ftvar_in_cont_subst_tvar_in_cont_fresh using solve [auto] : lngen.

Lemma ftvar_in_contd_subst_tvar_in_contd_fresh :
forall cc1 A1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [=] ftvar_in_contd cc1.
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_fresh_ftvar_in_contd_subst_tvar_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_tvar_in_contd_fresh : lngen.
#[export] Hint Rewrite ftvar_in_contd_subst_tvar_in_contd_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_var_in_cont_fresh_ftvar_in_contd_subst_var_in_contd_fresh_mutual :
(forall c1 A1 X1,
  fvar_in_cont (subst_tvar_in_cont A1 X1 c1) [=] fvar_in_cont c1) /\
(forall cc1 A1 X1,
  fvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [=] fvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_var_in_cont_fresh :
forall c1 A1 X1,
  fvar_in_cont (subst_tvar_in_cont A1 X1 c1) [=] fvar_in_cont c1.
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_fresh_ftvar_in_contd_subst_var_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_var_in_cont_fresh : lngen.
#[export] Hint Rewrite ftvar_in_cont_subst_var_in_cont_fresh using solve [auto] : lngen.

Lemma ftvar_in_contd_subst_var_in_contd_fresh :
forall cc1 A1 X1,
  fvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [=] fvar_in_contd cc1.
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_fresh_ftvar_in_contd_subst_var_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_var_in_contd_fresh : lngen.
#[export] Hint Rewrite ftvar_in_contd_subst_var_in_contd_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_var_in_cont_fresh_fvar_in_contd_subst_var_in_contd_fresh_mutual :
(forall c1 e1 x1,
  x1 `notin` fvar_in_cont c1 ->
  fvar_in_cont (subst_var_in_cont e1 x1 c1) [=] fvar_in_cont c1) /\
(forall cc1 e1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  fvar_in_contd (subst_var_in_contd e1 x1 cc1) [=] fvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_var_in_cont_fresh :
forall c1 e1 x1,
  x1 `notin` fvar_in_cont c1 ->
  fvar_in_cont (subst_var_in_cont e1 x1 c1) [=] fvar_in_cont c1.
Proof.
pose proof fvar_in_cont_subst_var_in_cont_fresh_fvar_in_contd_subst_var_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_var_in_cont_fresh : lngen.
#[export] Hint Rewrite fvar_in_cont_subst_var_in_cont_fresh using solve [auto] : lngen.

Lemma fvar_in_contd_subst_var_in_contd_fresh :
forall cc1 e1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  fvar_in_contd (subst_var_in_contd e1 x1 cc1) [=] fvar_in_contd cc1.
Proof.
pose proof fvar_in_cont_subst_var_in_cont_fresh_fvar_in_contd_subst_var_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_var_in_contd_fresh : lngen.
#[export] Hint Rewrite fvar_in_contd_subst_var_in_contd_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_fresh_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1) [=] ftvar_in_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_fresh :
forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1) [=] ftvar_in_dbind db1.
Proof.
pose proof ftvar_in_dbind_subst_tvar_in_dbind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_tvar_in_dbind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_dbind_subst_tvar_in_dbind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_tvar_in_work_fresh_mutual :
(forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  ftvar_in_work (subst_tvar_in_work A1 X1 w1) [=] ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_tvar_in_work_fresh :
forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  ftvar_in_work (subst_tvar_in_work A1 X1 w1) [=] ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_subst_tvar_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_tvar_in_work_fresh : lngen.
#[export] Hint Rewrite ftvar_in_work_subst_tvar_in_work_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_var_in_work_fresh_mutual :
(forall w1 A1 X1,
  fvar_in_work (subst_tvar_in_work A1 X1 w1) [=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_var_in_work_fresh :
forall w1 A1 X1,
  fvar_in_work (subst_tvar_in_work A1 X1 w1) [=] fvar_in_work w1.
Proof.
pose proof ftvar_in_work_subst_var_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_var_in_work_fresh : lngen.
#[export] Hint Rewrite ftvar_in_work_subst_var_in_work_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_var_in_work_fresh_mutual :
(forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  fvar_in_work (subst_var_in_work e1 x1 w1) [=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_var_in_work_fresh :
forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  fvar_in_work (subst_var_in_work e1 x1 w1) [=] fvar_in_work w1.
Proof.
pose proof fvar_in_work_subst_var_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_var_in_work_fresh : lngen.
#[export] Hint Rewrite fvar_in_work_subst_var_in_work_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_lower :
forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_lower : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_lower_mutual :
(forall ab1 A1 X1,
  remove X1 (ftvar_in_abind ab1) [<=] ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_lower :
forall ab1 A1 X1,
  remove X1 (ftvar_in_abind ab1) [<=] ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof ftvar_in_abind_subst_tvar_in_abind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_tvar_in_abind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_tvar_in_body_lower_ftvar_in_exp_subst_tvar_in_exp_lower_mutual :
(forall body1 A1 X1,
  remove X1 (ftvar_in_body body1) [<=] ftvar_in_body (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_tvar_in_body_lower :
forall body1 A1 X1,
  remove X1 (ftvar_in_body body1) [<=] ftvar_in_body (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_lower_ftvar_in_exp_subst_tvar_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_tvar_in_body_lower : lngen.

Lemma ftvar_in_exp_subst_tvar_in_exp_lower :
forall e1 A1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_lower_ftvar_in_exp_subst_tvar_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_tvar_in_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_var_in_body_lower_ftvar_in_exp_subst_var_in_exp_lower_mutual :
(forall body1 e1 x1,
  ftvar_in_body body1 [<=] ftvar_in_body (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 x1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_var_in_body_lower :
forall body1 e1 x1,
  ftvar_in_body body1 [<=] ftvar_in_body (subst_var_in_body e1 x1 body1).
Proof.
pose proof ftvar_in_body_subst_var_in_body_lower_ftvar_in_exp_subst_var_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_var_in_body_lower : lngen.

Lemma ftvar_in_exp_subst_var_in_exp_lower :
forall e1 e2 x1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (subst_var_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_body_subst_var_in_body_lower_ftvar_in_exp_subst_var_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_var_in_exp_lower : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_tvar_in_body_lower_fvar_in_exp_subst_tvar_in_exp_lower_mutual :
(forall body1 A1 X1,
  fvar_in_body body1 [<=] fvar_in_body (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_tvar_in_body_lower :
forall body1 A1 X1,
  fvar_in_body body1 [<=] fvar_in_body (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof fvar_in_body_subst_tvar_in_body_lower_fvar_in_exp_subst_tvar_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_tvar_in_body_lower : lngen.

Lemma fvar_in_exp_subst_tvar_in_exp_lower :
forall e1 A1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof fvar_in_body_subst_tvar_in_body_lower_fvar_in_exp_subst_tvar_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_tvar_in_exp_lower : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_var_in_body_lower_fvar_in_exp_subst_var_in_exp_lower_mutual :
(forall body1 e1 x1,
  remove x1 (fvar_in_body body1) [<=] fvar_in_body (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 x1,
  remove x1 (fvar_in_exp e1) [<=] fvar_in_exp (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_var_in_body_lower :
forall body1 e1 x1,
  remove x1 (fvar_in_body body1) [<=] fvar_in_body (subst_var_in_body e1 x1 body1).
Proof.
pose proof fvar_in_body_subst_var_in_body_lower_fvar_in_exp_subst_var_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_var_in_body_lower : lngen.

Lemma fvar_in_exp_subst_var_in_exp_lower :
forall e1 e2 x1,
  remove x1 (fvar_in_exp e1) [<=] fvar_in_exp (subst_var_in_exp e2 x1 e1).
Proof.
pose proof fvar_in_body_subst_var_in_body_lower_fvar_in_exp_subst_var_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_var_in_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_lower_ftvar_in_contd_subst_tvar_in_contd_lower_mutual :
(forall c1 A1 X1,
  remove X1 (ftvar_in_cont c1) [<=] ftvar_in_cont (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1,
  remove X1 (ftvar_in_contd cc1) [<=] ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_lower :
forall c1 A1 X1,
  remove X1 (ftvar_in_cont c1) [<=] ftvar_in_cont (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_lower_ftvar_in_contd_subst_tvar_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_tvar_in_cont_lower : lngen.

Lemma ftvar_in_contd_subst_tvar_in_contd_lower :
forall cc1 A1 X1,
  remove X1 (ftvar_in_contd cc1) [<=] ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_lower_ftvar_in_contd_subst_tvar_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_tvar_in_contd_lower : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_var_in_cont_lower_ftvar_in_contd_subst_var_in_contd_lower_mutual :
(forall c1 e1 x1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_var_in_cont_lower :
forall c1 e1 x1,
  ftvar_in_cont c1 [<=] ftvar_in_cont (subst_var_in_cont e1 x1 c1).
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_lower_ftvar_in_contd_subst_var_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_var_in_cont_lower : lngen.

Lemma ftvar_in_contd_subst_var_in_contd_lower :
forall cc1 e1 x1,
  ftvar_in_contd cc1 [<=] ftvar_in_contd (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_lower_ftvar_in_contd_subst_var_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_var_in_contd_lower : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_tvar_in_cont_lower_fvar_in_contd_subst_tvar_in_contd_lower_mutual :
(forall c1 A1 X1,
  fvar_in_cont c1 [<=] fvar_in_cont (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1,
  fvar_in_contd cc1 [<=] fvar_in_contd (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_tvar_in_cont_lower :
forall c1 A1 X1,
  fvar_in_cont c1 [<=] fvar_in_cont (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof fvar_in_cont_subst_tvar_in_cont_lower_fvar_in_contd_subst_tvar_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_tvar_in_cont_lower : lngen.

Lemma fvar_in_contd_subst_tvar_in_contd_lower :
forall cc1 A1 X1,
  fvar_in_contd cc1 [<=] fvar_in_contd (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof fvar_in_cont_subst_tvar_in_cont_lower_fvar_in_contd_subst_tvar_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_tvar_in_contd_lower : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_var_in_cont_lower_fvar_in_contd_subst_var_in_contd_lower_mutual :
(forall c1 e1 x1,
  remove x1 (fvar_in_cont c1) [<=] fvar_in_cont (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1,
  remove x1 (fvar_in_contd cc1) [<=] fvar_in_contd (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_var_in_cont_lower :
forall c1 e1 x1,
  remove x1 (fvar_in_cont c1) [<=] fvar_in_cont (subst_var_in_cont e1 x1 c1).
Proof.
pose proof fvar_in_cont_subst_var_in_cont_lower_fvar_in_contd_subst_var_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_var_in_cont_lower : lngen.

Lemma fvar_in_contd_subst_var_in_contd_lower :
forall cc1 e1 x1,
  remove x1 (fvar_in_contd cc1) [<=] fvar_in_contd (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof fvar_in_cont_subst_var_in_cont_lower_fvar_in_contd_subst_var_in_contd_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_var_in_contd_lower : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_lower_mutual :
(forall db1 A1 X1,
  remove X1 (ftvar_in_dbind db1) [<=] ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_lower :
forall db1 A1 X1,
  remove X1 (ftvar_in_dbind db1) [<=] ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof ftvar_in_dbind_subst_tvar_in_dbind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_tvar_in_dbind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_tvar_in_work_lower_mutual :
(forall w1 A1 X1,
  remove X1 (ftvar_in_work w1) [<=] ftvar_in_work (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_tvar_in_work_lower :
forall w1 A1 X1,
  remove X1 (ftvar_in_work w1) [<=] ftvar_in_work (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof ftvar_in_work_subst_tvar_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_tvar_in_work_lower : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_var_in_work_lower_mutual :
(forall w1 e1 x1,
  ftvar_in_work w1 [<=] ftvar_in_work (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_var_in_work_lower :
forall w1 e1 x1,
  ftvar_in_work w1 [<=] ftvar_in_work (subst_var_in_work e1 x1 w1).
Proof.
pose proof ftvar_in_work_subst_var_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_var_in_work_lower : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_tvar_in_work_lower_mutual :
(forall w1 A1 X1,
  fvar_in_work w1 [<=] fvar_in_work (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_tvar_in_work_lower :
forall w1 A1 X1,
  fvar_in_work w1 [<=] fvar_in_work (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof fvar_in_work_subst_tvar_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_tvar_in_work_lower : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_var_in_work_lower_mutual :
(forall w1 e1 x1,
  remove x1 (fvar_in_work w1) [<=] fvar_in_work (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_var_in_work_lower :
forall w1 e1 x1,
  remove x1 (fvar_in_work w1) [<=] fvar_in_work (subst_var_in_work e1 x1 w1).
Proof.
pose proof fvar_in_work_subst_var_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_var_in_work_lower : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_notin : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_notin_mutual :
(forall ab1 A1 X1 X2,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_notin :
forall ab1 A1 X1 X2,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof ftvar_in_abind_subst_tvar_in_abind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_tvar_in_abind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_tvar_in_body_notin_ftvar_in_exp_subst_tvar_in_exp_notin_mutual :
(forall body1 A1 X1 X2,
  X2 `notin` ftvar_in_body body1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_body (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_exp (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_tvar_in_body_notin :
forall body1 A1 X1 X2,
  X2 `notin` ftvar_in_body body1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_body (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_notin_ftvar_in_exp_subst_tvar_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_tvar_in_body_notin : lngen.

Lemma ftvar_in_exp_subst_tvar_in_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_exp (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_notin_ftvar_in_exp_subst_tvar_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_tvar_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_var_in_body_notin_ftvar_in_exp_subst_var_in_exp_notin_mutual :
(forall body1 e1 x1 X1,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_body (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_var_in_body_notin :
forall body1 e1 x1 X1,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_body (subst_var_in_body e1 x1 body1).
Proof.
pose proof ftvar_in_body_subst_var_in_body_notin_ftvar_in_exp_subst_var_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_var_in_body_notin : lngen.

Lemma ftvar_in_exp_subst_var_in_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp (subst_var_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_body_subst_var_in_body_notin_ftvar_in_exp_subst_var_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_var_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_tvar_in_body_notin_fvar_in_exp_subst_tvar_in_exp_notin_mutual :
(forall body1 A1 X1 x1,
  x1 `notin` fvar_in_body body1 ->
  x1 `notin` fvar_in_body (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_tvar_in_body_notin :
forall body1 A1 X1 x1,
  x1 `notin` fvar_in_body body1 ->
  x1 `notin` fvar_in_body (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof fvar_in_body_subst_tvar_in_body_notin_fvar_in_exp_subst_tvar_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_tvar_in_body_notin : lngen.

Lemma fvar_in_exp_subst_tvar_in_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof fvar_in_body_subst_tvar_in_body_notin_fvar_in_exp_subst_tvar_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_tvar_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_var_in_body_notin_fvar_in_exp_subst_var_in_exp_notin_mutual :
(forall body1 e1 x1 x2,
  x2 `notin` fvar_in_body body1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_body (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 x1 x2,
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_var_in_body_notin :
forall body1 e1 x1 x2,
  x2 `notin` fvar_in_body body1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_body (subst_var_in_body e1 x1 body1).
Proof.
pose proof fvar_in_body_subst_var_in_body_notin_fvar_in_exp_subst_var_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_var_in_body_notin : lngen.

Lemma fvar_in_exp_subst_var_in_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp (subst_var_in_exp e2 x1 e1).
Proof.
pose proof fvar_in_body_subst_var_in_body_notin_fvar_in_exp_subst_var_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_var_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_notin_ftvar_in_contd_subst_tvar_in_contd_notin_mutual :
(forall c1 A1 X1 X2,
  X2 `notin` ftvar_in_cont c1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_cont (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1 X2,
  X2 `notin` ftvar_in_contd cc1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_notin :
forall c1 A1 X1 X2,
  X2 `notin` ftvar_in_cont c1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_cont (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_notin_ftvar_in_contd_subst_tvar_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_tvar_in_cont_notin : lngen.

Lemma ftvar_in_contd_subst_tvar_in_contd_notin :
forall cc1 A1 X1 X2,
  X2 `notin` ftvar_in_contd cc1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_notin_ftvar_in_contd_subst_tvar_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_tvar_in_contd_notin : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_var_in_cont_notin_ftvar_in_contd_subst_var_in_contd_notin_mutual :
(forall c1 e1 x1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_cont (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_contd (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_var_in_cont_notin :
forall c1 e1 x1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_cont (subst_var_in_cont e1 x1 c1).
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_notin_ftvar_in_contd_subst_var_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_var_in_cont_notin : lngen.

Lemma ftvar_in_contd_subst_var_in_contd_notin :
forall cc1 e1 x1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_contd (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_notin_ftvar_in_contd_subst_var_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_var_in_contd_notin : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_tvar_in_cont_notin_fvar_in_contd_subst_tvar_in_contd_notin_mutual :
(forall c1 A1 X1 x1,
  x1 `notin` fvar_in_cont c1 ->
  x1 `notin` fvar_in_cont (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  x1 `notin` fvar_in_contd (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_tvar_in_cont_notin :
forall c1 A1 X1 x1,
  x1 `notin` fvar_in_cont c1 ->
  x1 `notin` fvar_in_cont (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof fvar_in_cont_subst_tvar_in_cont_notin_fvar_in_contd_subst_tvar_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_tvar_in_cont_notin : lngen.

Lemma fvar_in_contd_subst_tvar_in_contd_notin :
forall cc1 A1 X1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  x1 `notin` fvar_in_contd (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof fvar_in_cont_subst_tvar_in_cont_notin_fvar_in_contd_subst_tvar_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_tvar_in_contd_notin : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_var_in_cont_notin_fvar_in_contd_subst_var_in_contd_notin_mutual :
(forall c1 e1 x1 x2,
  x2 `notin` fvar_in_cont c1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_cont (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1 x2,
  x2 `notin` fvar_in_contd cc1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_contd (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_var_in_cont_notin :
forall c1 e1 x1 x2,
  x2 `notin` fvar_in_cont c1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_cont (subst_var_in_cont e1 x1 c1).
Proof.
pose proof fvar_in_cont_subst_var_in_cont_notin_fvar_in_contd_subst_var_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_var_in_cont_notin : lngen.

Lemma fvar_in_contd_subst_var_in_contd_notin :
forall cc1 e1 x1 x2,
  x2 `notin` fvar_in_contd cc1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_contd (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof fvar_in_cont_subst_var_in_cont_notin_fvar_in_contd_subst_var_in_contd_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_var_in_contd_notin : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_notin_mutual :
(forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_notin :
forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof ftvar_in_dbind_subst_tvar_in_dbind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_tvar_in_dbind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_tvar_in_work_notin_mutual :
(forall w1 A1 X1 X2,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_work (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_tvar_in_work_notin :
forall w1 A1 X1 X2,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_work (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof ftvar_in_work_subst_tvar_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_tvar_in_work_notin : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_var_in_work_notin_mutual :
(forall w1 e1 x1 X1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_work (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_var_in_work_notin :
forall w1 e1 x1 X1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_work (subst_var_in_work e1 x1 w1).
Proof.
pose proof ftvar_in_work_subst_var_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_var_in_work_notin : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_tvar_in_work_notin_mutual :
(forall w1 A1 X1 x1,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_work (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_tvar_in_work_notin :
forall w1 A1 X1 x1,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_work (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof fvar_in_work_subst_tvar_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_tvar_in_work_notin : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_var_in_work_notin_mutual :
(forall w1 e1 x1 x2,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_work (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_var_in_work_notin :
forall w1 e1 x1 x2,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_work (subst_var_in_work e1 x1 w1).
Proof.
pose proof fvar_in_work_subst_var_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_var_in_work_notin : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_upper_mutual :
(forall A1 A2 X1,
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_tvar_in_typ_upper :
forall A1 A2 X1,
  ftvar_in_typ (subst_tvar_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_subst_tvar_in_typ_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_tvar_in_typ_upper : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_upper_mutual :
(forall ab1 A1 X1,
  ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_abind ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_tvar_in_abind_upper :
forall ab1 A1 X1,
  ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_abind ab1).
Proof.
pose proof ftvar_in_abind_subst_tvar_in_abind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_tvar_in_abind_upper : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_tvar_in_body_upper_ftvar_in_exp_subst_tvar_in_exp_upper_mutual :
(forall body1 A1 X1,
  ftvar_in_body (subst_tvar_in_body A1 X1 body1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_body body1)) /\
(forall e1 A1 X1,
  ftvar_in_exp (subst_tvar_in_exp A1 X1 e1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_tvar_in_body_upper :
forall body1 A1 X1,
  ftvar_in_body (subst_tvar_in_body A1 X1 body1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_body body1).
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_upper_ftvar_in_exp_subst_tvar_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_tvar_in_body_upper : lngen.

Lemma ftvar_in_exp_subst_tvar_in_exp_upper :
forall e1 A1 X1,
  ftvar_in_exp (subst_tvar_in_exp A1 X1 e1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_body_subst_tvar_in_body_upper_ftvar_in_exp_subst_tvar_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_tvar_in_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_body_subst_var_in_body_upper_ftvar_in_exp_subst_var_in_exp_upper_mutual :
(forall body1 e1 x1,
  ftvar_in_body (subst_var_in_body e1 x1 body1) [<=] ftvar_in_exp e1 `union` ftvar_in_body body1) /\
(forall e1 e2 x1,
  ftvar_in_exp (subst_var_in_exp e2 x1 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_body_subst_var_in_body_upper :
forall body1 e1 x1,
  ftvar_in_body (subst_var_in_body e1 x1 body1) [<=] ftvar_in_exp e1 `union` ftvar_in_body body1.
Proof.
pose proof ftvar_in_body_subst_var_in_body_upper_ftvar_in_exp_subst_var_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_body_subst_var_in_body_upper : lngen.

Lemma ftvar_in_exp_subst_var_in_exp_upper :
forall e1 e2 x1,
  ftvar_in_exp (subst_var_in_exp e2 x1 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_body_subst_var_in_body_upper_ftvar_in_exp_subst_var_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_var_in_exp_upper : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_tvar_in_body_upper_fvar_in_exp_subst_tvar_in_exp_upper_mutual :
(forall body1 A1 X1,
  fvar_in_body (subst_tvar_in_body A1 X1 body1) [<=] fvar_in_body body1) /\
(forall e1 A1 X1,
  fvar_in_exp (subst_tvar_in_exp A1 X1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_tvar_in_body_upper :
forall body1 A1 X1,
  fvar_in_body (subst_tvar_in_body A1 X1 body1) [<=] fvar_in_body body1.
Proof.
pose proof fvar_in_body_subst_tvar_in_body_upper_fvar_in_exp_subst_tvar_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_tvar_in_body_upper : lngen.

Lemma fvar_in_exp_subst_tvar_in_exp_upper :
forall e1 A1 X1,
  fvar_in_exp (subst_tvar_in_exp A1 X1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_body_subst_tvar_in_body_upper_fvar_in_exp_subst_tvar_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_tvar_in_exp_upper : lngen.

(* begin hide *)

Lemma fvar_in_body_subst_var_in_body_upper_fvar_in_exp_subst_var_in_exp_upper_mutual :
(forall body1 e1 x1,
  fvar_in_body (subst_var_in_body e1 x1 body1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_body body1)) /\
(forall e1 e2 x1,
  fvar_in_exp (subst_var_in_exp e2 x1 e1) [<=] fvar_in_exp e2 `union` remove x1 (fvar_in_exp e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_body_subst_var_in_body_upper :
forall body1 e1 x1,
  fvar_in_body (subst_var_in_body e1 x1 body1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_body body1).
Proof.
pose proof fvar_in_body_subst_var_in_body_upper_fvar_in_exp_subst_var_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_body_subst_var_in_body_upper : lngen.

Lemma fvar_in_exp_subst_var_in_exp_upper :
forall e1 e2 x1,
  fvar_in_exp (subst_var_in_exp e2 x1 e1) [<=] fvar_in_exp e2 `union` remove x1 (fvar_in_exp e1).
Proof.
pose proof fvar_in_body_subst_var_in_body_upper_fvar_in_exp_subst_var_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_var_in_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_upper_ftvar_in_contd_subst_tvar_in_contd_upper_mutual :
(forall c1 A1 X1,
  ftvar_in_cont (subst_tvar_in_cont A1 X1 c1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_cont c1)) /\
(forall cc1 A1 X1,
  ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_contd cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_tvar_in_cont_upper :
forall c1 A1 X1,
  ftvar_in_cont (subst_tvar_in_cont A1 X1 c1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_cont c1).
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_upper_ftvar_in_contd_subst_tvar_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_tvar_in_cont_upper : lngen.

Lemma ftvar_in_contd_subst_tvar_in_contd_upper :
forall cc1 A1 X1,
  ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_contd cc1).
Proof.
pose proof ftvar_in_cont_subst_tvar_in_cont_upper_ftvar_in_contd_subst_tvar_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_tvar_in_contd_upper : lngen.

(* begin hide *)

Lemma ftvar_in_cont_subst_var_in_cont_upper_ftvar_in_contd_subst_var_in_contd_upper_mutual :
(forall c1 e1 x1,
  ftvar_in_cont (subst_var_in_cont e1 x1 c1) [<=] ftvar_in_exp e1 `union` ftvar_in_cont c1) /\
(forall cc1 e1 x1,
  ftvar_in_contd (subst_var_in_contd e1 x1 cc1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_cont_subst_var_in_cont_upper :
forall c1 e1 x1,
  ftvar_in_cont (subst_var_in_cont e1 x1 c1) [<=] ftvar_in_exp e1 `union` ftvar_in_cont c1.
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_upper_ftvar_in_contd_subst_var_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_cont_subst_var_in_cont_upper : lngen.

Lemma ftvar_in_contd_subst_var_in_contd_upper :
forall cc1 e1 x1,
  ftvar_in_contd (subst_var_in_contd e1 x1 cc1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cc1.
Proof.
pose proof ftvar_in_cont_subst_var_in_cont_upper_ftvar_in_contd_subst_var_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_var_in_contd_upper : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_tvar_in_cont_upper_fvar_in_contd_subst_tvar_in_contd_upper_mutual :
(forall c1 A1 X1,
  fvar_in_cont (subst_tvar_in_cont A1 X1 c1) [<=] fvar_in_cont c1) /\
(forall cc1 A1 X1,
  fvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [<=] fvar_in_contd cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_tvar_in_cont_upper :
forall c1 A1 X1,
  fvar_in_cont (subst_tvar_in_cont A1 X1 c1) [<=] fvar_in_cont c1.
Proof.
pose proof fvar_in_cont_subst_tvar_in_cont_upper_fvar_in_contd_subst_tvar_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_tvar_in_cont_upper : lngen.

Lemma fvar_in_contd_subst_tvar_in_contd_upper :
forall cc1 A1 X1,
  fvar_in_contd (subst_tvar_in_contd A1 X1 cc1) [<=] fvar_in_contd cc1.
Proof.
pose proof fvar_in_cont_subst_tvar_in_cont_upper_fvar_in_contd_subst_tvar_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_tvar_in_contd_upper : lngen.

(* begin hide *)

Lemma fvar_in_cont_subst_var_in_cont_upper_fvar_in_contd_subst_var_in_contd_upper_mutual :
(forall c1 e1 x1,
  fvar_in_cont (subst_var_in_cont e1 x1 c1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_cont c1)) /\
(forall cc1 e1 x1,
  fvar_in_contd (subst_var_in_contd e1 x1 cc1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_contd cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_cont_subst_var_in_cont_upper :
forall c1 e1 x1,
  fvar_in_cont (subst_var_in_cont e1 x1 c1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_cont c1).
Proof.
pose proof fvar_in_cont_subst_var_in_cont_upper_fvar_in_contd_subst_var_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_cont_subst_var_in_cont_upper : lngen.

Lemma fvar_in_contd_subst_var_in_contd_upper :
forall cc1 e1 x1,
  fvar_in_contd (subst_var_in_contd e1 x1 cc1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_contd cc1).
Proof.
pose proof fvar_in_cont_subst_var_in_cont_upper_fvar_in_contd_subst_var_in_contd_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_var_in_contd_upper : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_upper_mutual :
(forall db1 A1 X1,
  ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_dbind db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_tvar_in_dbind_upper :
forall db1 A1 X1,
  ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_dbind db1).
Proof.
pose proof ftvar_in_dbind_subst_tvar_in_dbind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_tvar_in_dbind_upper : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_tvar_in_work_upper_mutual :
(forall w1 A1 X1,
  ftvar_in_work (subst_tvar_in_work A1 X1 w1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_work w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_tvar_in_work_upper :
forall w1 A1 X1,
  ftvar_in_work (subst_tvar_in_work A1 X1 w1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_work w1).
Proof.
pose proof ftvar_in_work_subst_tvar_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_tvar_in_work_upper : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_var_in_work_upper_mutual :
(forall w1 e1 x1,
  ftvar_in_work (subst_var_in_work e1 x1 w1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_var_in_work_upper :
forall w1 e1 x1,
  ftvar_in_work (subst_var_in_work e1 x1 w1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_subst_var_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_var_in_work_upper : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_tvar_in_work_upper_mutual :
(forall w1 A1 X1,
  fvar_in_work (subst_tvar_in_work A1 X1 w1) [<=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_tvar_in_work_upper :
forall w1 A1 X1,
  fvar_in_work (subst_tvar_in_work A1 X1 w1) [<=] fvar_in_work w1.
Proof.
pose proof fvar_in_work_subst_tvar_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_tvar_in_work_upper : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_var_in_work_upper_mutual :
(forall w1 e1 x1,
  fvar_in_work (subst_var_in_work e1 x1 w1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_work w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_var_in_work_upper :
forall w1 e1 x1,
  fvar_in_work (subst_var_in_work e1 x1 w1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_work w1).
Proof.
pose proof fvar_in_work_subst_var_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_var_in_work_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 A2).
Proof.
pose proof subst_tvar_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_close_abind_wrt_typ_rec_mutual :
(forall ab1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_abind A1 X1 (close_abind_wrt_typ_rec n1 X2 ab1) = close_abind_wrt_typ_rec n1 X2 (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_close_abind_wrt_typ_rec :
forall ab1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_abind A1 X1 (close_abind_wrt_typ_rec n1 X2 ab1) = close_abind_wrt_typ_rec n1 X2 (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof subst_tvar_in_abind_close_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_close_abind_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_close_body_wrt_typ_rec_subst_tvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall body1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_body A1 X1 (close_body_wrt_typ_rec n1 X2 body1) = close_body_wrt_typ_rec n1 X2 (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_close_body_wrt_typ_rec :
forall body1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_body A1 X1 (close_body_wrt_typ_rec n1 X2 body1) = close_body_wrt_typ_rec n1 X2 (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_typ_rec_subst_tvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_typ_rec : lngen.

Lemma subst_tvar_in_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_typ_rec_subst_tvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_close_body_wrt_exp_rec_subst_tvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall body1 A1 x1 X1 n1,
  subst_tvar_in_body A1 x1 (close_body_wrt_exp_rec n1 X1 body1) = close_body_wrt_exp_rec n1 X1 (subst_tvar_in_body A1 x1 body1)) /\
(forall e1 A1 x1 X1 n1,
  subst_tvar_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_tvar_in_exp A1 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_close_body_wrt_exp_rec :
forall body1 A1 x1 X1 n1,
  subst_tvar_in_body A1 x1 (close_body_wrt_exp_rec n1 X1 body1) = close_body_wrt_exp_rec n1 X1 (subst_tvar_in_body A1 x1 body1).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_exp_rec_subst_tvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_exp_rec : lngen.

Lemma subst_tvar_in_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  subst_tvar_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_tvar_in_exp A1 x1 e1).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_exp_rec_subst_tvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_var_in_body_close_body_wrt_typ_rec_subst_var_in_exp_close_exp_wrt_typ_rec_mutual :
(forall body1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_body e1 X1 (close_body_wrt_typ_rec n1 x1 body1) = close_body_wrt_typ_rec n1 x1 (subst_var_in_body e1 X1 body1)) /\
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_var_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_close_body_wrt_typ_rec :
forall body1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_body e1 X1 (close_body_wrt_typ_rec n1 x1 body1) = close_body_wrt_typ_rec n1 x1 (subst_var_in_body e1 X1 body1).
Proof.
pose proof subst_var_in_body_close_body_wrt_typ_rec_subst_var_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_typ_rec : lngen.

Lemma subst_var_in_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_var_in_exp e1 X1 e2).
Proof.
pose proof subst_var_in_body_close_body_wrt_typ_rec_subst_var_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_var_in_body_close_body_wrt_exp_rec_subst_var_in_exp_close_exp_wrt_exp_rec_mutual :
(forall body1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_body e1 x1 (close_body_wrt_exp_rec n1 x2 body1) = close_body_wrt_exp_rec n1 x2 (subst_var_in_body e1 x1 body1)) /\
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_var_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_close_body_wrt_exp_rec :
forall body1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_body e1 x1 (close_body_wrt_exp_rec n1 x2 body1) = close_body_wrt_exp_rec n1 x2 (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_close_body_wrt_exp_rec_subst_var_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_exp_rec : lngen.

Lemma subst_var_in_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_var_in_exp e1 x1 e2).
Proof.
pose proof subst_var_in_body_close_body_wrt_exp_rec_subst_var_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_typ_rec_subst_tvar_in_contd_close_contd_wrt_typ_rec_mutual :
(forall c1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_cont A1 X1 (close_cont_wrt_typ_rec n1 X2 c1) = close_cont_wrt_typ_rec n1 X2 (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_contd A1 X1 (close_contd_wrt_typ_rec n1 X2 cc1) = close_contd_wrt_typ_rec n1 X2 (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_typ_rec :
forall c1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_cont A1 X1 (close_cont_wrt_typ_rec n1 X2 c1) = close_cont_wrt_typ_rec n1 X2 (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_typ_rec_subst_tvar_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_typ_rec : lngen.

Lemma subst_tvar_in_contd_close_contd_wrt_typ_rec :
forall cc1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_contd A1 X1 (close_contd_wrt_typ_rec n1 X2 cc1) = close_contd_wrt_typ_rec n1 X2 (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_typ_rec_subst_tvar_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_exp_rec_subst_tvar_in_contd_close_contd_wrt_exp_rec_mutual :
(forall c1 A1 x1 X1 n1,
  subst_tvar_in_cont A1 x1 (close_cont_wrt_exp_rec n1 X1 c1) = close_cont_wrt_exp_rec n1 X1 (subst_tvar_in_cont A1 x1 c1)) /\
(forall cc1 A1 x1 X1 n1,
  subst_tvar_in_contd A1 x1 (close_contd_wrt_exp_rec n1 X1 cc1) = close_contd_wrt_exp_rec n1 X1 (subst_tvar_in_contd A1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_exp_rec :
forall c1 A1 x1 X1 n1,
  subst_tvar_in_cont A1 x1 (close_cont_wrt_exp_rec n1 X1 c1) = close_cont_wrt_exp_rec n1 X1 (subst_tvar_in_cont A1 x1 c1).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_exp_rec_subst_tvar_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_exp_rec : lngen.

Lemma subst_tvar_in_contd_close_contd_wrt_exp_rec :
forall cc1 A1 x1 X1 n1,
  subst_tvar_in_contd A1 x1 (close_contd_wrt_exp_rec n1 X1 cc1) = close_contd_wrt_exp_rec n1 X1 (subst_tvar_in_contd A1 x1 cc1).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_exp_rec_subst_tvar_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_var_in_cont_close_cont_wrt_typ_rec_subst_var_in_contd_close_contd_wrt_typ_rec_mutual :
(forall c1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_cont e1 X1 (close_cont_wrt_typ_rec n1 x1 c1) = close_cont_wrt_typ_rec n1 x1 (subst_var_in_cont e1 X1 c1)) /\
(forall cc1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_contd e1 X1 (close_contd_wrt_typ_rec n1 x1 cc1) = close_contd_wrt_typ_rec n1 x1 (subst_var_in_contd e1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_close_cont_wrt_typ_rec :
forall c1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_cont e1 X1 (close_cont_wrt_typ_rec n1 x1 c1) = close_cont_wrt_typ_rec n1 x1 (subst_var_in_cont e1 X1 c1).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_typ_rec_subst_var_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_typ_rec : lngen.

Lemma subst_var_in_contd_close_contd_wrt_typ_rec :
forall cc1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_contd e1 X1 (close_contd_wrt_typ_rec n1 x1 cc1) = close_contd_wrt_typ_rec n1 x1 (subst_var_in_contd e1 X1 cc1).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_typ_rec_subst_var_in_contd_close_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_var_in_cont_close_cont_wrt_exp_rec_subst_var_in_contd_close_contd_wrt_exp_rec_mutual :
(forall c1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_cont e1 x1 (close_cont_wrt_exp_rec n1 x2 c1) = close_cont_wrt_exp_rec n1 x2 (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_contd e1 x1 (close_contd_wrt_exp_rec n1 x2 cc1) = close_contd_wrt_exp_rec n1 x2 (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_close_cont_wrt_exp_rec :
forall c1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_cont e1 x1 (close_cont_wrt_exp_rec n1 x2 c1) = close_cont_wrt_exp_rec n1 x2 (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_exp_rec_subst_var_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_exp_rec : lngen.

Lemma subst_var_in_contd_close_contd_wrt_exp_rec :
forall cc1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_contd e1 x1 (close_contd_wrt_exp_rec n1 x2 cc1) = close_contd_wrt_exp_rec n1 x2 (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_exp_rec_subst_var_in_contd_close_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_dbind A1 X1 (close_dbind_wrt_typ_rec n1 X2 db1) = close_dbind_wrt_typ_rec n1 X2 (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_close_dbind_wrt_typ_rec :
forall db1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_dbind A1 X1 (close_dbind_wrt_typ_rec n1 X2 db1) = close_dbind_wrt_typ_rec n1 X2 (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof subst_tvar_in_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_close_dbind_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_close_work_wrt_typ_rec_mutual :
(forall w1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_work A1 X1 (close_work_wrt_typ_rec n1 X2 w1) = close_work_wrt_typ_rec n1 X2 (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_close_work_wrt_typ_rec :
forall w1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_work A1 X1 (close_work_wrt_typ_rec n1 X2 w1) = close_work_wrt_typ_rec n1 X2 (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_close_work_wrt_exp_rec_mutual :
(forall w1 A1 x1 X1 n1,
  subst_tvar_in_work A1 x1 (close_work_wrt_exp_rec n1 X1 w1) = close_work_wrt_exp_rec n1 X1 (subst_tvar_in_work A1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_close_work_wrt_exp_rec :
forall w1 A1 x1 X1 n1,
  subst_tvar_in_work A1 x1 (close_work_wrt_exp_rec n1 X1 w1) = close_work_wrt_exp_rec n1 X1 (subst_tvar_in_work A1 x1 w1).
Proof.
pose proof subst_tvar_in_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_var_in_work_close_work_wrt_typ_rec_mutual :
(forall w1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_work e1 X1 (close_work_wrt_typ_rec n1 x1 w1) = close_work_wrt_typ_rec n1 x1 (subst_var_in_work e1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_close_work_wrt_typ_rec :
forall w1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_work e1 X1 (close_work_wrt_typ_rec n1 x1 w1) = close_work_wrt_typ_rec n1 x1 (subst_var_in_work e1 X1 w1).
Proof.
pose proof subst_var_in_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_var_in_work_close_work_wrt_exp_rec_mutual :
(forall w1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_work e1 x1 (close_work_wrt_exp_rec n1 x2 w1) = close_work_wrt_exp_rec n1 x2 (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_close_work_wrt_exp_rec :
forall w1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_work e1 x1 (close_work_wrt_exp_rec n1 x2 w1) = close_work_wrt_exp_rec n1 x2 (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_exp_rec : lngen.

Lemma subst_tvar_in_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ : lngen.

Lemma subst_tvar_in_abind_close_abind_wrt_typ :
forall ab1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_abind A1 X1 (close_abind_wrt_typ X2 ab1) = close_abind_wrt_typ X2 (subst_tvar_in_abind A1 X1 ab1).
Proof.
unfold close_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_close_abind_wrt_typ : lngen.

Lemma subst_tvar_in_body_close_body_wrt_typ :
forall body1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_body A1 X1 (close_body_wrt_typ X2 body1) = close_body_wrt_typ X2 (subst_tvar_in_body A1 X1 body1).
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_typ : lngen.

Lemma subst_tvar_in_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_exp A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (subst_tvar_in_exp A1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_tvar_in_body_close_body_wrt_exp :
forall body1 A1 x1 X1,
  lc_typ A1 ->  subst_tvar_in_body A1 x1 (close_body_wrt_exp X1 body1) = close_body_wrt_exp X1 (subst_tvar_in_body A1 x1 body1).
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_exp : lngen.

Lemma subst_tvar_in_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  lc_typ A1 ->  subst_tvar_in_exp A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_tvar_in_exp A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_var_in_body_close_body_wrt_typ :
forall body1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_body e1 X1 (close_body_wrt_typ x1 body1) = close_body_wrt_typ x1 (subst_var_in_body e1 X1 body1).
Proof.
unfold close_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_typ : lngen.

Lemma subst_var_in_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_var_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_var_in_body_close_body_wrt_exp :
forall body1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_body e1 x1 (close_body_wrt_exp x2 body1) = close_body_wrt_exp x2 (subst_var_in_body e1 x1 body1).
Proof.
unfold close_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_exp : lngen.

Lemma subst_var_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_var_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_tvar_in_cont_close_cont_wrt_typ :
forall c1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_cont A1 X1 (close_cont_wrt_typ X2 c1) = close_cont_wrt_typ X2 (subst_tvar_in_cont A1 X1 c1).
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_typ : lngen.

Lemma subst_tvar_in_contd_close_contd_wrt_typ :
forall cc1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_contd A1 X1 (close_contd_wrt_typ X2 cc1) = close_contd_wrt_typ X2 (subst_tvar_in_contd A1 X1 cc1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_typ : lngen.

Lemma subst_tvar_in_cont_close_cont_wrt_exp :
forall c1 A1 x1 X1,
  lc_typ A1 ->  subst_tvar_in_cont A1 x1 (close_cont_wrt_exp X1 c1) = close_cont_wrt_exp X1 (subst_tvar_in_cont A1 x1 c1).
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_exp : lngen.

Lemma subst_tvar_in_contd_close_contd_wrt_exp :
forall cc1 A1 x1 X1,
  lc_typ A1 ->  subst_tvar_in_contd A1 x1 (close_contd_wrt_exp X1 cc1) = close_contd_wrt_exp X1 (subst_tvar_in_contd A1 x1 cc1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_exp : lngen.

Lemma subst_var_in_cont_close_cont_wrt_typ :
forall c1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_cont e1 X1 (close_cont_wrt_typ x1 c1) = close_cont_wrt_typ x1 (subst_var_in_cont e1 X1 c1).
Proof.
unfold close_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_typ : lngen.

Lemma subst_var_in_contd_close_contd_wrt_typ :
forall cc1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_contd e1 X1 (close_contd_wrt_typ x1 cc1) = close_contd_wrt_typ x1 (subst_var_in_contd e1 X1 cc1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_typ : lngen.

Lemma subst_var_in_cont_close_cont_wrt_exp :
forall c1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_cont e1 x1 (close_cont_wrt_exp x2 c1) = close_cont_wrt_exp x2 (subst_var_in_cont e1 x1 c1).
Proof.
unfold close_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_exp : lngen.

Lemma subst_var_in_contd_close_contd_wrt_exp :
forall cc1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_contd e1 x1 (close_contd_wrt_exp x2 cc1) = close_contd_wrt_exp x2 (subst_var_in_contd e1 x1 cc1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_exp : lngen.

Lemma subst_tvar_in_dbind_close_dbind_wrt_typ :
forall db1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_dbind A1 X1 (close_dbind_wrt_typ X2 db1) = close_dbind_wrt_typ X2 (subst_tvar_in_dbind A1 X1 db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_close_dbind_wrt_typ : lngen.

Lemma subst_tvar_in_work_close_work_wrt_typ :
forall w1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_tvar_in_work A1 X1 (close_work_wrt_typ X2 w1) = close_work_wrt_typ X2 (subst_tvar_in_work A1 X1 w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_typ : lngen.

Lemma subst_tvar_in_work_close_work_wrt_exp :
forall w1 A1 x1 X1,
  lc_typ A1 ->  subst_tvar_in_work A1 x1 (close_work_wrt_exp X1 w1) = close_work_wrt_exp X1 (subst_tvar_in_work A1 x1 w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_exp : lngen.

Lemma subst_var_in_work_close_work_wrt_typ :
forall w1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_var_in_work e1 X1 (close_work_wrt_typ x1 w1) = close_work_wrt_typ x1 (subst_var_in_work e1 X1 w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_typ : lngen.

Lemma subst_var_in_work_close_work_wrt_exp :
forall w1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_var_in_work e1 x1 (close_work_wrt_exp x2 w1) = close_work_wrt_exp x2 (subst_var_in_work e1 x1 w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_exp : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof subst_tvar_in_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_degree_abind_wrt_typ_mutual :
(forall ab1 A1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_abind_wrt_typ n1 (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_degree_abind_wrt_typ :
forall ab1 A1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_abind_wrt_typ n1 (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof subst_tvar_in_abind_degree_abind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_degree_abind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_degree_body_wrt_typ_subst_tvar_in_exp_degree_exp_wrt_typ_mutual :
(forall body1 A1 X1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_body_wrt_typ n1 (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_degree_body_wrt_typ :
forall body1 A1 X1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_body_wrt_typ n1 (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_degree_body_wrt_typ_subst_tvar_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_degree_body_wrt_typ : lngen.

Lemma subst_tvar_in_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_degree_body_wrt_typ_subst_tvar_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_degree_body_wrt_exp_subst_tvar_in_exp_degree_exp_wrt_exp_mutual :
(forall body1 A1 X1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp n1 (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_degree_body_wrt_exp :
forall body1 A1 X1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_body_wrt_exp n1 (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_degree_body_wrt_exp_subst_tvar_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_degree_body_wrt_exp : lngen.

Lemma subst_tvar_in_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_degree_body_wrt_exp_subst_tvar_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_var_in_body_degree_body_wrt_typ_subst_var_in_exp_degree_exp_wrt_typ_mutual :
(forall body1 e1 x1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_body_wrt_typ n1 (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_degree_body_wrt_typ :
forall body1 e1 x1 n1,
  degree_body_wrt_typ n1 body1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_body_wrt_typ n1 (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_degree_body_wrt_typ_subst_var_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_degree_body_wrt_typ : lngen.

Lemma subst_var_in_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_var_in_exp e2 x1 e1).
Proof.
pose proof subst_var_in_body_degree_body_wrt_typ_subst_var_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_var_in_body_degree_body_wrt_exp_subst_var_in_exp_degree_exp_wrt_exp_mutual :
(forall body1 e1 x1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_body_wrt_exp n1 (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_degree_body_wrt_exp :
forall body1 e1 x1 n1,
  degree_body_wrt_exp n1 body1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_body_wrt_exp n1 (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_degree_body_wrt_exp_subst_var_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_degree_body_wrt_exp : lngen.

Lemma subst_var_in_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_var_in_exp e2 x1 e1).
Proof.
pose proof subst_var_in_body_degree_body_wrt_exp_subst_var_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_degree_cont_wrt_typ_subst_tvar_in_contd_degree_contd_wrt_typ_mutual :
(forall c1 A1 X1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_cont_wrt_typ n1 (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_degree_cont_wrt_typ :
forall c1 A1 X1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_cont_wrt_typ n1 (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_degree_cont_wrt_typ_subst_tvar_in_contd_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_degree_cont_wrt_typ : lngen.

Lemma subst_tvar_in_contd_degree_contd_wrt_typ :
forall cc1 A1 X1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_degree_cont_wrt_typ_subst_tvar_in_contd_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_degree_contd_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_degree_cont_wrt_exp_subst_tvar_in_contd_degree_contd_wrt_exp_mutual :
(forall c1 A1 X1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp n1 (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp n1 (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_degree_cont_wrt_exp :
forall c1 A1 X1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_cont_wrt_exp n1 (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_degree_cont_wrt_exp_subst_tvar_in_contd_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_degree_cont_wrt_exp : lngen.

Lemma subst_tvar_in_contd_degree_contd_wrt_exp :
forall cc1 A1 X1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_contd_wrt_exp n1 (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_degree_cont_wrt_exp_subst_tvar_in_contd_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_degree_contd_wrt_exp : lngen.

(* begin hide *)

Lemma subst_var_in_cont_degree_cont_wrt_typ_subst_var_in_contd_degree_contd_wrt_typ_mutual :
(forall c1 e1 x1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_cont_wrt_typ n1 (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_degree_cont_wrt_typ :
forall c1 e1 x1 n1,
  degree_cont_wrt_typ n1 c1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_cont_wrt_typ n1 (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_degree_cont_wrt_typ_subst_var_in_contd_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_degree_cont_wrt_typ : lngen.

Lemma subst_var_in_contd_degree_contd_wrt_typ :
forall cc1 e1 x1 n1,
  degree_contd_wrt_typ n1 cc1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_degree_cont_wrt_typ_subst_var_in_contd_degree_contd_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_degree_contd_wrt_typ : lngen.

(* begin hide *)

Lemma subst_var_in_cont_degree_cont_wrt_exp_subst_var_in_contd_degree_contd_wrt_exp_mutual :
(forall c1 e1 x1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_cont_wrt_exp n1 (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_degree_cont_wrt_exp :
forall c1 e1 x1 n1,
  degree_cont_wrt_exp n1 c1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_cont_wrt_exp n1 (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_degree_cont_wrt_exp_subst_var_in_contd_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_degree_cont_wrt_exp : lngen.

Lemma subst_var_in_contd_degree_contd_wrt_exp :
forall cc1 e1 x1 n1,
  degree_contd_wrt_exp n1 cc1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_degree_cont_wrt_exp_subst_var_in_contd_degree_contd_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_degree_contd_wrt_exp : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_degree_dbind_wrt_typ_mutual :
(forall db1 A1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_degree_dbind_wrt_typ :
forall db1 A1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof subst_tvar_in_dbind_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_degree_dbind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_degree_work_wrt_typ_mutual :
(forall w1 A1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_work_wrt_typ n1 (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_degree_work_wrt_typ :
forall w1 A1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_work_wrt_typ n1 (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_degree_work_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_degree_work_wrt_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_degree_work_wrt_exp_mutual :
(forall w1 A1 X1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_degree_work_wrt_exp :
forall w1 A1 X1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_degree_work_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_degree_work_wrt_exp : lngen.

(* begin hide *)

Lemma subst_var_in_work_degree_work_wrt_typ_mutual :
(forall w1 e1 x1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_degree_work_wrt_typ :
forall w1 e1 x1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_degree_work_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_degree_work_wrt_typ : lngen.

(* begin hide *)

Lemma subst_var_in_work_degree_work_wrt_exp_mutual :
(forall w1 e1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_work_wrt_exp n1 (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_degree_work_wrt_exp :
forall w1 e1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_work_wrt_exp n1 (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_degree_work_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_degree_work_wrt_exp : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_tvar_in_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_tvar_in_typ A1 X1 A2 = A2.
Proof.
pose proof subst_tvar_in_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_fresh_eq_mutual :
(forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  subst_tvar_in_abind A1 X1 ab1 = ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_fresh_eq :
forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  subst_tvar_in_abind A1 X1 ab1 = ab1.
Proof.
pose proof subst_tvar_in_abind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_abind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_fresh_eq_subst_tvar_in_exp_fresh_eq_mutual :
(forall body1 A1 X1,
  X1 `notin` ftvar_in_body body1 ->
  subst_tvar_in_body A1 X1 body1 = body1) /\
(forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_tvar_in_exp A1 X1 e1 = e1).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_fresh_eq :
forall body1 A1 X1,
  X1 `notin` ftvar_in_body body1 ->
  subst_tvar_in_body A1 X1 body1 = body1.
Proof.
pose proof subst_tvar_in_body_fresh_eq_subst_tvar_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_body_fresh_eq using solve [auto] : lngen.

Lemma subst_tvar_in_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_tvar_in_exp A1 X1 e1 = e1.
Proof.
pose proof subst_tvar_in_body_fresh_eq_subst_tvar_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_in_body_fresh_eq_subst_var_in_exp_fresh_eq_mutual :
(forall body1 e1 x1,
  x1 `notin` fvar_in_body body1 ->
  subst_var_in_body e1 x1 body1 = body1) /\
(forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  subst_var_in_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_fresh_eq :
forall body1 e1 x1,
  x1 `notin` fvar_in_body body1 ->
  subst_var_in_body e1 x1 body1 = body1.
Proof.
pose proof subst_var_in_body_fresh_eq_subst_var_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_in_body_fresh_eq using solve [auto] : lngen.

Lemma subst_var_in_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  subst_var_in_exp e1 x1 e2 = e2.
Proof.
pose proof subst_var_in_body_fresh_eq_subst_var_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_fresh_eq_subst_tvar_in_contd_fresh_eq_mutual :
(forall c1 A1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  subst_tvar_in_cont A1 X1 c1 = c1) /\
(forall cc1 A1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  subst_tvar_in_contd A1 X1 cc1 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_fresh_eq :
forall c1 A1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  subst_tvar_in_cont A1 X1 c1 = c1.
Proof.
pose proof subst_tvar_in_cont_fresh_eq_subst_tvar_in_contd_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_cont_fresh_eq using solve [auto] : lngen.

Lemma subst_tvar_in_contd_fresh_eq :
forall cc1 A1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  subst_tvar_in_contd A1 X1 cc1 = cc1.
Proof.
pose proof subst_tvar_in_cont_fresh_eq_subst_tvar_in_contd_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_contd_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_in_cont_fresh_eq_subst_var_in_contd_fresh_eq_mutual :
(forall c1 e1 x1,
  x1 `notin` fvar_in_cont c1 ->
  subst_var_in_cont e1 x1 c1 = c1) /\
(forall cc1 e1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  subst_var_in_contd e1 x1 cc1 = cc1).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_fresh_eq :
forall c1 e1 x1,
  x1 `notin` fvar_in_cont c1 ->
  subst_var_in_cont e1 x1 c1 = c1.
Proof.
pose proof subst_var_in_cont_fresh_eq_subst_var_in_contd_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_in_cont_fresh_eq using solve [auto] : lngen.

Lemma subst_var_in_contd_fresh_eq :
forall cc1 e1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  subst_var_in_contd e1 x1 cc1 = cc1.
Proof.
pose proof subst_var_in_cont_fresh_eq_subst_var_in_contd_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_in_contd_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_fresh_eq_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  subst_tvar_in_dbind A1 X1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_fresh_eq :
forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  subst_tvar_in_dbind A1 X1 db1 = db1.
Proof.
pose proof subst_tvar_in_dbind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_dbind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_fresh_eq_mutual :
(forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  subst_tvar_in_work A1 X1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_fresh_eq :
forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  subst_tvar_in_work A1 X1 w1 = w1.
Proof.
pose proof subst_tvar_in_work_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_fresh_eq : lngen.
#[export] Hint Rewrite subst_tvar_in_work_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_in_work_fresh_eq_mutual :
(forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  subst_var_in_work e1 x1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_fresh_eq :
forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  subst_var_in_work e1 x1 w1 = w1.
Proof.
pose proof subst_var_in_work_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_fresh_eq : lngen.
#[export] Hint Rewrite subst_var_in_work_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X1 A2).
Proof.
pose proof subst_tvar_in_typ_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_fresh_same_mutual :
(forall ab1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_fresh_same :
forall ab1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof subst_tvar_in_abind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_fresh_same_subst_tvar_in_exp_fresh_same_mutual :
(forall body1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_body (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_fresh_same :
forall body1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_body (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_fresh_same_subst_tvar_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_fresh_same : lngen.

Lemma subst_tvar_in_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_fresh_same_subst_tvar_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_var_in_body_fresh_same_subst_var_in_exp_fresh_same_mutual :
(forall body1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_body (subst_var_in_body e1 x1 body1)) /\
(forall e2 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_var_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_fresh_same :
forall body1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_body (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_fresh_same_subst_var_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_fresh_same : lngen.

Lemma subst_var_in_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_var_in_exp e1 x1 e2).
Proof.
pose proof subst_var_in_body_fresh_same_subst_var_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_fresh_same_subst_tvar_in_contd_fresh_same_mutual :
(forall c1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_cont (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_fresh_same :
forall c1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_cont (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_fresh_same_subst_tvar_in_contd_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_fresh_same : lngen.

Lemma subst_tvar_in_contd_fresh_same :
forall cc1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_fresh_same_subst_tvar_in_contd_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_fresh_same : lngen.

(* begin hide *)

Lemma subst_var_in_cont_fresh_same_subst_var_in_contd_fresh_same_mutual :
(forall c1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_cont (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_fresh_same :
forall c1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_cont (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_fresh_same_subst_var_in_contd_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_fresh_same : lngen.

Lemma subst_var_in_contd_fresh_same :
forall cc1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_fresh_same_subst_var_in_contd_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_fresh_same_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_fresh_same :
forall db1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof subst_tvar_in_dbind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_fresh_same_mutual :
(forall w1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_fresh_same :
forall w1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_fresh_same : lngen.

(* begin hide *)

Lemma subst_var_in_work_fresh_same_mutual :
(forall w1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_fresh_same :
forall w1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_fresh_same : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_tvar_in_typ A1 X2 A2).
Proof.
pose proof subst_tvar_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_fresh_mutual :
(forall ab1 A1 X1 X2,
  X1 `notin` ftvar_in_abind ab1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_tvar_in_abind A1 X2 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_fresh :
forall ab1 A1 X1 X2,
  X1 `notin` ftvar_in_abind ab1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_tvar_in_abind A1 X2 ab1).
Proof.
pose proof subst_tvar_in_abind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_fresh_subst_tvar_in_exp_fresh_mutual :
(forall body1 A1 X1 X2,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_body (subst_tvar_in_body A1 X2 body1)) /\
(forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_tvar_in_exp A1 X2 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_fresh :
forall body1 A1 X1 X2,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_body (subst_tvar_in_body A1 X2 body1).
Proof.
pose proof subst_tvar_in_body_fresh_subst_tvar_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_fresh : lngen.

Lemma subst_tvar_in_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_tvar_in_exp A1 X2 e1).
Proof.
pose proof subst_tvar_in_body_fresh_subst_tvar_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_var_in_body_fresh_subst_var_in_exp_fresh_mutual :
(forall body1 e1 x1 x2,
  x1 `notin` fvar_in_body body1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_body (subst_var_in_body e1 x2 body1)) /\
(forall e2 e1 x1 x2,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_var_in_exp e1 x2 e2)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_fresh :
forall body1 e1 x1 x2,
  x1 `notin` fvar_in_body body1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_body (subst_var_in_body e1 x2 body1).
Proof.
pose proof subst_var_in_body_fresh_subst_var_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_fresh : lngen.

Lemma subst_var_in_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_var_in_exp e1 x2 e2).
Proof.
pose proof subst_var_in_body_fresh_subst_var_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_fresh_subst_tvar_in_contd_fresh_mutual :
(forall c1 A1 X1 X2,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_cont (subst_tvar_in_cont A1 X2 c1)) /\
(forall cc1 A1 X1 X2,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_tvar_in_contd A1 X2 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_fresh :
forall c1 A1 X1 X2,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_cont (subst_tvar_in_cont A1 X2 c1).
Proof.
pose proof subst_tvar_in_cont_fresh_subst_tvar_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_fresh : lngen.

Lemma subst_tvar_in_contd_fresh :
forall cc1 A1 X1 X2,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_tvar_in_contd A1 X2 cc1).
Proof.
pose proof subst_tvar_in_cont_fresh_subst_tvar_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_fresh : lngen.

(* begin hide *)

Lemma subst_var_in_cont_fresh_subst_var_in_contd_fresh_mutual :
(forall c1 e1 x1 x2,
  x1 `notin` fvar_in_cont c1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_cont (subst_var_in_cont e1 x2 c1)) /\
(forall cc1 e1 x1 x2,
  x1 `notin` fvar_in_contd cc1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_var_in_contd e1 x2 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_fresh :
forall c1 e1 x1 x2,
  x1 `notin` fvar_in_cont c1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_cont (subst_var_in_cont e1 x2 c1).
Proof.
pose proof subst_var_in_cont_fresh_subst_var_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_fresh : lngen.

Lemma subst_var_in_contd_fresh :
forall cc1 e1 x1 x2,
  x1 `notin` fvar_in_contd cc1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_var_in_contd e1 x2 cc1).
Proof.
pose proof subst_var_in_cont_fresh_subst_var_in_contd_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_fresh_mutual :
(forall db1 A1 X1 X2,
  X1 `notin` ftvar_in_dbind db1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_tvar_in_dbind A1 X2 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_fresh :
forall db1 A1 X1 X2,
  X1 `notin` ftvar_in_dbind db1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_tvar_in_dbind A1 X2 db1).
Proof.
pose proof subst_tvar_in_dbind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_fresh : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_fresh_mutual :
(forall w1 A1 X1 X2,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_tvar_in_work A1 X2 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_fresh :
forall w1 A1 X1 X2,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_tvar_in_work A1 X2 w1).
Proof.
pose proof subst_tvar_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_fresh : lngen.

(* begin hide *)

Lemma subst_var_in_work_fresh_mutual :
(forall w1 e1 x1 x2,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_var_in_work e1 x2 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_fresh :
forall w1 e1 x1 x2,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_var_in_work e1 x2 w1).
Proof.
pose proof subst_var_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_fresh : lngen.

Lemma subst_tvar_in_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (subst_tvar_in_typ A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_lc_typ : lngen.

Lemma subst_tvar_in_abind_lc_abind :
forall ab1 A1 X1,
  lc_abind ab1 ->
  lc_typ A1 ->
  lc_abind (subst_tvar_in_abind A1 X1 ab1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_lc_abind : lngen.

Lemma subst_tvar_in_body_lc_body :
forall body1 A1 X1,
  lc_body body1 ->
  lc_typ A1 ->
  lc_body (subst_tvar_in_body A1 X1 body1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_lc_body : lngen.

Lemma subst_tvar_in_exp_lc_exp :
forall e1 A1 X1,
  lc_exp e1 ->
  lc_typ A1 ->
  lc_exp (subst_tvar_in_exp A1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_lc_exp : lngen.

Lemma subst_var_in_body_lc_body :
forall body1 e1 x1,
  lc_body body1 ->
  lc_exp e1 ->
  lc_body (subst_var_in_body e1 x1 body1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_lc_body : lngen.

Lemma subst_var_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_var_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_lc_exp : lngen.

Lemma subst_tvar_in_cont_lc_cont :
forall c1 A1 X1,
  lc_cont c1 ->
  lc_typ A1 ->
  lc_cont (subst_tvar_in_cont A1 X1 c1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_lc_cont : lngen.

Lemma subst_tvar_in_contd_lc_contd :
forall cc1 A1 X1,
  lc_contd cc1 ->
  lc_typ A1 ->
  lc_contd (subst_tvar_in_contd A1 X1 cc1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_lc_contd : lngen.

Lemma subst_var_in_cont_lc_cont :
forall c1 e1 x1,
  lc_cont c1 ->
  lc_exp e1 ->
  lc_cont (subst_var_in_cont e1 x1 c1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_lc_cont : lngen.

Lemma subst_var_in_contd_lc_contd :
forall cc1 e1 x1,
  lc_contd cc1 ->
  lc_exp e1 ->
  lc_contd (subst_var_in_contd e1 x1 cc1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_lc_contd : lngen.

Lemma subst_tvar_in_dbind_lc_dbind :
forall db1 A1 X1,
  lc_dbind db1 ->
  lc_typ A1 ->
  lc_dbind (subst_tvar_in_dbind A1 X1 db1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_lc_dbind : lngen.

Lemma subst_tvar_in_work_lc_work :
forall w1 A1 X1,
  lc_work w1 ->
  lc_typ A1 ->
  lc_work (subst_tvar_in_work A1 X1 w1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_lc_work : lngen.

Lemma subst_var_in_work_lc_work :
forall w1 e1 x1,
  lc_work w1 ->
  lc_exp e1 ->
  lc_work (subst_var_in_work e1 x1 w1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_lc_work : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_typ A1 X1 A3).
Proof.
pose proof subst_tvar_in_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_abind_open_abind_wrt_typ_rec_mutual :
(forall ab1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_abind A1 X1 (open_abind_wrt_typ_rec n1 A2 ab1) = open_abind_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_abind_open_abind_wrt_typ_rec :
forall ab1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_abind A1 X1 (open_abind_wrt_typ_rec n1 A2 ab1) = open_abind_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof subst_tvar_in_abind_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_open_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_open_body_wrt_typ_rec_subst_tvar_in_exp_open_exp_wrt_typ_rec_mutual :
(forall body1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_body A1 X1 (open_body_wrt_typ_rec n1 A2 body1) = open_body_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_open_body_wrt_typ_rec :
forall body1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_body A1 X1 (open_body_wrt_typ_rec n1 A2 body1) = open_body_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_open_body_wrt_typ_rec_subst_tvar_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_exp_open_exp_wrt_typ_rec :
forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_open_body_wrt_typ_rec_subst_tvar_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_open_body_wrt_exp_rec_subst_tvar_in_exp_open_exp_wrt_exp_rec_mutual :
(forall body1 A1 e1 X1 n1,
  subst_tvar_in_body A1 X1 (open_body_wrt_exp_rec n1 e1 body1) = open_body_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_body A1 X1 body1)) /\
(forall e2 A1 e1 X1 n1,
  subst_tvar_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_exp A1 X1 e2)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_open_body_wrt_exp_rec :
forall body1 A1 e1 X1 n1,
  subst_tvar_in_body A1 X1 (open_body_wrt_exp_rec n1 e1 body1) = open_body_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_open_body_wrt_exp_rec_subst_tvar_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 X1 n1,
  subst_tvar_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_exp A1 X1 e2).
Proof.
pose proof subst_tvar_in_body_open_body_wrt_exp_rec_subst_tvar_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_open_body_wrt_typ_rec_subst_var_in_exp_open_exp_wrt_typ_rec_mutual :
(forall body1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_body e1 x1 (open_body_wrt_typ_rec n1 A1 body1) = open_body_wrt_typ_rec n1 A1 (subst_var_in_body e1 x1 body1)) /\
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_var_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_open_body_wrt_typ_rec :
forall body1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_body e1 x1 (open_body_wrt_typ_rec n1 A1 body1) = open_body_wrt_typ_rec n1 A1 (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_open_body_wrt_typ_rec_subst_var_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_exp_open_exp_wrt_typ_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_var_in_exp e1 x1 e2).
Proof.
pose proof subst_var_in_body_open_body_wrt_typ_rec_subst_var_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_open_body_wrt_exp_rec_subst_var_in_exp_open_exp_wrt_exp_rec_mutual :
(forall body1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_body e1 x1 (open_body_wrt_exp_rec n1 e2 body1) = open_body_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_body e1 x1 body1)) /\
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_exp e1 x1 e3)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_open_body_wrt_exp_rec :
forall body1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_body e1 x1 (open_body_wrt_exp_rec n1 e2 body1) = open_body_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_open_body_wrt_exp_rec_subst_var_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_exp e1 x1 e3).
Proof.
pose proof subst_var_in_body_open_body_wrt_exp_rec_subst_var_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_open_cont_wrt_typ_rec_subst_tvar_in_contd_open_contd_wrt_typ_rec_mutual :
(forall c1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_cont A1 X1 (open_cont_wrt_typ_rec n1 A2 c1) = open_cont_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_contd A1 X1 (open_contd_wrt_typ_rec n1 A2 cc1) = open_contd_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_open_cont_wrt_typ_rec :
forall c1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_cont A1 X1 (open_cont_wrt_typ_rec n1 A2 c1) = open_cont_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_open_cont_wrt_typ_rec_subst_tvar_in_contd_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_contd_open_contd_wrt_typ_rec :
forall cc1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_contd A1 X1 (open_contd_wrt_typ_rec n1 A2 cc1) = open_contd_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_open_cont_wrt_typ_rec_subst_tvar_in_contd_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_open_cont_wrt_exp_rec_subst_tvar_in_contd_open_contd_wrt_exp_rec_mutual :
(forall c1 A1 e1 X1 n1,
  subst_tvar_in_cont A1 X1 (open_cont_wrt_exp_rec n1 e1 c1) = open_cont_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 e1 X1 n1,
  subst_tvar_in_contd A1 X1 (open_contd_wrt_exp_rec n1 e1 cc1) = open_contd_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_open_cont_wrt_exp_rec :
forall c1 A1 e1 X1 n1,
  subst_tvar_in_cont A1 X1 (open_cont_wrt_exp_rec n1 e1 c1) = open_cont_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_open_cont_wrt_exp_rec_subst_tvar_in_contd_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_contd_open_contd_wrt_exp_rec :
forall cc1 A1 e1 X1 n1,
  subst_tvar_in_contd A1 X1 (open_contd_wrt_exp_rec n1 e1 cc1) = open_contd_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_open_cont_wrt_exp_rec_subst_tvar_in_contd_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_open_cont_wrt_typ_rec_subst_var_in_contd_open_contd_wrt_typ_rec_mutual :
(forall c1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_cont e1 x1 (open_cont_wrt_typ_rec n1 A1 c1) = open_cont_wrt_typ_rec n1 A1 (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_contd e1 x1 (open_contd_wrt_typ_rec n1 A1 cc1) = open_contd_wrt_typ_rec n1 A1 (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_open_cont_wrt_typ_rec :
forall c1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_cont e1 x1 (open_cont_wrt_typ_rec n1 A1 c1) = open_cont_wrt_typ_rec n1 A1 (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_open_cont_wrt_typ_rec_subst_var_in_contd_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_contd_open_contd_wrt_typ_rec :
forall cc1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_contd e1 x1 (open_contd_wrt_typ_rec n1 A1 cc1) = open_contd_wrt_typ_rec n1 A1 (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_open_cont_wrt_typ_rec_subst_var_in_contd_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_open_cont_wrt_exp_rec_subst_var_in_contd_open_contd_wrt_exp_rec_mutual :
(forall c1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_cont e1 x1 (open_cont_wrt_exp_rec n1 e2 c1) = open_cont_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_contd e1 x1 (open_contd_wrt_exp_rec n1 e2 cc1) = open_contd_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_open_cont_wrt_exp_rec :
forall c1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_cont e1 x1 (open_cont_wrt_exp_rec n1 e2 c1) = open_cont_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_open_cont_wrt_exp_rec_subst_var_in_contd_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_contd_open_contd_wrt_exp_rec :
forall cc1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_contd e1 x1 (open_contd_wrt_exp_rec n1 e2 cc1) = open_contd_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_open_cont_wrt_exp_rec_subst_var_in_contd_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_dbind_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 A2 db1) = open_dbind_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_dbind_open_dbind_wrt_typ_rec :
forall db1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 A2 db1) = open_dbind_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof subst_tvar_in_dbind_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_open_work_wrt_typ_rec_mutual :
(forall w1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_work A1 X1 (open_work_wrt_typ_rec n1 A2 w1) = open_work_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_open_work_wrt_typ_rec :
forall w1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_tvar_in_work A1 X1 (open_work_wrt_typ_rec n1 A2 w1) = open_work_wrt_typ_rec n1 (subst_tvar_in_typ A1 X1 A2) (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_open_work_wrt_exp_rec_mutual :
(forall w1 A1 e1 X1 n1,
  subst_tvar_in_work A1 X1 (open_work_wrt_exp_rec n1 e1 w1) = open_work_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_open_work_wrt_exp_rec :
forall w1 A1 e1 X1 n1,
  subst_tvar_in_work A1 X1 (open_work_wrt_exp_rec n1 e1 w1) = open_work_wrt_exp_rec n1 (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_open_work_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_open_work_wrt_typ_rec_mutual :
(forall w1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_work e1 x1 (open_work_wrt_typ_rec n1 A1 w1) = open_work_wrt_typ_rec n1 A1 (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_open_work_wrt_typ_rec :
forall w1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_var_in_work e1 x1 (open_work_wrt_typ_rec n1 A1 w1) = open_work_wrt_typ_rec n1 A1 (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_open_work_wrt_exp_rec_mutual :
(forall w1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_work e1 x1 (open_work_wrt_exp_rec n1 e2 w1) = open_work_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_open_work_wrt_exp_rec :
forall w1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_var_in_work e1 x1 (open_work_wrt_exp_rec n1 e2 w1) = open_work_wrt_exp_rec n1 (subst_var_in_exp e1 x1 e2) (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_open_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_tvar_in_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (subst_tvar_in_typ A1 X1 A3) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_open_typ_wrt_typ : lngen.

Lemma subst_tvar_in_abind_open_abind_wrt_typ :
forall ab1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_abind A1 X1 (open_abind_wrt_typ ab1 A2) = open_abind_wrt_typ (subst_tvar_in_abind A1 X1 ab1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_open_abind_wrt_typ : lngen.

Lemma subst_tvar_in_body_open_body_wrt_typ :
forall body1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_body A1 X1 (open_body_wrt_typ body1 A2) = open_body_wrt_typ (subst_tvar_in_body A1 X1 body1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_open_body_wrt_typ : lngen.

Lemma subst_tvar_in_exp_open_exp_wrt_typ :
forall e1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_exp A1 X1 (open_exp_wrt_typ e1 A2) = open_exp_wrt_typ (subst_tvar_in_exp A1 X1 e1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_tvar_in_body_open_body_wrt_exp :
forall body1 A1 e1 X1,
  subst_tvar_in_body A1 X1 (open_body_wrt_exp body1 e1) = open_body_wrt_exp (subst_tvar_in_body A1 X1 body1) (subst_tvar_in_exp A1 X1 e1).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_open_body_wrt_exp : lngen.

Lemma subst_tvar_in_exp_open_exp_wrt_exp :
forall e2 A1 e1 X1,
  subst_tvar_in_exp A1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_tvar_in_exp A1 X1 e2) (subst_tvar_in_exp A1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_var_in_body_open_body_wrt_typ :
forall body1 e1 A1 x1,
  lc_exp e1 ->
  subst_var_in_body e1 x1 (open_body_wrt_typ body1 A1) = open_body_wrt_typ (subst_var_in_body e1 x1 body1) A1.
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_open_body_wrt_typ : lngen.

Lemma subst_var_in_exp_open_exp_wrt_typ :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_var_in_exp e1 x1 (open_exp_wrt_typ e2 A1) = open_exp_wrt_typ (subst_var_in_exp e1 x1 e2) A1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_var_in_body_open_body_wrt_exp :
forall body1 e1 e2 x1,
  lc_exp e1 ->
  subst_var_in_body e1 x1 (open_body_wrt_exp body1 e2) = open_body_wrt_exp (subst_var_in_body e1 x1 body1) (subst_var_in_exp e1 x1 e2).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_open_body_wrt_exp : lngen.

Lemma subst_var_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_var_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_var_in_exp e1 x1 e3) (subst_var_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_tvar_in_cont_open_cont_wrt_typ :
forall c1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_cont A1 X1 (open_cont_wrt_typ c1 A2) = open_cont_wrt_typ (subst_tvar_in_cont A1 X1 c1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_open_cont_wrt_typ : lngen.

Lemma subst_tvar_in_contd_open_contd_wrt_typ :
forall cc1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_contd A1 X1 (open_contd_wrt_typ cc1 A2) = open_contd_wrt_typ (subst_tvar_in_contd A1 X1 cc1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_open_contd_wrt_typ : lngen.

Lemma subst_tvar_in_cont_open_cont_wrt_exp :
forall c1 A1 e1 X1,
  subst_tvar_in_cont A1 X1 (open_cont_wrt_exp c1 e1) = open_cont_wrt_exp (subst_tvar_in_cont A1 X1 c1) (subst_tvar_in_exp A1 X1 e1).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_open_cont_wrt_exp : lngen.

Lemma subst_tvar_in_contd_open_contd_wrt_exp :
forall cc1 A1 e1 X1,
  subst_tvar_in_contd A1 X1 (open_contd_wrt_exp cc1 e1) = open_contd_wrt_exp (subst_tvar_in_contd A1 X1 cc1) (subst_tvar_in_exp A1 X1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_open_contd_wrt_exp : lngen.

Lemma subst_var_in_cont_open_cont_wrt_typ :
forall c1 e1 A1 x1,
  lc_exp e1 ->
  subst_var_in_cont e1 x1 (open_cont_wrt_typ c1 A1) = open_cont_wrt_typ (subst_var_in_cont e1 x1 c1) A1.
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_open_cont_wrt_typ : lngen.

Lemma subst_var_in_contd_open_contd_wrt_typ :
forall cc1 e1 A1 x1,
  lc_exp e1 ->
  subst_var_in_contd e1 x1 (open_contd_wrt_typ cc1 A1) = open_contd_wrt_typ (subst_var_in_contd e1 x1 cc1) A1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_open_contd_wrt_typ : lngen.

Lemma subst_var_in_cont_open_cont_wrt_exp :
forall c1 e1 e2 x1,
  lc_exp e1 ->
  subst_var_in_cont e1 x1 (open_cont_wrt_exp c1 e2) = open_cont_wrt_exp (subst_var_in_cont e1 x1 c1) (subst_var_in_exp e1 x1 e2).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_open_cont_wrt_exp : lngen.

Lemma subst_var_in_contd_open_contd_wrt_exp :
forall cc1 e1 e2 x1,
  lc_exp e1 ->
  subst_var_in_contd e1 x1 (open_contd_wrt_exp cc1 e2) = open_contd_wrt_exp (subst_var_in_contd e1 x1 cc1) (subst_var_in_exp e1 x1 e2).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_open_contd_wrt_exp : lngen.

Lemma subst_tvar_in_dbind_open_dbind_wrt_typ :
forall db1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ db1 A2) = open_dbind_wrt_typ (subst_tvar_in_dbind A1 X1 db1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_open_dbind_wrt_typ : lngen.

Lemma subst_tvar_in_work_open_work_wrt_typ :
forall w1 A1 A2 X1,
  lc_typ A1 ->
  subst_tvar_in_work A1 X1 (open_work_wrt_typ w1 A2) = open_work_wrt_typ (subst_tvar_in_work A1 X1 w1) (subst_tvar_in_typ A1 X1 A2).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_open_work_wrt_typ : lngen.

Lemma subst_tvar_in_work_open_work_wrt_exp :
forall w1 A1 e1 X1,
  subst_tvar_in_work A1 X1 (open_work_wrt_exp w1 e1) = open_work_wrt_exp (subst_tvar_in_work A1 X1 w1) (subst_tvar_in_exp A1 X1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_open_work_wrt_exp : lngen.

Lemma subst_var_in_work_open_work_wrt_typ :
forall w1 e1 A1 x1,
  lc_exp e1 ->
  subst_var_in_work e1 x1 (open_work_wrt_typ w1 A1) = open_work_wrt_typ (subst_var_in_work e1 x1 w1) A1.
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_open_work_wrt_typ : lngen.

Lemma subst_var_in_work_open_work_wrt_exp :
forall w1 e1 e2 x1,
  lc_exp e1 ->
  subst_var_in_work e1 x1 (open_work_wrt_exp w1 e2) = open_work_wrt_exp (subst_var_in_work e1 x1 w1) (subst_var_in_exp e1 x1 e2).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_open_work_wrt_exp : lngen.

Lemma subst_tvar_in_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (subst_tvar_in_typ A1 X1 A2) (typ_var_f X2) = subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_typ_open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_tvar_in_abind_open_abind_wrt_typ_var :
forall ab1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_abind_wrt_typ (subst_tvar_in_abind A1 X1 ab1) (typ_var_f X2) = subst_tvar_in_abind A1 X1 (open_abind_wrt_typ ab1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_abind_open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_open_abind_wrt_typ_var : lngen.

Lemma subst_tvar_in_body_open_body_wrt_typ_var :
forall body1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_body_wrt_typ (subst_tvar_in_body A1 X1 body1) (typ_var_f X2) = subst_tvar_in_body A1 X1 (open_body_wrt_typ body1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_body_open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_open_body_wrt_typ_var : lngen.

Lemma subst_tvar_in_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_exp_wrt_typ (subst_tvar_in_exp A1 X1 e1) (typ_var_f X2) = subst_tvar_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_tvar_in_body_open_body_wrt_exp_var :
forall body1 A1 X1 x1,
  open_body_wrt_exp (subst_tvar_in_body A1 X1 body1) (exp_var_f x1) = subst_tvar_in_body A1 X1 (open_body_wrt_exp body1 (exp_var_f x1)).
Proof.
intros; rewrite subst_tvar_in_body_open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_open_body_wrt_exp_var : lngen.

Lemma subst_tvar_in_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_exp_wrt_exp (subst_tvar_in_exp A1 X1 e1) (exp_var_f x1) = subst_tvar_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_tvar_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_var_in_body_open_body_wrt_typ_var :
forall body1 e1 x1 X1,
  lc_exp e1 ->
  open_body_wrt_typ (subst_var_in_body e1 x1 body1) (typ_var_f X1) = subst_var_in_body e1 x1 (open_body_wrt_typ body1 (typ_var_f X1)).
Proof.
intros; rewrite subst_var_in_body_open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_open_body_wrt_typ_var : lngen.

Lemma subst_var_in_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_var_in_exp e1 x1 e2) (typ_var_f X1) = subst_var_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)).
Proof.
intros; rewrite subst_var_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_var_in_body_open_body_wrt_exp_var :
forall body1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_body_wrt_exp (subst_var_in_body e1 x1 body1) (exp_var_f x2) = subst_var_in_body e1 x1 (open_body_wrt_exp body1 (exp_var_f x2)).
Proof.
intros; rewrite subst_var_in_body_open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_open_body_wrt_exp_var : lngen.

Lemma subst_var_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_var_in_exp e1 x1 e2) (exp_var_f x2) = subst_var_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_var_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_tvar_in_cont_open_cont_wrt_typ_var :
forall c1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_cont_wrt_typ (subst_tvar_in_cont A1 X1 c1) (typ_var_f X2) = subst_tvar_in_cont A1 X1 (open_cont_wrt_typ c1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_cont_open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_open_cont_wrt_typ_var : lngen.

Lemma subst_tvar_in_contd_open_contd_wrt_typ_var :
forall cc1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_contd_wrt_typ (subst_tvar_in_contd A1 X1 cc1) (typ_var_f X2) = subst_tvar_in_contd A1 X1 (open_contd_wrt_typ cc1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_contd_open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_open_contd_wrt_typ_var : lngen.

Lemma subst_tvar_in_cont_open_cont_wrt_exp_var :
forall c1 A1 X1 x1,
  open_cont_wrt_exp (subst_tvar_in_cont A1 X1 c1) (exp_var_f x1) = subst_tvar_in_cont A1 X1 (open_cont_wrt_exp c1 (exp_var_f x1)).
Proof.
intros; rewrite subst_tvar_in_cont_open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_open_cont_wrt_exp_var : lngen.

Lemma subst_tvar_in_contd_open_contd_wrt_exp_var :
forall cc1 A1 X1 x1,
  open_contd_wrt_exp (subst_tvar_in_contd A1 X1 cc1) (exp_var_f x1) = subst_tvar_in_contd A1 X1 (open_contd_wrt_exp cc1 (exp_var_f x1)).
Proof.
intros; rewrite subst_tvar_in_contd_open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_open_contd_wrt_exp_var : lngen.

Lemma subst_var_in_cont_open_cont_wrt_typ_var :
forall c1 e1 x1 X1,
  lc_exp e1 ->
  open_cont_wrt_typ (subst_var_in_cont e1 x1 c1) (typ_var_f X1) = subst_var_in_cont e1 x1 (open_cont_wrt_typ c1 (typ_var_f X1)).
Proof.
intros; rewrite subst_var_in_cont_open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_open_cont_wrt_typ_var : lngen.

Lemma subst_var_in_contd_open_contd_wrt_typ_var :
forall cc1 e1 x1 X1,
  lc_exp e1 ->
  open_contd_wrt_typ (subst_var_in_contd e1 x1 cc1) (typ_var_f X1) = subst_var_in_contd e1 x1 (open_contd_wrt_typ cc1 (typ_var_f X1)).
Proof.
intros; rewrite subst_var_in_contd_open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_open_contd_wrt_typ_var : lngen.

Lemma subst_var_in_cont_open_cont_wrt_exp_var :
forall c1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_cont_wrt_exp (subst_var_in_cont e1 x1 c1) (exp_var_f x2) = subst_var_in_cont e1 x1 (open_cont_wrt_exp c1 (exp_var_f x2)).
Proof.
intros; rewrite subst_var_in_cont_open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_open_cont_wrt_exp_var : lngen.

Lemma subst_var_in_contd_open_contd_wrt_exp_var :
forall cc1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_contd_wrt_exp (subst_var_in_contd e1 x1 cc1) (exp_var_f x2) = subst_var_in_contd e1 x1 (open_contd_wrt_exp cc1 (exp_var_f x2)).
Proof.
intros; rewrite subst_var_in_contd_open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_open_contd_wrt_exp_var : lngen.

Lemma subst_tvar_in_dbind_open_dbind_wrt_typ_var :
forall db1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_dbind_wrt_typ (subst_tvar_in_dbind A1 X1 db1) (typ_var_f X2) = subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_dbind_open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_open_dbind_wrt_typ_var : lngen.

Lemma subst_tvar_in_work_open_work_wrt_typ_var :
forall w1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_work_wrt_typ (subst_tvar_in_work A1 X1 w1) (typ_var_f X2) = subst_tvar_in_work A1 X1 (open_work_wrt_typ w1 (typ_var_f X2)).
Proof.
intros; rewrite subst_tvar_in_work_open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_open_work_wrt_typ_var : lngen.

Lemma subst_tvar_in_work_open_work_wrt_exp_var :
forall w1 A1 X1 x1,
  open_work_wrt_exp (subst_tvar_in_work A1 X1 w1) (exp_var_f x1) = subst_tvar_in_work A1 X1 (open_work_wrt_exp w1 (exp_var_f x1)).
Proof.
intros; rewrite subst_tvar_in_work_open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_open_work_wrt_exp_var : lngen.

Lemma subst_var_in_work_open_work_wrt_typ_var :
forall w1 e1 x1 X1,
  lc_exp e1 ->
  open_work_wrt_typ (subst_var_in_work e1 x1 w1) (typ_var_f X1) = subst_var_in_work e1 x1 (open_work_wrt_typ w1 (typ_var_f X1)).
Proof.
intros; rewrite subst_var_in_work_open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_open_work_wrt_typ_var : lngen.

Lemma subst_var_in_work_open_work_wrt_exp_var :
forall w1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_work_wrt_exp (subst_var_in_work e1 x1 w1) (exp_var_f x2) = subst_var_in_work e1 x1 (open_work_wrt_exp w1 (exp_var_f x2)).
Proof.
intros; rewrite subst_var_in_work_open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_open_work_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_tvar_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_typ_spec_rec :
forall A1 A2 X1 n1,
  subst_tvar_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof subst_tvar_in_typ_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_abind_spec_rec_mutual :
(forall ab1 A1 X1 n1,
  subst_tvar_in_abind A1 X1 ab1 = open_abind_wrt_typ_rec n1 A1 (close_abind_wrt_typ_rec n1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_abind_spec_rec :
forall ab1 A1 X1 n1,
  subst_tvar_in_abind A1 X1 ab1 = open_abind_wrt_typ_rec n1 A1 (close_abind_wrt_typ_rec n1 X1 ab1).
Proof.
pose proof subst_tvar_in_abind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_spec_rec_subst_tvar_in_exp_spec_rec_mutual :
(forall body1 A1 X1 n1,
  subst_tvar_in_body A1 X1 body1 = open_body_wrt_typ_rec n1 A1 (close_body_wrt_typ_rec n1 X1 body1)) /\
(forall e1 A1 X1 n1,
  subst_tvar_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_spec_rec :
forall body1 A1 X1 n1,
  subst_tvar_in_body A1 X1 body1 = open_body_wrt_typ_rec n1 A1 (close_body_wrt_typ_rec n1 X1 body1).
Proof.
pose proof subst_tvar_in_body_spec_rec_subst_tvar_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_exp_spec_rec :
forall e1 A1 X1 n1,
  subst_tvar_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof subst_tvar_in_body_spec_rec_subst_tvar_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_spec_rec_subst_var_in_exp_spec_rec_mutual :
(forall body1 e1 x1 n1,
  subst_var_in_body e1 x1 body1 = open_body_wrt_exp_rec n1 e1 (close_body_wrt_exp_rec n1 x1 body1)) /\
(forall e1 e2 x1 n1,
  subst_var_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_spec_rec :
forall body1 e1 x1 n1,
  subst_var_in_body e1 x1 body1 = open_body_wrt_exp_rec n1 e1 (close_body_wrt_exp_rec n1 x1 body1).
Proof.
pose proof subst_var_in_body_spec_rec_subst_var_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_var_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_var_in_body_spec_rec_subst_var_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_spec_rec_subst_tvar_in_contd_spec_rec_mutual :
(forall c1 A1 X1 n1,
  subst_tvar_in_cont A1 X1 c1 = open_cont_wrt_typ_rec n1 A1 (close_cont_wrt_typ_rec n1 X1 c1)) /\
(forall cc1 A1 X1 n1,
  subst_tvar_in_contd A1 X1 cc1 = open_contd_wrt_typ_rec n1 A1 (close_contd_wrt_typ_rec n1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_spec_rec :
forall c1 A1 X1 n1,
  subst_tvar_in_cont A1 X1 c1 = open_cont_wrt_typ_rec n1 A1 (close_cont_wrt_typ_rec n1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_spec_rec_subst_tvar_in_contd_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_contd_spec_rec :
forall cc1 A1 X1 n1,
  subst_tvar_in_contd A1 X1 cc1 = open_contd_wrt_typ_rec n1 A1 (close_contd_wrt_typ_rec n1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_spec_rec_subst_tvar_in_contd_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_spec_rec_subst_var_in_contd_spec_rec_mutual :
(forall c1 e1 x1 n1,
  subst_var_in_cont e1 x1 c1 = open_cont_wrt_exp_rec n1 e1 (close_cont_wrt_exp_rec n1 x1 c1)) /\
(forall cc1 e1 x1 n1,
  subst_var_in_contd e1 x1 cc1 = open_contd_wrt_exp_rec n1 e1 (close_contd_wrt_exp_rec n1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_spec_rec :
forall c1 e1 x1 n1,
  subst_var_in_cont e1 x1 c1 = open_cont_wrt_exp_rec n1 e1 (close_cont_wrt_exp_rec n1 x1 c1).
Proof.
pose proof subst_var_in_cont_spec_rec_subst_var_in_contd_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_contd_spec_rec :
forall cc1 e1 x1 n1,
  subst_var_in_contd e1 x1 cc1 = open_contd_wrt_exp_rec n1 e1 (close_contd_wrt_exp_rec n1 x1 cc1).
Proof.
pose proof subst_var_in_cont_spec_rec_subst_var_in_contd_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_dbind_spec_rec_mutual :
(forall db1 A1 X1 n1,
  subst_tvar_in_dbind A1 X1 db1 = open_dbind_wrt_typ_rec n1 A1 (close_dbind_wrt_typ_rec n1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_dbind_spec_rec :
forall db1 A1 X1 n1,
  subst_tvar_in_dbind A1 X1 db1 = open_dbind_wrt_typ_rec n1 A1 (close_dbind_wrt_typ_rec n1 X1 db1).
Proof.
pose proof subst_tvar_in_dbind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_spec_rec_mutual :
(forall w1 A1 X1 n1,
  subst_tvar_in_work A1 X1 w1 = open_work_wrt_typ_rec n1 A1 (close_work_wrt_typ_rec n1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_spec_rec :
forall w1 A1 X1 n1,
  subst_tvar_in_work A1 X1 w1 = open_work_wrt_typ_rec n1 A1 (close_work_wrt_typ_rec n1 X1 w1).
Proof.
pose proof subst_tvar_in_work_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_spec_rec_mutual :
(forall w1 e1 x1 n1,
  subst_var_in_work e1 x1 w1 = open_work_wrt_exp_rec n1 e1 (close_work_wrt_exp_rec n1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_spec_rec :
forall w1 e1 x1 n1,
  subst_var_in_work e1 x1 w1 = open_work_wrt_exp_rec n1 e1 (close_work_wrt_exp_rec n1 x1 w1).
Proof.
pose proof subst_var_in_work_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_spec_rec : lngen.

(* end hide *)

Lemma subst_tvar_in_typ_spec :
forall A1 A2 X1,
  subst_tvar_in_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_spec : lngen.

Lemma subst_tvar_in_abind_spec :
forall ab1 A1 X1,
  subst_tvar_in_abind A1 X1 ab1 = open_abind_wrt_typ (close_abind_wrt_typ X1 ab1) A1.
Proof.
unfold close_abind_wrt_typ; unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_spec : lngen.

Lemma subst_tvar_in_body_spec :
forall body1 A1 X1,
  subst_tvar_in_body A1 X1 body1 = open_body_wrt_typ (close_body_wrt_typ X1 body1) A1.
Proof.
unfold close_body_wrt_typ; unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_spec : lngen.

Lemma subst_tvar_in_exp_spec :
forall e1 A1 X1,
  subst_tvar_in_exp A1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) A1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_spec : lngen.

Lemma subst_var_in_body_spec :
forall body1 e1 x1,
  subst_var_in_body e1 x1 body1 = open_body_wrt_exp (close_body_wrt_exp x1 body1) e1.
Proof.
unfold close_body_wrt_exp; unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_spec : lngen.

Lemma subst_var_in_exp_spec :
forall e1 e2 x1,
  subst_var_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_spec : lngen.

Lemma subst_tvar_in_cont_spec :
forall c1 A1 X1,
  subst_tvar_in_cont A1 X1 c1 = open_cont_wrt_typ (close_cont_wrt_typ X1 c1) A1.
Proof.
unfold close_cont_wrt_typ; unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_spec : lngen.

Lemma subst_tvar_in_contd_spec :
forall cc1 A1 X1,
  subst_tvar_in_contd A1 X1 cc1 = open_contd_wrt_typ (close_contd_wrt_typ X1 cc1) A1.
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_spec : lngen.

Lemma subst_var_in_cont_spec :
forall c1 e1 x1,
  subst_var_in_cont e1 x1 c1 = open_cont_wrt_exp (close_cont_wrt_exp x1 c1) e1.
Proof.
unfold close_cont_wrt_exp; unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_spec : lngen.

Lemma subst_var_in_contd_spec :
forall cc1 e1 x1,
  subst_var_in_contd e1 x1 cc1 = open_contd_wrt_exp (close_contd_wrt_exp x1 cc1) e1.
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_spec : lngen.

Lemma subst_tvar_in_dbind_spec :
forall db1 A1 X1,
  subst_tvar_in_dbind A1 X1 db1 = open_dbind_wrt_typ (close_dbind_wrt_typ X1 db1) A1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_spec : lngen.

Lemma subst_tvar_in_work_spec :
forall w1 A1 X1,
  subst_tvar_in_work A1 X1 w1 = open_work_wrt_typ (close_work_wrt_typ X1 w1) A1.
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_spec : lngen.

Lemma subst_var_in_work_spec :
forall w1 e1 x1,
  subst_var_in_work e1 x1 w1 = open_work_wrt_exp (close_work_wrt_exp x1 w1) e1.
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_spec : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_subst_tvar_in_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_tvar_in_typ A2 X1 (subst_tvar_in_typ A3 X2 A1) = subst_tvar_in_typ (subst_tvar_in_typ A2 X1 A3) X2 (subst_tvar_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_subst_tvar_in_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_tvar_in_typ A2 X1 (subst_tvar_in_typ A3 X2 A1) = subst_tvar_in_typ (subst_tvar_in_typ A2 X1 A3) X2 (subst_tvar_in_typ A2 X1 A1).
Proof.
pose proof subst_tvar_in_typ_subst_tvar_in_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_subst_tvar_in_typ : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_subst_tvar_in_abind_mutual :
(forall ab1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_abind A1 X1 (subst_tvar_in_abind A2 X2 ab1) = subst_tvar_in_abind (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_subst_tvar_in_abind :
forall ab1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_abind A1 X1 (subst_tvar_in_abind A2 X2 ab1) = subst_tvar_in_abind (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_abind A1 X1 ab1).
Proof.
pose proof subst_tvar_in_abind_subst_tvar_in_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_subst_tvar_in_abind : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_subst_tvar_in_body_subst_tvar_in_exp_subst_tvar_in_exp_mutual :
(forall body1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_body A1 X1 (subst_tvar_in_body A2 X2 body1) = subst_tvar_in_body (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_exp A1 X1 (subst_tvar_in_exp A2 X2 e1) = subst_tvar_in_exp (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_subst_tvar_in_body :
forall body1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_body A1 X1 (subst_tvar_in_body A2 X2 body1) = subst_tvar_in_body (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_subst_tvar_in_body_subst_tvar_in_exp_subst_tvar_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_subst_tvar_in_body : lngen.

Lemma subst_tvar_in_exp_subst_tvar_in_exp :
forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_exp A1 X1 (subst_tvar_in_exp A2 X2 e1) = subst_tvar_in_exp (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_subst_tvar_in_body_subst_tvar_in_exp_subst_tvar_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_subst_tvar_in_exp : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_subst_var_in_body_subst_tvar_in_exp_subst_var_in_exp_mutual :
(forall body1 A1 e1 x1 X1,
  subst_tvar_in_body A1 X1 (subst_var_in_body e1 x1 body1) = subst_var_in_body (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_body A1 X1 body1)) /\
(forall e1 A1 e2 x1 X1,
  subst_tvar_in_exp A1 X1 (subst_var_in_exp e2 x1 e1) = subst_var_in_exp (subst_tvar_in_exp A1 X1 e2) x1 (subst_tvar_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_subst_var_in_body :
forall body1 A1 e1 x1 X1,
  subst_tvar_in_body A1 X1 (subst_var_in_body e1 x1 body1) = subst_var_in_body (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_body A1 X1 body1).
Proof.
pose proof subst_tvar_in_body_subst_var_in_body_subst_tvar_in_exp_subst_var_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_subst_var_in_body : lngen.

Lemma subst_tvar_in_exp_subst_var_in_exp :
forall e1 A1 e2 x1 X1,
  subst_tvar_in_exp A1 X1 (subst_var_in_exp e2 x1 e1) = subst_var_in_exp (subst_tvar_in_exp A1 X1 e2) x1 (subst_tvar_in_exp A1 X1 e1).
Proof.
pose proof subst_tvar_in_body_subst_var_in_body_subst_tvar_in_exp_subst_var_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_subst_var_in_exp : lngen.

(* begin hide *)

Lemma subst_var_in_body_subst_tvar_in_body_subst_var_in_exp_subst_tvar_in_exp_mutual :
(forall body1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_body e1 x1 (subst_tvar_in_body A1 X1 body1) = subst_tvar_in_body A1 X1 (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_var_in_exp e2 x1 (subst_tvar_in_exp A1 X1 e1) = subst_tvar_in_exp A1 X1 (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_subst_tvar_in_body :
forall body1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_body e1 x1 (subst_tvar_in_body A1 X1 body1) = subst_tvar_in_body A1 X1 (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_subst_tvar_in_body_subst_var_in_exp_subst_tvar_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_subst_tvar_in_body : lngen.

Lemma subst_var_in_exp_subst_tvar_in_exp :
forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_var_in_exp e2 x1 (subst_tvar_in_exp A1 X1 e1) = subst_tvar_in_exp A1 X1 (subst_var_in_exp e2 x1 e1).
Proof.
pose proof subst_var_in_body_subst_tvar_in_body_subst_var_in_exp_subst_tvar_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_subst_tvar_in_exp : lngen.

(* begin hide *)

Lemma subst_var_in_body_subst_var_in_body_subst_var_in_exp_subst_var_in_exp_mutual :
(forall body1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_body e1 x1 (subst_var_in_body e2 x2 body1) = subst_var_in_body (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_body e1 x1 body1)) /\
(forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_exp e2 ->
  x2 <> x1 ->
  subst_var_in_exp e2 x1 (subst_var_in_exp e3 x2 e1) = subst_var_in_exp (subst_var_in_exp e2 x1 e3) x2 (subst_var_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_subst_var_in_body :
forall body1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_body e1 x1 (subst_var_in_body e2 x2 body1) = subst_var_in_body (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_body e1 x1 body1).
Proof.
pose proof subst_var_in_body_subst_var_in_body_subst_var_in_exp_subst_var_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_subst_var_in_body : lngen.

Lemma subst_var_in_exp_subst_var_in_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_exp e2 ->
  x2 <> x1 ->
  subst_var_in_exp e2 x1 (subst_var_in_exp e3 x2 e1) = subst_var_in_exp (subst_var_in_exp e2 x1 e3) x2 (subst_var_in_exp e2 x1 e1).
Proof.
pose proof subst_var_in_body_subst_var_in_body_subst_var_in_exp_subst_var_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_subst_var_in_exp : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_subst_tvar_in_cont_subst_tvar_in_contd_subst_tvar_in_contd_mutual :
(forall c1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_cont A1 X1 (subst_tvar_in_cont A2 X2 c1) = subst_tvar_in_cont (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_contd A1 X1 (subst_tvar_in_contd A2 X2 cc1) = subst_tvar_in_contd (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_subst_tvar_in_cont :
forall c1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_cont A1 X1 (subst_tvar_in_cont A2 X2 c1) = subst_tvar_in_cont (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_subst_tvar_in_cont_subst_tvar_in_contd_subst_tvar_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_subst_tvar_in_cont : lngen.

Lemma subst_tvar_in_contd_subst_tvar_in_contd :
forall cc1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_contd A1 X1 (subst_tvar_in_contd A2 X2 cc1) = subst_tvar_in_contd (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_subst_tvar_in_cont_subst_tvar_in_contd_subst_tvar_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_subst_tvar_in_contd : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_subst_var_in_cont_subst_tvar_in_contd_subst_var_in_contd_mutual :
(forall c1 A1 e1 x1 X1,
  subst_tvar_in_cont A1 X1 (subst_var_in_cont e1 x1 c1) = subst_var_in_cont (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_cont A1 X1 c1)) /\
(forall cc1 A1 e1 x1 X1,
  subst_tvar_in_contd A1 X1 (subst_var_in_contd e1 x1 cc1) = subst_var_in_contd (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_contd A1 X1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_subst_var_in_cont :
forall c1 A1 e1 x1 X1,
  subst_tvar_in_cont A1 X1 (subst_var_in_cont e1 x1 c1) = subst_var_in_cont (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_cont A1 X1 c1).
Proof.
pose proof subst_tvar_in_cont_subst_var_in_cont_subst_tvar_in_contd_subst_var_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_subst_var_in_cont : lngen.

Lemma subst_tvar_in_contd_subst_var_in_contd :
forall cc1 A1 e1 x1 X1,
  subst_tvar_in_contd A1 X1 (subst_var_in_contd e1 x1 cc1) = subst_var_in_contd (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_contd A1 X1 cc1).
Proof.
pose proof subst_tvar_in_cont_subst_var_in_cont_subst_tvar_in_contd_subst_var_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_subst_var_in_contd : lngen.

(* begin hide *)

Lemma subst_var_in_cont_subst_tvar_in_cont_subst_var_in_contd_subst_tvar_in_contd_mutual :
(forall c1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_cont e1 x1 (subst_tvar_in_cont A1 X1 c1) = subst_tvar_in_cont A1 X1 (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_contd e1 x1 (subst_tvar_in_contd A1 X1 cc1) = subst_tvar_in_contd A1 X1 (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_subst_tvar_in_cont :
forall c1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_cont e1 x1 (subst_tvar_in_cont A1 X1 c1) = subst_tvar_in_cont A1 X1 (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_subst_tvar_in_cont_subst_var_in_contd_subst_tvar_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_subst_tvar_in_cont : lngen.

Lemma subst_var_in_contd_subst_tvar_in_contd :
forall cc1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_contd e1 x1 (subst_tvar_in_contd A1 X1 cc1) = subst_tvar_in_contd A1 X1 (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_subst_tvar_in_cont_subst_var_in_contd_subst_tvar_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_subst_tvar_in_contd : lngen.

(* begin hide *)

Lemma subst_var_in_cont_subst_var_in_cont_subst_var_in_contd_subst_var_in_contd_mutual :
(forall c1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_cont e1 x1 (subst_var_in_cont e2 x2 c1) = subst_var_in_cont (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_cont e1 x1 c1)) /\
(forall cc1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_contd e1 x1 (subst_var_in_contd e2 x2 cc1) = subst_var_in_contd (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_contd e1 x1 cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_subst_var_in_cont :
forall c1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_cont e1 x1 (subst_var_in_cont e2 x2 c1) = subst_var_in_cont (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_cont e1 x1 c1).
Proof.
pose proof subst_var_in_cont_subst_var_in_cont_subst_var_in_contd_subst_var_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_subst_var_in_cont : lngen.

Lemma subst_var_in_contd_subst_var_in_contd :
forall cc1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_contd e1 x1 (subst_var_in_contd e2 x2 cc1) = subst_var_in_contd (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_contd e1 x1 cc1).
Proof.
pose proof subst_var_in_cont_subst_var_in_cont_subst_var_in_contd_subst_var_in_contd_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_subst_var_in_contd : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_subst_tvar_in_dbind_mutual :
(forall db1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_dbind A1 X1 (subst_tvar_in_dbind A2 X2 db1) = subst_tvar_in_dbind (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_subst_tvar_in_dbind :
forall db1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_dbind A1 X1 (subst_tvar_in_dbind A2 X2 db1) = subst_tvar_in_dbind (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_dbind A1 X1 db1).
Proof.
pose proof subst_tvar_in_dbind_subst_tvar_in_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_subst_tvar_in_dbind : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_subst_tvar_in_work_mutual :
(forall w1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_work A1 X1 (subst_tvar_in_work A2 X2 w1) = subst_tvar_in_work (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_subst_tvar_in_work :
forall w1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_tvar_in_work A1 X1 (subst_tvar_in_work A2 X2 w1) = subst_tvar_in_work (subst_tvar_in_typ A1 X1 A2) X2 (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_subst_tvar_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_subst_tvar_in_work : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_subst_var_in_work_mutual :
(forall w1 A1 e1 x1 X1,
  subst_tvar_in_work A1 X1 (subst_var_in_work e1 x1 w1) = subst_var_in_work (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_subst_var_in_work :
forall w1 A1 e1 x1 X1,
  subst_tvar_in_work A1 X1 (subst_var_in_work e1 x1 w1) = subst_var_in_work (subst_tvar_in_exp A1 X1 e1) x1 (subst_tvar_in_work A1 X1 w1).
Proof.
pose proof subst_tvar_in_work_subst_var_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_subst_var_in_work : lngen.

(* begin hide *)

Lemma subst_var_in_work_subst_tvar_in_work_mutual :
(forall w1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_work e1 x1 (subst_tvar_in_work A1 X1 w1) = subst_tvar_in_work A1 X1 (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_subst_tvar_in_work :
forall w1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_var_in_work e1 x1 (subst_tvar_in_work A1 X1 w1) = subst_tvar_in_work A1 X1 (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_subst_tvar_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_subst_tvar_in_work : lngen.

(* begin hide *)

Lemma subst_var_in_work_subst_var_in_work_mutual :
(forall w1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_work e1 x1 (subst_var_in_work e2 x2 w1) = subst_var_in_work (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_subst_var_in_work :
forall w1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_var_in_work e1 x1 (subst_var_in_work e2 x2 w1) = subst_var_in_work (subst_var_in_exp e1 x1 e2) x2 (subst_var_in_work e1 x1 w1).
Proof.
pose proof subst_var_in_work_subst_var_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_subst_var_in_work : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2)).
Proof.
pose proof subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec_mutual :
(forall ab1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_abind A1 X1 ab1 = close_abind_wrt_typ_rec n1 X2 (subst_tvar_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X2) ab1))).
Proof.
apply_mutual_ind abind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec :
forall ab1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_abind A1 X1 ab1 = close_abind_wrt_typ_rec n1 X2 (subst_tvar_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X2) ab1)).
Proof.
pose proof subst_tvar_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec_subst_tvar_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall body1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_body body1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_body A1 X1 body1 = close_body_wrt_typ_rec n1 X2 (subst_tvar_in_body A1 X1 (open_body_wrt_typ_rec n1 (typ_var_f X2) body1))) *
(forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_tvar_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1))).
Proof.
apply_mutual_ind body_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec :
forall body1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_body body1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_body A1 X1 body1 = close_body_wrt_typ_rec n1 X2 (subst_tvar_in_body A1 X1 (open_body_wrt_typ_rec n1 (typ_var_f X2) body1)).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec_subst_tvar_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_tvar_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1)).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec_subst_tvar_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec_subst_tvar_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall body1 A1 X1 x1 n1,
  x1 `notin` fvar_in_body body1 ->
  subst_tvar_in_body A1 X1 body1 = close_body_wrt_exp_rec n1 x1 (subst_tvar_in_body A1 X1 (open_body_wrt_exp_rec n1 (exp_var_f x1) body1))) *
(forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_tvar_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_tvar_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind body_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec :
forall body1 A1 X1 x1 n1,
  x1 `notin` fvar_in_body body1 ->
  subst_tvar_in_body A1 X1 body1 = close_body_wrt_exp_rec n1 x1 (subst_tvar_in_body A1 X1 (open_body_wrt_exp_rec n1 (exp_var_f x1) body1)).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec_subst_tvar_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_tvar_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_tvar_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_tvar_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec_subst_tvar_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec_subst_var_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall body1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_body e1 x1 body1 = close_body_wrt_typ_rec n1 X1 (subst_var_in_body e1 x1 (open_body_wrt_typ_rec n1 (typ_var_f X1) body1))) *
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_var_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2))).
Proof.
apply_mutual_ind body_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec :
forall body1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_body e1 x1 body1 = close_body_wrt_typ_rec n1 X1 (subst_var_in_body e1 x1 (open_body_wrt_typ_rec n1 (typ_var_f X1) body1)).
Proof.
pose proof subst_var_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec_subst_var_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_var_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2)).
Proof.
pose proof subst_var_in_body_close_body_wrt_typ_rec_open_body_wrt_typ_rec_subst_var_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec_subst_var_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall body1 e1 x1 x2 n1,
  x2 `notin` fvar_in_body body1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_body e1 x1 body1 = close_body_wrt_exp_rec n1 x2 (subst_var_in_body e1 x1 (open_body_wrt_exp_rec n1 (exp_var_f x2) body1))) *
(forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_var_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind body_exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec :
forall body1 e1 x1 x2 n1,
  x2 `notin` fvar_in_body body1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_body e1 x1 body1 = close_body_wrt_exp_rec n1 x2 (subst_var_in_body e1 x1 (open_body_wrt_exp_rec n1 (exp_var_f x2) body1)).
Proof.
pose proof subst_var_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec_subst_var_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_var_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof subst_var_in_body_close_body_wrt_exp_rec_open_body_wrt_exp_rec_subst_var_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_subst_tvar_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual :
(forall c1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_cont c1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_cont A1 X1 c1 = close_cont_wrt_typ_rec n1 X2 (subst_tvar_in_cont A1 X1 (open_cont_wrt_typ_rec n1 (typ_var_f X2) c1))) *
(forall cc1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_contd cc1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_contd A1 X1 cc1 = close_contd_wrt_typ_rec n1 X2 (subst_tvar_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X2) cc1))).
Proof.
apply_mutual_ind cont_contd_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec :
forall c1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_cont c1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_cont A1 X1 c1 = close_cont_wrt_typ_rec n1 X2 (subst_tvar_in_cont A1 X1 (open_cont_wrt_typ_rec n1 (typ_var_f X2) c1)).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_subst_tvar_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec :
forall cc1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_contd cc1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_contd A1 X1 cc1 = close_contd_wrt_typ_rec n1 X2 (subst_tvar_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X2) cc1)).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_subst_tvar_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_subst_tvar_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual :
(forall c1 A1 X1 x1 n1,
  x1 `notin` fvar_in_cont c1 ->
  subst_tvar_in_cont A1 X1 c1 = close_cont_wrt_exp_rec n1 x1 (subst_tvar_in_cont A1 X1 (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1))) *
(forall cc1 A1 X1 x1 n1,
  x1 `notin` fvar_in_contd cc1 ->
  subst_tvar_in_contd A1 X1 cc1 = close_contd_wrt_exp_rec n1 x1 (subst_tvar_in_contd A1 X1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1))).
Proof.
apply_mutual_ind cont_contd_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec :
forall c1 A1 X1 x1 n1,
  x1 `notin` fvar_in_cont c1 ->
  subst_tvar_in_cont A1 X1 c1 = close_cont_wrt_exp_rec n1 x1 (subst_tvar_in_cont A1 X1 (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1)).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_subst_tvar_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec :
forall cc1 A1 X1 x1 n1,
  x1 `notin` fvar_in_contd cc1 ->
  subst_tvar_in_contd A1 X1 cc1 = close_contd_wrt_exp_rec n1 x1 (subst_tvar_in_contd A1 X1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1)).
Proof.
pose proof subst_tvar_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_subst_tvar_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_subst_var_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual :
(forall c1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_cont e1 x1 c1 = close_cont_wrt_typ_rec n1 X1 (subst_var_in_cont e1 x1 (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1))) *
(forall cc1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_contd e1 x1 cc1 = close_contd_wrt_typ_rec n1 X1 (subst_var_in_contd e1 x1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1))).
Proof.
apply_mutual_ind cont_contd_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec :
forall c1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_cont e1 x1 c1 = close_cont_wrt_typ_rec n1 X1 (subst_var_in_cont e1 x1 (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1)).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_subst_var_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec :
forall cc1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_contd e1 x1 cc1 = close_contd_wrt_typ_rec n1 X1 (subst_var_in_contd e1 x1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1)).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_typ_rec_open_cont_wrt_typ_rec_subst_var_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_subst_var_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual :
(forall c1 e1 x1 x2 n1,
  x2 `notin` fvar_in_cont c1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_cont e1 x1 c1 = close_cont_wrt_exp_rec n1 x2 (subst_var_in_cont e1 x1 (open_cont_wrt_exp_rec n1 (exp_var_f x2) c1))) *
(forall cc1 e1 x1 x2 n1,
  x2 `notin` fvar_in_contd cc1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_contd e1 x1 cc1 = close_contd_wrt_exp_rec n1 x2 (subst_var_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x2) cc1))).
Proof.
apply_mutual_ind cont_contd_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec :
forall c1 e1 x1 x2 n1,
  x2 `notin` fvar_in_cont c1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_cont e1 x1 c1 = close_cont_wrt_exp_rec n1 x2 (subst_var_in_cont e1 x1 (open_cont_wrt_exp_rec n1 (exp_var_f x2) c1)).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_subst_var_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec :
forall cc1 e1 x1 x2 n1,
  x2 `notin` fvar_in_contd cc1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_contd e1 x1 cc1 = close_contd_wrt_exp_rec n1 x2 (subst_var_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x2) cc1)).
Proof.
pose proof subst_var_in_cont_close_cont_wrt_exp_rec_open_cont_wrt_exp_rec_subst_var_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_dbind A1 X1 db1 = close_dbind_wrt_typ_rec n1 X2 (subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X2) db1))).
Proof.
apply_mutual_ind dbind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec :
forall db1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_dbind A1 X1 db1 = close_dbind_wrt_typ_rec n1 X2 (subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X2) db1)).
Proof.
pose proof subst_tvar_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual :
(forall w1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_work A1 X1 w1 = close_work_wrt_typ_rec n1 X2 (subst_tvar_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X2) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec :
forall w1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tvar_in_work A1 X1 w1 = close_work_wrt_typ_rec n1 X2 (subst_tvar_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X2) w1)).
Proof.
pose proof subst_tvar_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual :
(forall w1 A1 X1 x1 n1,
  x1 `notin` fvar_in_work w1 ->
  subst_tvar_in_work A1 X1 w1 = close_work_wrt_exp_rec n1 x1 (subst_tvar_in_work A1 X1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_tvar_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec :
forall w1 A1 X1 x1 n1,
  x1 `notin` fvar_in_work w1 ->
  subst_tvar_in_work A1 X1 w1 = close_work_wrt_exp_rec n1 x1 (subst_tvar_in_work A1 X1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1)).
Proof.
pose proof subst_tvar_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual :
(forall w1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_work e1 x1 w1 = close_work_wrt_typ_rec n1 X1 (subst_var_in_work e1 x1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec :
forall w1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_var_in_work e1 x1 w1 = close_work_wrt_typ_rec n1 X1 (subst_var_in_work e1 x1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1)).
Proof.
pose proof subst_var_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual :
(forall w1 e1 x1 x2 n1,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_work e1 x1 w1 = close_work_wrt_exp_rec n1 x2 (subst_var_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x2) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_var_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec :
forall w1 e1 x1 x2 n1,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_var_in_work e1 x1 w1 = close_work_wrt_exp_rec n1 x2 (subst_var_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x2) w1)).
Proof.
pose proof subst_var_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_tvar_in_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_typ A1 X1 A2 = close_typ_wrt_typ X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_tvar_in_abind_close_abind_wrt_typ_open_abind_wrt_typ :
forall ab1 A1 X1 X2,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_abind A1 X1 ab1 = close_abind_wrt_typ X2 (subst_tvar_in_abind A1 X1 (open_abind_wrt_typ ab1 (typ_var_f X2))).
Proof.
unfold close_abind_wrt_typ; unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_close_abind_wrt_typ_open_abind_wrt_typ : lngen.

Lemma subst_tvar_in_body_close_body_wrt_typ_open_body_wrt_typ :
forall body1 A1 X1 X2,
  X2 `notin` ftvar_in_body body1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_body A1 X1 body1 = close_body_wrt_typ X2 (subst_tvar_in_body A1 X1 (open_body_wrt_typ body1 (typ_var_f X2))).
Proof.
unfold close_body_wrt_typ; unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_typ_open_body_wrt_typ : lngen.

Lemma subst_tvar_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_exp A1 X1 e1 = close_exp_wrt_typ X2 (subst_tvar_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_tvar_in_body_close_body_wrt_exp_open_body_wrt_exp :
forall body1 A1 X1 x1,
  x1 `notin` fvar_in_body body1 ->
  lc_typ A1 ->
  subst_tvar_in_body A1 X1 body1 = close_body_wrt_exp x1 (subst_tvar_in_body A1 X1 (open_body_wrt_exp body1 (exp_var_f x1))).
Proof.
unfold close_body_wrt_exp; unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_close_body_wrt_exp_open_body_wrt_exp : lngen.

Lemma subst_tvar_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  lc_typ A1 ->
  subst_tvar_in_exp A1 X1 e1 = close_exp_wrt_exp x1 (subst_tvar_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_var_in_body_close_body_wrt_typ_open_body_wrt_typ :
forall body1 e1 x1 X1,
  X1 `notin` ftvar_in_body body1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_var_in_body e1 x1 body1 = close_body_wrt_typ X1 (subst_var_in_body e1 x1 (open_body_wrt_typ body1 (typ_var_f X1))).
Proof.
unfold close_body_wrt_typ; unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_typ_open_body_wrt_typ : lngen.

Lemma subst_var_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_var_in_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_var_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_var_in_body_close_body_wrt_exp_open_body_wrt_exp :
forall body1 e1 x1 x2,
  x2 `notin` fvar_in_body body1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_var_in_body e1 x1 body1 = close_body_wrt_exp x2 (subst_var_in_body e1 x1 (open_body_wrt_exp body1 (exp_var_f x2))).
Proof.
unfold close_body_wrt_exp; unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_close_body_wrt_exp_open_body_wrt_exp : lngen.

Lemma subst_var_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_var_in_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_var_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_tvar_in_cont_close_cont_wrt_typ_open_cont_wrt_typ :
forall c1 A1 X1 X2,
  X2 `notin` ftvar_in_cont c1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_cont A1 X1 c1 = close_cont_wrt_typ X2 (subst_tvar_in_cont A1 X1 (open_cont_wrt_typ c1 (typ_var_f X2))).
Proof.
unfold close_cont_wrt_typ; unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_typ_open_cont_wrt_typ : lngen.

Lemma subst_tvar_in_contd_close_contd_wrt_typ_open_contd_wrt_typ :
forall cc1 A1 X1 X2,
  X2 `notin` ftvar_in_contd cc1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_contd A1 X1 cc1 = close_contd_wrt_typ X2 (subst_tvar_in_contd A1 X1 (open_contd_wrt_typ cc1 (typ_var_f X2))).
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_typ_open_contd_wrt_typ : lngen.

Lemma subst_tvar_in_cont_close_cont_wrt_exp_open_cont_wrt_exp :
forall c1 A1 X1 x1,
  x1 `notin` fvar_in_cont c1 ->
  lc_typ A1 ->
  subst_tvar_in_cont A1 X1 c1 = close_cont_wrt_exp x1 (subst_tvar_in_cont A1 X1 (open_cont_wrt_exp c1 (exp_var_f x1))).
Proof.
unfold close_cont_wrt_exp; unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_close_cont_wrt_exp_open_cont_wrt_exp : lngen.

Lemma subst_tvar_in_contd_close_contd_wrt_exp_open_contd_wrt_exp :
forall cc1 A1 X1 x1,
  x1 `notin` fvar_in_contd cc1 ->
  lc_typ A1 ->
  subst_tvar_in_contd A1 X1 cc1 = close_contd_wrt_exp x1 (subst_tvar_in_contd A1 X1 (open_contd_wrt_exp cc1 (exp_var_f x1))).
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_close_contd_wrt_exp_open_contd_wrt_exp : lngen.

Lemma subst_var_in_cont_close_cont_wrt_typ_open_cont_wrt_typ :
forall c1 e1 x1 X1,
  X1 `notin` ftvar_in_cont c1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_var_in_cont e1 x1 c1 = close_cont_wrt_typ X1 (subst_var_in_cont e1 x1 (open_cont_wrt_typ c1 (typ_var_f X1))).
Proof.
unfold close_cont_wrt_typ; unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_typ_open_cont_wrt_typ : lngen.

Lemma subst_var_in_contd_close_contd_wrt_typ_open_contd_wrt_typ :
forall cc1 e1 x1 X1,
  X1 `notin` ftvar_in_contd cc1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_var_in_contd e1 x1 cc1 = close_contd_wrt_typ X1 (subst_var_in_contd e1 x1 (open_contd_wrt_typ cc1 (typ_var_f X1))).
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_typ_open_contd_wrt_typ : lngen.

Lemma subst_var_in_cont_close_cont_wrt_exp_open_cont_wrt_exp :
forall c1 e1 x1 x2,
  x2 `notin` fvar_in_cont c1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_var_in_cont e1 x1 c1 = close_cont_wrt_exp x2 (subst_var_in_cont e1 x1 (open_cont_wrt_exp c1 (exp_var_f x2))).
Proof.
unfold close_cont_wrt_exp; unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_close_cont_wrt_exp_open_cont_wrt_exp : lngen.

Lemma subst_var_in_contd_close_contd_wrt_exp_open_contd_wrt_exp :
forall cc1 e1 x1 x2,
  x2 `notin` fvar_in_contd cc1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_var_in_contd e1 x1 cc1 = close_contd_wrt_exp x2 (subst_var_in_contd e1 x1 (open_contd_wrt_exp cc1 (exp_var_f x2))).
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_close_contd_wrt_exp_open_contd_wrt_exp : lngen.

Lemma subst_tvar_in_dbind_close_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_dbind A1 X1 db1 = close_dbind_wrt_typ X2 (subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X2))).
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_close_dbind_wrt_typ_open_dbind_wrt_typ : lngen.

Lemma subst_tvar_in_work_close_work_wrt_typ_open_work_wrt_typ :
forall w1 A1 X1 X2,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_tvar_in_work A1 X1 w1 = close_work_wrt_typ X2 (subst_tvar_in_work A1 X1 (open_work_wrt_typ w1 (typ_var_f X2))).
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_typ_open_work_wrt_typ : lngen.

Lemma subst_tvar_in_work_close_work_wrt_exp_open_work_wrt_exp :
forall w1 A1 X1 x1,
  x1 `notin` fvar_in_work w1 ->
  lc_typ A1 ->
  subst_tvar_in_work A1 X1 w1 = close_work_wrt_exp x1 (subst_tvar_in_work A1 X1 (open_work_wrt_exp w1 (exp_var_f x1))).
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_close_work_wrt_exp_open_work_wrt_exp : lngen.

Lemma subst_var_in_work_close_work_wrt_typ_open_work_wrt_typ :
forall w1 e1 x1 X1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_var_in_work e1 x1 w1 = close_work_wrt_typ X1 (subst_var_in_work e1 x1 (open_work_wrt_typ w1 (typ_var_f X1))).
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_typ_open_work_wrt_typ : lngen.

Lemma subst_var_in_work_close_work_wrt_exp_open_work_wrt_exp :
forall w1 e1 x1 x2,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_var_in_work e1 x1 w1 = close_work_wrt_exp x2 (subst_var_in_work e1 x1 (open_work_wrt_exp w1 (exp_var_f x2))).
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_close_work_wrt_exp_open_work_wrt_exp : lngen.

Lemma subst_tvar_in_typ_typ_all :
forall X2 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_typ A2 `union` singleton X1 ->
  subst_tvar_in_typ A1 X1 (typ_all A2) = typ_all (close_typ_wrt_typ X2 (subst_tvar_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_typ_all : lngen.

Lemma subst_tvar_in_exp_exp_abs :
forall x1 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_tvar_in_exp A1 X1 (exp_abs e1) = exp_abs (close_exp_wrt_exp x1 (subst_tvar_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_exp_abs : lngen.

Lemma subst_tvar_in_exp_exp_tabs :
forall X2 body1 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_body body1 `union` singleton X1 ->
  subst_tvar_in_exp A1 X1 (exp_tabs body1) = exp_tabs (close_body_wrt_typ X2 (subst_tvar_in_body A1 X1 (open_body_wrt_typ body1 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_exp_tabs : lngen.

Lemma subst_var_in_exp_exp_abs :
forall x2 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fvar_in_exp e1 `union` fvar_in_exp e2 `union` singleton x1 ->
  subst_var_in_exp e1 x1 (exp_abs e2) = exp_abs (close_exp_wrt_exp x2 (subst_var_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_exp_abs : lngen.

Lemma subst_var_in_exp_exp_tabs :
forall X1 body1 e1 x1,
  lc_exp e1 ->
  X1 `notin` ftvar_in_exp e1 `union` ftvar_in_body body1 ->
  subst_var_in_exp e1 x1 (exp_tabs body1) = exp_tabs (close_body_wrt_typ X1 (subst_var_in_body e1 x1 (open_body_wrt_typ body1 (typ_var_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_exp_tabs : lngen.

(* begin hide *)

Lemma subst_tvar_in_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_tvar_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_tvar_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1).
Proof.
pose proof subst_tvar_in_typ_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_abind_intro_rec_mutual :
(forall ab1 X1 A1 n1,
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ_rec n1 A1 ab1 = subst_tvar_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_abind_intro_rec :
forall ab1 X1 A1 n1,
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ_rec n1 A1 ab1 = subst_tvar_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1).
Proof.
pose proof subst_tvar_in_abind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_abind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_body_intro_rec_subst_tvar_in_exp_intro_rec_mutual :
(forall body1 X1 A1 n1,
  X1 `notin` ftvar_in_body body1 ->
  open_body_wrt_typ_rec n1 A1 body1 = subst_tvar_in_body A1 X1 (open_body_wrt_typ_rec n1 (typ_var_f X1) body1)) /\
(forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_tvar_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_body_intro_rec :
forall body1 X1 A1 n1,
  X1 `notin` ftvar_in_body body1 ->
  open_body_wrt_typ_rec n1 A1 body1 = subst_tvar_in_body A1 X1 (open_body_wrt_typ_rec n1 (typ_var_f X1) body1).
Proof.
pose proof subst_tvar_in_body_intro_rec_subst_tvar_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_body_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_body_intro_rec using solve [auto] : lngen.

Lemma subst_tvar_in_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_tvar_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1).
Proof.
pose proof subst_tvar_in_body_intro_rec_subst_tvar_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_in_body_intro_rec_subst_var_in_exp_intro_rec_mutual :
(forall body1 x1 e1 n1,
  x1 `notin` fvar_in_body body1 ->
  open_body_wrt_exp_rec n1 e1 body1 = subst_var_in_body e1 x1 (open_body_wrt_exp_rec n1 (exp_var_f x1) body1)) /\
(forall e1 x1 e2 n1,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_var_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind body_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_body_intro_rec :
forall body1 x1 e1 n1,
  x1 `notin` fvar_in_body body1 ->
  open_body_wrt_exp_rec n1 e1 body1 = subst_var_in_body e1 x1 (open_body_wrt_exp_rec n1 (exp_var_f x1) body1).
Proof.
pose proof subst_var_in_body_intro_rec_subst_var_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_body_intro_rec : lngen.
#[export] Hint Rewrite subst_var_in_body_intro_rec using solve [auto] : lngen.

Lemma subst_var_in_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_var_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof subst_var_in_body_intro_rec_subst_var_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_var_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_cont_intro_rec_subst_tvar_in_contd_intro_rec_mutual :
(forall c1 X1 A1 n1,
  X1 `notin` ftvar_in_cont c1 ->
  open_cont_wrt_typ_rec n1 A1 c1 = subst_tvar_in_cont A1 X1 (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1)) /\
(forall cc1 X1 A1 n1,
  X1 `notin` ftvar_in_contd cc1 ->
  open_contd_wrt_typ_rec n1 A1 cc1 = subst_tvar_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_cont_intro_rec :
forall c1 X1 A1 n1,
  X1 `notin` ftvar_in_cont c1 ->
  open_cont_wrt_typ_rec n1 A1 c1 = subst_tvar_in_cont A1 X1 (open_cont_wrt_typ_rec n1 (typ_var_f X1) c1).
Proof.
pose proof subst_tvar_in_cont_intro_rec_subst_tvar_in_contd_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_cont_intro_rec using solve [auto] : lngen.

Lemma subst_tvar_in_contd_intro_rec :
forall cc1 X1 A1 n1,
  X1 `notin` ftvar_in_contd cc1 ->
  open_contd_wrt_typ_rec n1 A1 cc1 = subst_tvar_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cc1).
Proof.
pose proof subst_tvar_in_cont_intro_rec_subst_tvar_in_contd_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_contd_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_in_cont_intro_rec_subst_var_in_contd_intro_rec_mutual :
(forall c1 x1 e1 n1,
  x1 `notin` fvar_in_cont c1 ->
  open_cont_wrt_exp_rec n1 e1 c1 = subst_var_in_cont e1 x1 (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1)) /\
(forall cc1 x1 e1 n1,
  x1 `notin` fvar_in_contd cc1 ->
  open_contd_wrt_exp_rec n1 e1 cc1 = subst_var_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1)).
Proof.
apply_mutual_ind cont_contd_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_cont_intro_rec :
forall c1 x1 e1 n1,
  x1 `notin` fvar_in_cont c1 ->
  open_cont_wrt_exp_rec n1 e1 c1 = subst_var_in_cont e1 x1 (open_cont_wrt_exp_rec n1 (exp_var_f x1) c1).
Proof.
pose proof subst_var_in_cont_intro_rec_subst_var_in_contd_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_cont_intro_rec : lngen.
#[export] Hint Rewrite subst_var_in_cont_intro_rec using solve [auto] : lngen.

Lemma subst_var_in_contd_intro_rec :
forall cc1 x1 e1 n1,
  x1 `notin` fvar_in_contd cc1 ->
  open_contd_wrt_exp_rec n1 e1 cc1 = subst_var_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cc1).
Proof.
pose proof subst_var_in_cont_intro_rec_subst_var_in_contd_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_contd_intro_rec : lngen.
#[export] Hint Rewrite subst_var_in_contd_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_dbind_intro_rec_mutual :
(forall db1 X1 A1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_dbind_intro_rec :
forall db1 X1 A1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1).
Proof.
pose proof subst_tvar_in_dbind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_dbind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_tvar_in_work_intro_rec_mutual :
(forall w1 X1 A1 n1,
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ_rec n1 A1 w1 = subst_tvar_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_tvar_in_work_intro_rec :
forall w1 X1 A1 n1,
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ_rec n1 A1 w1 = subst_tvar_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1).
Proof.
pose proof subst_tvar_in_work_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_tvar_in_work_intro_rec : lngen.
#[export] Hint Rewrite subst_tvar_in_work_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_var_in_work_intro_rec_mutual :
(forall w1 x1 e1 n1,
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp_rec n1 e1 w1 = subst_var_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_var_in_work_intro_rec :
forall w1 x1 e1 n1,
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp_rec n1 e1 w1 = subst_var_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1).
Proof.
pose proof subst_var_in_work_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_var_in_work_intro_rec : lngen.
#[export] Hint Rewrite subst_var_in_work_intro_rec using solve [auto] : lngen.

Lemma subst_tvar_in_typ_intro :
forall X1 A1 A2,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A1 A2 = subst_tvar_in_typ A2 X1 (open_typ_wrt_typ A1 (typ_var_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_typ_intro : lngen.

Lemma subst_tvar_in_abind_intro :
forall X1 ab1 A1,
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ ab1 A1 = subst_tvar_in_abind A1 X1 (open_abind_wrt_typ ab1 (typ_var_f X1)).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_abind_intro : lngen.

Lemma subst_tvar_in_body_intro :
forall X1 body1 A1,
  X1 `notin` ftvar_in_body body1 ->
  open_body_wrt_typ body1 A1 = subst_tvar_in_body A1 X1 (open_body_wrt_typ body1 (typ_var_f X1)).
Proof.
unfold open_body_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_body_intro : lngen.

Lemma subst_tvar_in_exp_intro :
forall X1 e1 A1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ e1 A1 = subst_tvar_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X1)).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_exp_intro : lngen.

Lemma subst_var_in_body_intro :
forall x1 body1 e1,
  x1 `notin` fvar_in_body body1 ->
  open_body_wrt_exp body1 e1 = subst_var_in_body e1 x1 (open_body_wrt_exp body1 (exp_var_f x1)).
Proof.
unfold open_body_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_body_intro : lngen.

Lemma subst_var_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_var_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_exp_intro : lngen.

Lemma subst_tvar_in_cont_intro :
forall X1 c1 A1,
  X1 `notin` ftvar_in_cont c1 ->
  open_cont_wrt_typ c1 A1 = subst_tvar_in_cont A1 X1 (open_cont_wrt_typ c1 (typ_var_f X1)).
Proof.
unfold open_cont_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_cont_intro : lngen.

Lemma subst_tvar_in_contd_intro :
forall X1 cc1 A1,
  X1 `notin` ftvar_in_contd cc1 ->
  open_contd_wrt_typ cc1 A1 = subst_tvar_in_contd A1 X1 (open_contd_wrt_typ cc1 (typ_var_f X1)).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_contd_intro : lngen.

Lemma subst_var_in_cont_intro :
forall x1 c1 e1,
  x1 `notin` fvar_in_cont c1 ->
  open_cont_wrt_exp c1 e1 = subst_var_in_cont e1 x1 (open_cont_wrt_exp c1 (exp_var_f x1)).
Proof.
unfold open_cont_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_cont_intro : lngen.

Lemma subst_var_in_contd_intro :
forall x1 cc1 e1,
  x1 `notin` fvar_in_contd cc1 ->
  open_contd_wrt_exp cc1 e1 = subst_var_in_contd e1 x1 (open_contd_wrt_exp cc1 (exp_var_f x1)).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_contd_intro : lngen.

Lemma subst_tvar_in_dbind_intro :
forall X1 db1 A1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ db1 A1 = subst_tvar_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X1)).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_dbind_intro : lngen.

Lemma subst_tvar_in_work_intro :
forall X1 w1 A1,
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ w1 A1 = subst_tvar_in_work A1 X1 (open_work_wrt_typ w1 (typ_var_f X1)).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_tvar_in_work_intro : lngen.

Lemma subst_var_in_work_intro :
forall x1 w1 e1,
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp w1 e1 = subst_var_in_work e1 x1 (open_work_wrt_exp w1 (exp_var_f x1)).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_var_in_work_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
