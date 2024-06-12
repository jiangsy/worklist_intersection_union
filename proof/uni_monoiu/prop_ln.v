Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export uni_monoiu.def_ott.

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

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Scheme contd_ind' := Induction for contd Sort Prop
  with conts_ind' := Induction for conts Sort Prop.

Combined Scheme contd_conts_mutind from contd_ind',conts_ind'.

Scheme contd_rec' := Induction for contd Sort Set
  with conts_rec' := Induction for conts Sort Set.

Combined Scheme contd_conts_mutrec from contd_rec',conts_rec'.

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
    | typ_label l1 => 1
  end.

Fixpoint size_abind (ab1 : abind) {struct ab1} : nat :=
  match ab1 with
    | abind_tvar_empty => 1
    | abind_stvar_empty => 1
    | abind_etvar_empty => 1
    | abind_var_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_unit => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_tabs e2 => 1 + (size_exp e2)
    | exp_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | exp_rcd_nil => 1
    | exp_rcd_cons l1 e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_rcd_proj e2 l1 => 1 + (size_exp e2)
  end.

Fixpoint size_contd (cd1 : contd) {struct cd1} : nat :=
  match cd1 with
    | contd_infabsunion A1 cd2 => 1 + (size_typ A1) + (size_contd cd2)
    | contd_infapp e1 cs1 => 1 + (size_exp e1) + (size_conts cs1)
    | contd_infproj A1 cs1 => 1 + (size_typ A1) + (size_conts cs1)
    | contd_unioninfabs A1 B1 cd2 => 1 + (size_typ A1) + (size_typ B1) + (size_contd cd2)
  end

with size_conts (cs1 : conts) {struct cs1} : nat :=
  match cs1 with
    | conts_infabs cd1 => 1 + (size_contd cd1)
    | conts_inftapp A1 cs2 => 1 + (size_typ A1) + (size_conts cs2)
    | conts_inftappunion A1 A2 cs2 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs2)
    | conts_unioninftapp A1 cs2 => 1 + (size_typ A1) + (size_conts cs2)
    | conts_infrcdconsintersection l1 e1 cs2 => 1 + (size_exp e1) + (size_conts cs2)
    | conts_intersectioninfrcdcons A1 cs2 => 1 + (size_typ A1) + (size_conts cs2)
    | conts_sub A1 => 1 + (size_typ A1)
  end.

Fixpoint size_dbind (db1 : dbind) {struct db1} : nat :=
  match db1 with
    | dbind_tvar_empty => 1
    | dbind_stvar_empty => 1
    | dbind_typ A1 => 1 + (size_typ A1)
  end.

Fixpoint size_work (w1 : work) {struct w1} : nat :=
  match w1 with
    | work_infer e1 cs1 => 1 + (size_exp e1) + (size_conts cs1)
    | work_check e1 A1 => 1 + (size_exp e1) + (size_typ A1)
    | work_infabs A1 cd1 => 1 + (size_typ A1) + (size_contd cd1)
    | work_infabsunion A1 B1 A2 cd1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ A2) + (size_contd cd1)
    | work_infapp A1 B1 e1 cs1 => 1 + (size_typ A1) + (size_typ B1) + (size_exp e1) + (size_conts cs1)
    | work_infproj A1 B1 C1 cs1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ C1) + (size_conts cs1)
    | work_infrcdconsintersection l1 A1 e1 cs1 => 1 + (size_typ A1) + (size_exp e1) + (size_conts cs1)
    | work_intersectioninfrcdcons A1 A2 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs1)
    | work_inftapp A1 A2 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs1)
    | work_sub A1 A2 => 1 + (size_typ A1) + (size_typ A2)
    | work_inftappunion A1 A2 B1 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_typ B1) + (size_conts cs1)
    | work_unioninftapp A1 A2 cs1 => 1 + (size_typ A1) + (size_typ A2) + (size_conts cs1)
    | work_unioninfabs A1 B1 A2 B2 cd1 => 1 + (size_typ A1) + (size_typ B1) + (size_typ A2) + (size_typ B2) + (size_contd cd1)
    | work_applys cs1 A1 => 1 + (size_conts cs1) + (size_typ A1)
    | work_applyd cd1 A1 B1 => 1 + (size_contd cd1) + (size_typ A1) + (size_typ B1)
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
    degree_typ_wrt_typ n1 (typ_intersection A1 A2)
  | degree_wrt_typ_typ_label : forall n1 l1,
    degree_typ_wrt_typ n1 (typ_label l1).

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

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
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
  | degree_wrt_typ_exp_tabs : forall n1 e1,
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (exp_tabs e1)
  | degree_wrt_typ_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_tapp e1 A1)
  | degree_wrt_typ_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_anno e1 A1)
  | degree_wrt_typ_exp_rcd_nil : forall n1,
    degree_exp_wrt_typ n1 (exp_rcd_nil)
  | degree_wrt_typ_exp_rcd_cons : forall n1 l1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_rcd_cons l1 e1 e2)
  | degree_wrt_typ_exp_rcd_proj : forall n1 e1 l1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_rcd_proj e1 l1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
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
  | degree_wrt_exp_exp_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tabs e1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 A1)
  | degree_wrt_exp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_anno e1 A1)
  | degree_wrt_exp_exp_rcd_nil : forall n1,
    degree_exp_wrt_exp n1 (exp_rcd_nil)
  | degree_wrt_exp_exp_rcd_cons : forall n1 l1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_rcd_cons l1 e1 e2)
  | degree_wrt_exp_exp_rcd_proj : forall n1 e1 l1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_rcd_proj e1 l1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_exp_wrt_typ_mutind from degree_exp_wrt_typ_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_exp_wrt_typ : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.

Inductive degree_contd_wrt_typ : nat -> contd -> Prop :=
  | degree_wrt_typ_contd_infabsunion : forall n1 A1 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_contd_wrt_typ n1 (contd_infabsunion A1 cd1)
  | degree_wrt_typ_contd_infapp : forall n1 e1 cs1,
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_contd_wrt_typ n1 (contd_infapp e1 cs1)
  | degree_wrt_typ_contd_infproj : forall n1 A1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_contd_wrt_typ n1 (contd_infproj A1 cs1)
  | degree_wrt_typ_contd_unioninfabs : forall n1 A1 B1 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_contd_wrt_typ n1 (contd_unioninfabs A1 B1 cd1)

with degree_conts_wrt_typ : nat -> conts -> Prop :=
  | degree_wrt_typ_conts_infabs : forall n1 cd1,
    degree_contd_wrt_typ n1 cd1 ->
    degree_conts_wrt_typ n1 (conts_infabs cd1)
  | degree_wrt_typ_conts_inftapp : forall n1 A1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_inftapp A1 cs1)
  | degree_wrt_typ_conts_inftappunion : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_inftappunion A1 A2 cs1)
  | degree_wrt_typ_conts_unioninftapp : forall n1 A1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_unioninftapp A1 cs1)
  | degree_wrt_typ_conts_infrcdconsintersection : forall n1 l1 e1 cs1,
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_infrcdconsintersection l1 e1 cs1)
  | degree_wrt_typ_conts_intersectioninfrcdcons : forall n1 A1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_conts_wrt_typ n1 (conts_intersectioninfrcdcons A1 cs1)
  | degree_wrt_typ_conts_sub : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_conts_wrt_typ n1 (conts_sub A1).

Inductive degree_contd_wrt_exp : nat -> contd -> Prop :=
  | degree_wrt_exp_contd_infabsunion : forall n1 A1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_contd_wrt_exp n1 (contd_infabsunion A1 cd1)
  | degree_wrt_exp_contd_infapp : forall n1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_contd_wrt_exp n1 (contd_infapp e1 cs1)
  | degree_wrt_exp_contd_infproj : forall n1 A1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_contd_wrt_exp n1 (contd_infproj A1 cs1)
  | degree_wrt_exp_contd_unioninfabs : forall n1 A1 B1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_contd_wrt_exp n1 (contd_unioninfabs A1 B1 cd1)

with degree_conts_wrt_exp : nat -> conts -> Prop :=
  | degree_wrt_exp_conts_infabs : forall n1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_conts_wrt_exp n1 (conts_infabs cd1)
  | degree_wrt_exp_conts_inftapp : forall n1 A1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_inftapp A1 cs1)
  | degree_wrt_exp_conts_inftappunion : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_inftappunion A1 A2 cs1)
  | degree_wrt_exp_conts_unioninftapp : forall n1 A1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_unioninftapp A1 cs1)
  | degree_wrt_exp_conts_infrcdconsintersection : forall n1 l1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_infrcdconsintersection l1 e1 cs1)
  | degree_wrt_exp_conts_intersectioninfrcdcons : forall n1 A1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_conts_wrt_exp n1 (conts_intersectioninfrcdcons A1 cs1)
  | degree_wrt_exp_conts_sub : forall n1 A1,
    degree_conts_wrt_exp n1 (conts_sub A1).

Scheme degree_contd_wrt_typ_ind' := Induction for degree_contd_wrt_typ Sort Prop
  with degree_conts_wrt_typ_ind' := Induction for degree_conts_wrt_typ Sort Prop.

Combined Scheme degree_contd_wrt_typ_degree_conts_wrt_typ_mutind from degree_contd_wrt_typ_ind',degree_conts_wrt_typ_ind'.

Scheme degree_contd_wrt_exp_ind' := Induction for degree_contd_wrt_exp Sort Prop
  with degree_conts_wrt_exp_ind' := Induction for degree_conts_wrt_exp Sort Prop.

Combined Scheme degree_contd_wrt_exp_degree_conts_wrt_exp_mutind from degree_contd_wrt_exp_ind',degree_conts_wrt_exp_ind'.

#[export] Hint Constructors degree_contd_wrt_typ : core lngen.

#[export] Hint Constructors degree_conts_wrt_typ : core lngen.

#[export] Hint Constructors degree_contd_wrt_exp : core lngen.

#[export] Hint Constructors degree_conts_wrt_exp : core lngen.

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
  | degree_wrt_typ_work_infer : forall n1 e1 cs1,
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_infer e1 cs1)
  | degree_wrt_typ_work_check : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_work_wrt_typ n1 (work_check e1 A1)
  | degree_wrt_typ_work_infabs : forall n1 A1 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_work_wrt_typ n1 (work_infabs A1 cd1)
  | degree_wrt_typ_work_infabsunion : forall n1 A1 B1 A2 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_work_wrt_typ n1 (work_infabsunion A1 B1 A2 cd1)
  | degree_wrt_typ_work_infapp : forall n1 A1 B1 e1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_infapp A1 B1 e1 cs1)
  | degree_wrt_typ_work_infproj : forall n1 A1 B1 C1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 C1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_infproj A1 B1 C1 cs1)
  | degree_wrt_typ_work_infrcdconsintersection : forall n1 l1 A1 e1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_infrcdconsintersection l1 A1 e1 cs1)
  | degree_wrt_typ_work_intersectioninfrcdcons : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_intersectioninfrcdcons A1 A2 cs1)
  | degree_wrt_typ_work_inftapp : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_inftapp A1 A2 cs1)
  | degree_wrt_typ_work_sub : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_work_wrt_typ n1 (work_sub A1 A2)
  | degree_wrt_typ_work_inftappunion : forall n1 A1 A2 B1 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_inftappunion A1 A2 B1 cs1)
  | degree_wrt_typ_work_unioninftapp : forall n1 A1 A2 cs1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_conts_wrt_typ n1 cs1 ->
    degree_work_wrt_typ n1 (work_unioninftapp A1 A2 cs1)
  | degree_wrt_typ_work_unioninfabs : forall n1 A1 B1 A2 B2 cd1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 B2 ->
    degree_contd_wrt_typ n1 cd1 ->
    degree_work_wrt_typ n1 (work_unioninfabs A1 B1 A2 B2 cd1)
  | degree_wrt_typ_work_applys : forall n1 cs1 A1,
    degree_conts_wrt_typ n1 cs1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_work_wrt_typ n1 (work_applys cs1 A1)
  | degree_wrt_typ_work_applyd : forall n1 cd1 A1 B1,
    degree_contd_wrt_typ n1 cd1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_work_wrt_typ n1 (work_applyd cd1 A1 B1).

Inductive degree_work_wrt_exp : nat -> work -> Prop :=
  | degree_wrt_exp_work_infer : forall n1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_infer e1 cs1)
  | degree_wrt_exp_work_check : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_work_wrt_exp n1 (work_check e1 A1)
  | degree_wrt_exp_work_infabs : forall n1 A1 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_infabs A1 cd1)
  | degree_wrt_exp_work_infabsunion : forall n1 A1 B1 A2 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_infabsunion A1 B1 A2 cd1)
  | degree_wrt_exp_work_infapp : forall n1 A1 B1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_infapp A1 B1 e1 cs1)
  | degree_wrt_exp_work_infproj : forall n1 A1 B1 C1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_infproj A1 B1 C1 cs1)
  | degree_wrt_exp_work_infrcdconsintersection : forall n1 l1 A1 e1 cs1,
    degree_exp_wrt_exp n1 e1 ->
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_infrcdconsintersection l1 A1 e1 cs1)
  | degree_wrt_exp_work_intersectioninfrcdcons : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_intersectioninfrcdcons A1 A2 cs1)
  | degree_wrt_exp_work_inftapp : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_inftapp A1 A2 cs1)
  | degree_wrt_exp_work_sub : forall n1 A1 A2,
    degree_work_wrt_exp n1 (work_sub A1 A2)
  | degree_wrt_exp_work_inftappunion : forall n1 A1 A2 B1 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_inftappunion A1 A2 B1 cs1)
  | degree_wrt_exp_work_unioninftapp : forall n1 A1 A2 cs1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_unioninftapp A1 A2 cs1)
  | degree_wrt_exp_work_unioninfabs : forall n1 A1 B1 A2 B2 cd1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_unioninfabs A1 B1 A2 B2 cd1)
  | degree_wrt_exp_work_applys : forall n1 cs1 A1,
    degree_conts_wrt_exp n1 cs1 ->
    degree_work_wrt_exp n1 (work_applys cs1 A1)
  | degree_wrt_exp_work_applyd : forall n1 cd1 A1 B1,
    degree_contd_wrt_exp n1 cd1 ->
    degree_work_wrt_exp n1 (work_applyd cd1 A1 B1).

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
    lc_set_typ (typ_intersection A1 A2)
  | lc_set_typ_label : forall l1,
    lc_set_typ (typ_label l1).

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

Inductive lc_set_exp : exp -> Set :=
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
  | lc_set_exp_tabs : forall e1,
    (forall X1 : typvar, lc_set_exp (open_exp_wrt_typ e1 (typ_var_f X1))) ->
    lc_set_exp (exp_tabs e1)
  | lc_set_exp_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_tapp e1 A1)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_anno e1 A1)
  | lc_set_exp_rcd_nil :
    lc_set_exp (exp_rcd_nil)
  | lc_set_exp_rcd_cons : forall l1 e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_rcd_cons l1 e1 e2)
  | lc_set_exp_rcd_proj : forall e1 l1,
    lc_set_exp e1 ->
    lc_set_exp (exp_rcd_proj e1 l1).

Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_exp_mutind from lc_exp_ind'.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_exp_mutind from lc_set_exp_ind'.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_exp_mutrec from lc_set_exp_rec'.

#[export] Hint Constructors lc_exp : core lngen.

#[export] Hint Constructors lc_set_exp : core lngen.

Inductive lc_set_contd : contd -> Set :=
  | lc_set_contd_infabsunion : forall A1 cd1,
    lc_set_typ A1 ->
    lc_set_contd cd1 ->
    lc_set_contd (contd_infabsunion A1 cd1)
  | lc_set_contd_infapp : forall e1 cs1,
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_contd (contd_infapp e1 cs1)
  | lc_set_contd_infproj : forall A1 cs1,
    lc_set_typ A1 ->
    lc_set_conts cs1 ->
    lc_set_contd (contd_infproj A1 cs1)
  | lc_set_contd_unioninfabs : forall A1 B1 cd1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_contd cd1 ->
    lc_set_contd (contd_unioninfabs A1 B1 cd1)

with lc_set_conts : conts -> Set :=
  | lc_set_conts_infabs : forall cd1,
    lc_set_contd cd1 ->
    lc_set_conts (conts_infabs cd1)
  | lc_set_conts_inftapp : forall A1 cs1,
    lc_set_typ A1 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_inftapp A1 cs1)
  | lc_set_conts_inftappunion : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_inftappunion A1 A2 cs1)
  | lc_set_conts_unioninftapp : forall A1 cs1,
    lc_set_typ A1 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_unioninftapp A1 cs1)
  | lc_set_conts_infrcdconsintersection : forall l1 e1 cs1,
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_infrcdconsintersection l1 e1 cs1)
  | lc_set_conts_intersectioninfrcdcons : forall A1 cs1,
    lc_set_typ A1 ->
    lc_set_conts cs1 ->
    lc_set_conts (conts_intersectioninfrcdcons A1 cs1)
  | lc_set_conts_sub : forall A1,
    lc_set_typ A1 ->
    lc_set_conts (conts_sub A1).

Scheme lc_contd_ind' := Induction for lc_contd Sort Prop
  with lc_conts_ind' := Induction for lc_conts Sort Prop.

Combined Scheme lc_contd_lc_conts_mutind from lc_contd_ind',lc_conts_ind'.

Scheme lc_set_contd_ind' := Induction for lc_set_contd Sort Prop
  with lc_set_conts_ind' := Induction for lc_set_conts Sort Prop.

Combined Scheme lc_set_contd_lc_set_conts_mutind from lc_set_contd_ind',lc_set_conts_ind'.

Scheme lc_set_contd_rec' := Induction for lc_set_contd Sort Set
  with lc_set_conts_rec' := Induction for lc_set_conts Sort Set.

Combined Scheme lc_set_contd_lc_set_conts_mutrec from lc_set_contd_rec',lc_set_conts_rec'.

#[export] Hint Constructors lc_contd : core lngen.

#[export] Hint Constructors lc_conts : core lngen.

#[export] Hint Constructors lc_set_contd : core lngen.

#[export] Hint Constructors lc_set_conts : core lngen.

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
  | lc_set_work_infer : forall e1 cs1,
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_infer e1 cs1)
  | lc_set_work_check : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_work (work_check e1 A1)
  | lc_set_work_infabs : forall A1 cd1,
    lc_set_typ A1 ->
    lc_set_contd cd1 ->
    lc_set_work (work_infabs A1 cd1)
  | lc_set_work_infabsunion : forall A1 B1 A2 cd1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ A2 ->
    lc_set_contd cd1 ->
    lc_set_work (work_infabsunion A1 B1 A2 cd1)
  | lc_set_work_infapp : forall A1 B1 e1 cs1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_infapp A1 B1 e1 cs1)
  | lc_set_work_infproj : forall A1 B1 C1 cs1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ C1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_infproj A1 B1 C1 cs1)
  | lc_set_work_infrcdconsintersection : forall l1 A1 e1 cs1,
    lc_set_typ A1 ->
    lc_set_exp e1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_infrcdconsintersection l1 A1 e1 cs1)
  | lc_set_work_intersectioninfrcdcons : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_work (work_intersectioninfrcdcons A1 A2 cs1)
  | lc_set_work_inftapp : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_work (work_inftapp A1 A2 cs1)
  | lc_set_work_sub : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_work (work_sub A1 A2)
  | lc_set_work_inftappunion : forall A1 A2 B1 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ B1 ->
    lc_set_conts cs1 ->
    lc_set_work (work_inftappunion A1 A2 B1 cs1)
  | lc_set_work_unioninftapp : forall A1 A2 cs1,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_conts cs1 ->
    lc_set_work (work_unioninftapp A1 A2 cs1)
  | lc_set_work_unioninfabs : forall A1 B1 A2 B2 cd1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ A2 ->
    lc_set_typ B2 ->
    lc_set_contd cd1 ->
    lc_set_work (work_unioninfabs A1 B1 A2 B2 cd1)
  | lc_set_work_applys : forall cs1 A1,
    lc_set_conts cs1 ->
    lc_set_typ A1 ->
    lc_set_work (work_applys cs1 A1)
  | lc_set_work_applyd : forall cd1 A1 B1,
    lc_set_contd cd1 ->
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_work (work_applyd cd1 A1 B1).

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

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

#[export] Hint Unfold body_exp_wrt_typ : core.

#[export] Hint Unfold body_exp_wrt_exp : core.

Definition body_contd_wrt_typ cd1 := forall X1, lc_contd (open_contd_wrt_typ cd1 (typ_var_f X1)).

Definition body_conts_wrt_typ cs1 := forall X1, lc_conts (open_conts_wrt_typ cs1 (typ_var_f X1)).

Definition body_contd_wrt_exp cd1 := forall x1, lc_contd (open_contd_wrt_exp cd1 (exp_var_f x1)).

Definition body_conts_wrt_exp cs1 := forall x1, lc_conts (open_conts_wrt_exp cs1 (exp_var_f x1)).

#[export] Hint Unfold body_contd_wrt_typ : core.

#[export] Hint Unfold body_conts_wrt_typ : core.

#[export] Hint Unfold body_contd_wrt_exp : core.

#[export] Hint Unfold body_conts_wrt_exp : core.

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

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_contd_min_size_conts_min_mutual :
(forall cd1, 1 <= size_contd cd1) /\
(forall cs1, 1 <= size_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_contd_min :
forall cd1, 1 <= size_contd cd1.
Proof.
pose proof size_contd_min_size_conts_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_min : lngen.

Lemma size_conts_min :
forall cs1, 1 <= size_conts cs1.
Proof.
pose proof size_contd_min_size_conts_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_min : lngen.

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

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_close_contd_wrt_typ_rec_size_conts_close_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1,
  size_contd (close_contd_wrt_typ_rec n1 X1 cd1) = size_contd cd1) /\
(forall cs1 X1 n1,
  size_conts (close_conts_wrt_typ_rec n1 X1 cs1) = size_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_contd_close_contd_wrt_typ_rec :
forall cd1 X1 n1,
  size_contd (close_contd_wrt_typ_rec n1 X1 cd1) = size_contd cd1.
Proof.
pose proof size_contd_close_contd_wrt_typ_rec_size_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_conts_close_conts_wrt_typ_rec :
forall cs1 X1 n1,
  size_conts (close_conts_wrt_typ_rec n1 X1 cs1) = size_conts cs1.
Proof.
pose proof size_contd_close_contd_wrt_typ_rec_size_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_close_conts_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_conts_close_conts_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_close_contd_wrt_exp_rec_size_conts_close_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1,
  size_contd (close_contd_wrt_exp_rec n1 x1 cd1) = size_contd cd1) /\
(forall cs1 x1 n1,
  size_conts (close_conts_wrt_exp_rec n1 x1 cs1) = size_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_contd_close_contd_wrt_exp_rec :
forall cd1 x1 n1,
  size_contd (close_contd_wrt_exp_rec n1 x1 cd1) = size_contd cd1.
Proof.
pose proof size_contd_close_contd_wrt_exp_rec_size_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_conts_close_conts_wrt_exp_rec :
forall cs1 x1 n1,
  size_conts (close_conts_wrt_exp_rec n1 x1 cs1) = size_conts cs1.
Proof.
pose proof size_contd_close_contd_wrt_exp_rec_size_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_close_conts_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_conts_close_conts_wrt_exp_rec using solve [auto] : lngen.

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

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma size_contd_close_contd_wrt_typ :
forall cd1 X1,
  size_contd (close_contd_wrt_typ X1 cd1) = size_contd cd1.
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_typ using solve [auto] : lngen.

Lemma size_conts_close_conts_wrt_typ :
forall cs1 X1,
  size_conts (close_conts_wrt_typ X1 cs1) = size_conts cs1.
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_conts_close_conts_wrt_typ : lngen.
#[export] Hint Rewrite size_conts_close_conts_wrt_typ using solve [auto] : lngen.

Lemma size_contd_close_contd_wrt_exp :
forall cd1 x1,
  size_contd (close_contd_wrt_exp x1 cd1) = size_contd cd1.
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_contd_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite size_contd_close_contd_wrt_exp using solve [auto] : lngen.

Lemma size_conts_close_conts_wrt_exp :
forall cs1 x1,
  size_conts (close_conts_wrt_exp x1 cs1) = size_conts cs1.
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_conts_close_conts_wrt_exp : lngen.
#[export] Hint Rewrite size_conts_close_conts_wrt_exp using solve [auto] : lngen.

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

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_typ_rec_size_conts_open_conts_wrt_typ_rec_mutual :
(forall cd1 A1 n1,
  size_contd cd1 <= size_contd (open_contd_wrt_typ_rec n1 A1 cd1)) /\
(forall cs1 A1 n1,
  size_conts cs1 <= size_conts (open_conts_wrt_typ_rec n1 A1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_typ_rec :
forall cd1 A1 n1,
  size_contd cd1 <= size_contd (open_contd_wrt_typ_rec n1 A1 cd1).
Proof.
pose proof size_contd_open_contd_wrt_typ_rec_size_conts_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_conts_open_conts_wrt_typ_rec :
forall cs1 A1 n1,
  size_conts cs1 <= size_conts (open_conts_wrt_typ_rec n1 A1 cs1).
Proof.
pose proof size_contd_open_contd_wrt_typ_rec_size_conts_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_exp_rec_size_conts_open_conts_wrt_exp_rec_mutual :
(forall cd1 e1 n1,
  size_contd cd1 <= size_contd (open_contd_wrt_exp_rec n1 e1 cd1)) /\
(forall cs1 e1 n1,
  size_conts cs1 <= size_conts (open_conts_wrt_exp_rec n1 e1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_exp_rec :
forall cd1 e1 n1,
  size_contd cd1 <= size_contd (open_contd_wrt_exp_rec n1 e1 cd1).
Proof.
pose proof size_contd_open_contd_wrt_exp_rec_size_conts_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_conts_open_conts_wrt_exp_rec :
forall cs1 e1 n1,
  size_conts cs1 <= size_conts (open_conts_wrt_exp_rec n1 e1 cs1).
Proof.
pose proof size_contd_open_contd_wrt_exp_rec_size_conts_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_exp_rec : lngen.

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

Lemma size_exp_open_exp_wrt_typ :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

Lemma size_contd_open_contd_wrt_typ :
forall cd1 A1,
  size_contd cd1 <= size_contd (open_contd_wrt_typ cd1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ : lngen.

Lemma size_conts_open_conts_wrt_typ :
forall cs1 A1,
  size_conts cs1 <= size_conts (open_conts_wrt_typ cs1 A1).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_typ : lngen.

Lemma size_contd_open_contd_wrt_exp :
forall cd1 e1,
  size_contd cd1 <= size_contd (open_contd_wrt_exp cd1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp : lngen.

Lemma size_conts_open_conts_wrt_exp :
forall cs1 e1,
  size_conts cs1 <= size_conts (open_conts_wrt_exp cs1 e1).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_exp : lngen.

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

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_typ_rec_var_size_conts_open_conts_wrt_typ_rec_var_mutual :
(forall cd1 X1 n1,
  size_contd (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1) = size_contd cd1) /\
(forall cs1 X1 n1,
  size_conts (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1) = size_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_typ_rec_var :
forall cd1 X1 n1,
  size_contd (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1) = size_contd cd1.
Proof.
pose proof size_contd_open_contd_wrt_typ_rec_var_size_conts_open_conts_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_conts_open_conts_wrt_typ_rec_var :
forall cs1 X1 n1,
  size_conts (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1) = size_conts cs1.
Proof.
pose proof size_contd_open_contd_wrt_typ_rec_var_size_conts_open_conts_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_conts_open_conts_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_exp_rec_var_size_conts_open_conts_wrt_exp_rec_var_mutual :
(forall cd1 x1 n1,
  size_contd (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1) = size_contd cd1) /\
(forall cs1 x1 n1,
  size_conts (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1) = size_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_contd_open_contd_wrt_exp_rec_var :
forall cd1 x1 n1,
  size_contd (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1) = size_contd cd1.
Proof.
pose proof size_contd_open_contd_wrt_exp_rec_var_size_conts_open_conts_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_conts_open_conts_wrt_exp_rec_var :
forall cs1 x1 n1,
  size_conts (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1) = size_conts cs1.
Proof.
pose proof size_contd_open_contd_wrt_exp_rec_var_size_conts_open_conts_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_conts_open_conts_wrt_exp_rec_var using solve [auto] : lngen.

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

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (typ_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

Lemma size_contd_open_contd_wrt_typ_var :
forall cd1 X1,
  size_contd (open_contd_wrt_typ cd1 (typ_var_f X1)) = size_contd cd1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_typ_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_typ_var using solve [auto] : lngen.

Lemma size_conts_open_conts_wrt_typ_var :
forall cs1 X1,
  size_conts (open_conts_wrt_typ cs1 (typ_var_f X1)) = size_conts cs1.
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_typ_var : lngen.
#[export] Hint Rewrite size_conts_open_conts_wrt_typ_var using solve [auto] : lngen.

Lemma size_contd_open_contd_wrt_exp_var :
forall cd1 x1,
  size_contd (open_contd_wrt_exp cd1 (exp_var_f x1)) = size_contd cd1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_contd_open_contd_wrt_exp_var : lngen.
#[export] Hint Rewrite size_contd_open_contd_wrt_exp_var using solve [auto] : lngen.

Lemma size_conts_open_conts_wrt_exp_var :
forall cs1 x1,
  size_conts (open_conts_wrt_exp cs1 (exp_var_f x1)) = size_conts cs1.
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_conts_open_conts_wrt_exp_var : lngen.
#[export] Hint Rewrite size_conts_open_conts_wrt_exp_var using solve [auto] : lngen.

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

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_S : lngen.

(* begin hide *)

Lemma degree_contd_wrt_typ_S_degree_conts_wrt_typ_S_mutual :
(forall n1 cd1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_contd_wrt_typ (S n1) cd1) /\
(forall n1 cs1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_conts_wrt_typ (S n1) cs1).
Proof.
apply_mutual_ind degree_contd_wrt_typ_degree_conts_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_contd_wrt_typ_S :
forall n1 cd1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_contd_wrt_typ (S n1) cd1.
Proof.
pose proof degree_contd_wrt_typ_S_degree_conts_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_S : lngen.

Lemma degree_conts_wrt_typ_S :
forall n1 cs1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_conts_wrt_typ (S n1) cs1.
Proof.
pose proof degree_contd_wrt_typ_S_degree_conts_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_contd_wrt_exp_S_degree_conts_wrt_exp_S_mutual :
(forall n1 cd1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp (S n1) cd1) /\
(forall n1 cs1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp (S n1) cs1).
Proof.
apply_mutual_ind degree_contd_wrt_exp_degree_conts_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_contd_wrt_exp_S :
forall n1 cd1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp (S n1) cd1.
Proof.
pose proof degree_contd_wrt_exp_S_degree_conts_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_S : lngen.

Lemma degree_conts_wrt_exp_S :
forall n1 cs1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp (S n1) cs1.
Proof.
pose proof degree_contd_wrt_exp_S_degree_conts_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_S : lngen.

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

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

Lemma degree_contd_wrt_typ_O :
forall n1 cd1,
  degree_contd_wrt_typ O cd1 ->
  degree_contd_wrt_typ n1 cd1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_O : lngen.

Lemma degree_conts_wrt_typ_O :
forall n1 cs1,
  degree_conts_wrt_typ O cs1 ->
  degree_conts_wrt_typ n1 cs1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_O : lngen.

Lemma degree_contd_wrt_exp_O :
forall n1 cd1,
  degree_contd_wrt_exp O cd1 ->
  degree_contd_wrt_exp n1 cd1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_O : lngen.

Lemma degree_conts_wrt_exp_O :
forall n1 cs1,
  degree_conts_wrt_exp O cs1 ->
  degree_conts_wrt_exp n1 cs1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_O : lngen.

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

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_rec_degree_conts_wrt_typ_close_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cd1)) /\
(forall cs1 X1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_conts_wrt_typ (S n1) (close_conts_wrt_typ_rec n1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_rec :
forall cd1 X1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cd1).
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_typ_rec_degree_conts_wrt_typ_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_close_conts_wrt_typ_rec :
forall cs1 X1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_conts_wrt_typ (S n1) (close_conts_wrt_typ_rec n1 X1 cs1).
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_typ_rec_degree_conts_wrt_typ_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_close_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_rec_degree_conts_wrt_typ_close_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1 n2,
  degree_contd_wrt_typ n2 cd1 ->
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cd1)) /\
(forall cs1 x1 n1 n2,
  degree_conts_wrt_typ n2 cs1 ->
  degree_conts_wrt_typ n2 (close_conts_wrt_exp_rec n1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_rec :
forall cd1 x1 n1 n2,
  degree_contd_wrt_typ n2 cd1 ->
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cd1).
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_exp_rec_degree_conts_wrt_typ_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_close_conts_wrt_exp_rec :
forall cs1 x1 n1 n2,
  degree_conts_wrt_typ n2 cs1 ->
  degree_conts_wrt_typ n2 (close_conts_wrt_exp_rec n1 x1 cs1).
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_exp_rec_degree_conts_wrt_typ_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_close_conts_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_rec_degree_conts_wrt_exp_close_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1 n2,
  degree_contd_wrt_exp n2 cd1 ->
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cd1)) /\
(forall cs1 X1 n1 n2,
  degree_conts_wrt_exp n2 cs1 ->
  degree_conts_wrt_exp n2 (close_conts_wrt_typ_rec n1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_rec :
forall cd1 X1 n1 n2,
  degree_contd_wrt_exp n2 cd1 ->
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cd1).
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_typ_rec_degree_conts_wrt_exp_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_close_conts_wrt_typ_rec :
forall cs1 X1 n1 n2,
  degree_conts_wrt_exp n2 cs1 ->
  degree_conts_wrt_exp n2 (close_conts_wrt_typ_rec n1 X1 cs1).
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_typ_rec_degree_conts_wrt_exp_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_close_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_rec_degree_conts_wrt_exp_close_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cd1)) /\
(forall cs1 x1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp (S n1) (close_conts_wrt_exp_rec n1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_rec :
forall cd1 x1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cd1).
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_exp_rec_degree_conts_wrt_exp_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_close_conts_wrt_exp_rec :
forall cs1 x1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp (S n1) (close_conts_wrt_exp_rec n1 x1 cs1).
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_exp_rec_degree_conts_wrt_exp_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_close_conts_wrt_exp_rec : lngen.

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

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_typ :
forall cd1 X1,
  degree_contd_wrt_typ 0 cd1 ->
  degree_contd_wrt_typ 1 (close_contd_wrt_typ X1 cd1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_typ : lngen.

Lemma degree_conts_wrt_typ_close_conts_wrt_typ :
forall cs1 X1,
  degree_conts_wrt_typ 0 cs1 ->
  degree_conts_wrt_typ 1 (close_conts_wrt_typ X1 cs1).
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_close_conts_wrt_typ : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_exp :
forall cd1 x1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_contd_wrt_typ n1 (close_contd_wrt_exp x1 cd1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_close_contd_wrt_exp : lngen.

Lemma degree_conts_wrt_typ_close_conts_wrt_exp :
forall cs1 x1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_conts_wrt_typ n1 (close_conts_wrt_exp x1 cs1).
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_close_conts_wrt_exp : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_typ :
forall cd1 X1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp n1 (close_contd_wrt_typ X1 cd1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_typ : lngen.

Lemma degree_conts_wrt_exp_close_conts_wrt_typ :
forall cs1 X1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp n1 (close_conts_wrt_typ X1 cs1).
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_close_conts_wrt_typ : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_exp :
forall cd1 x1,
  degree_contd_wrt_exp 0 cd1 ->
  degree_contd_wrt_exp 1 (close_contd_wrt_exp x1 cd1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_close_contd_wrt_exp : lngen.

Lemma degree_conts_wrt_exp_close_conts_wrt_exp :
forall cs1 x1,
  degree_conts_wrt_exp 0 cs1 ->
  degree_conts_wrt_exp 1 (close_conts_wrt_exp x1 cs1).
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_close_conts_wrt_exp : lngen.

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

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv_degree_conts_wrt_typ_close_conts_wrt_typ_rec_inv_mutual :
(forall cd1 X1 n1,
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cd1) ->
  degree_contd_wrt_typ n1 cd1) /\
(forall cs1 X1 n1,
  degree_conts_wrt_typ (S n1) (close_conts_wrt_typ_rec n1 X1 cs1) ->
  degree_conts_wrt_typ n1 cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv :
forall cd1 X1 n1,
  degree_contd_wrt_typ (S n1) (close_contd_wrt_typ_rec n1 X1 cd1) ->
  degree_contd_wrt_typ n1 cd1.
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv_degree_conts_wrt_typ_close_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_close_conts_wrt_typ_rec_inv :
forall cs1 X1 n1,
  degree_conts_wrt_typ (S n1) (close_conts_wrt_typ_rec n1 X1 cs1) ->
  degree_conts_wrt_typ n1 cs1.
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_typ_rec_inv_degree_conts_wrt_typ_close_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_close_conts_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv_degree_conts_wrt_typ_close_conts_wrt_exp_rec_inv_mutual :
(forall cd1 x1 n1 n2,
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cd1) ->
  degree_contd_wrt_typ n2 cd1) /\
(forall cs1 x1 n1 n2,
  degree_conts_wrt_typ n2 (close_conts_wrt_exp_rec n1 x1 cs1) ->
  degree_conts_wrt_typ n2 cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv :
forall cd1 x1 n1 n2,
  degree_contd_wrt_typ n2 (close_contd_wrt_exp_rec n1 x1 cd1) ->
  degree_contd_wrt_typ n2 cd1.
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv_degree_conts_wrt_typ_close_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_close_conts_wrt_exp_rec_inv :
forall cs1 x1 n1 n2,
  degree_conts_wrt_typ n2 (close_conts_wrt_exp_rec n1 x1 cs1) ->
  degree_conts_wrt_typ n2 cs1.
Proof.
pose proof degree_contd_wrt_typ_close_contd_wrt_exp_rec_inv_degree_conts_wrt_typ_close_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_close_conts_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv_degree_conts_wrt_exp_close_conts_wrt_typ_rec_inv_mutual :
(forall cd1 X1 n1 n2,
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cd1) ->
  degree_contd_wrt_exp n2 cd1) /\
(forall cs1 X1 n1 n2,
  degree_conts_wrt_exp n2 (close_conts_wrt_typ_rec n1 X1 cs1) ->
  degree_conts_wrt_exp n2 cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv :
forall cd1 X1 n1 n2,
  degree_contd_wrt_exp n2 (close_contd_wrt_typ_rec n1 X1 cd1) ->
  degree_contd_wrt_exp n2 cd1.
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv_degree_conts_wrt_exp_close_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_close_conts_wrt_typ_rec_inv :
forall cs1 X1 n1 n2,
  degree_conts_wrt_exp n2 (close_conts_wrt_typ_rec n1 X1 cs1) ->
  degree_conts_wrt_exp n2 cs1.
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_typ_rec_inv_degree_conts_wrt_exp_close_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_close_conts_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv_degree_conts_wrt_exp_close_conts_wrt_exp_rec_inv_mutual :
(forall cd1 x1 n1,
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cd1) ->
  degree_contd_wrt_exp n1 cd1) /\
(forall cs1 x1 n1,
  degree_conts_wrt_exp (S n1) (close_conts_wrt_exp_rec n1 x1 cs1) ->
  degree_conts_wrt_exp n1 cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv :
forall cd1 x1 n1,
  degree_contd_wrt_exp (S n1) (close_contd_wrt_exp_rec n1 x1 cd1) ->
  degree_contd_wrt_exp n1 cd1.
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv_degree_conts_wrt_exp_close_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_close_conts_wrt_exp_rec_inv :
forall cs1 x1 n1,
  degree_conts_wrt_exp (S n1) (close_conts_wrt_exp_rec n1 x1 cs1) ->
  degree_conts_wrt_exp n1 cs1.
Proof.
pose proof degree_contd_wrt_exp_close_contd_wrt_exp_rec_inv_degree_conts_wrt_exp_close_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_close_conts_wrt_exp_rec_inv : lngen.

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

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_typ_inv :
forall cd1 X1,
  degree_contd_wrt_typ 1 (close_contd_wrt_typ X1 cd1) ->
  degree_contd_wrt_typ 0 cd1.
Proof.
unfold close_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_typ_inv : lngen.

Lemma degree_conts_wrt_typ_close_conts_wrt_typ_inv :
forall cs1 X1,
  degree_conts_wrt_typ 1 (close_conts_wrt_typ X1 cs1) ->
  degree_conts_wrt_typ 0 cs1.
Proof.
unfold close_conts_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_close_conts_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_typ_close_contd_wrt_exp_inv :
forall cd1 x1 n1,
  degree_contd_wrt_typ n1 (close_contd_wrt_exp x1 cd1) ->
  degree_contd_wrt_typ n1 cd1.
Proof.
unfold close_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_close_contd_wrt_exp_inv : lngen.

Lemma degree_conts_wrt_typ_close_conts_wrt_exp_inv :
forall cs1 x1 n1,
  degree_conts_wrt_typ n1 (close_conts_wrt_exp x1 cs1) ->
  degree_conts_wrt_typ n1 cs1.
Proof.
unfold close_conts_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_close_conts_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_typ_inv :
forall cd1 X1 n1,
  degree_contd_wrt_exp n1 (close_contd_wrt_typ X1 cd1) ->
  degree_contd_wrt_exp n1 cd1.
Proof.
unfold close_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_typ_inv : lngen.

Lemma degree_conts_wrt_exp_close_conts_wrt_typ_inv :
forall cs1 X1 n1,
  degree_conts_wrt_exp n1 (close_conts_wrt_typ X1 cs1) ->
  degree_conts_wrt_exp n1 cs1.
Proof.
unfold close_conts_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_close_conts_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_exp_close_contd_wrt_exp_inv :
forall cd1 x1,
  degree_contd_wrt_exp 1 (close_contd_wrt_exp x1 cd1) ->
  degree_contd_wrt_exp 0 cd1.
Proof.
unfold close_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_close_contd_wrt_exp_inv : lngen.

Lemma degree_conts_wrt_exp_close_conts_wrt_exp_inv :
forall cs1 x1,
  degree_conts_wrt_exp 1 (close_conts_wrt_exp x1 cs1) ->
  degree_conts_wrt_exp 0 cs1.
Proof.
unfold close_conts_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_close_conts_wrt_exp_inv : lngen.

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

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_rec_degree_conts_wrt_typ_open_conts_wrt_typ_rec_mutual :
(forall cd1 A1 n1,
  degree_contd_wrt_typ (S n1) cd1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cd1)) /\
(forall cs1 A1 n1,
  degree_conts_wrt_typ (S n1) cs1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_conts_wrt_typ n1 (open_conts_wrt_typ_rec n1 A1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_rec :
forall cd1 A1 n1,
  degree_contd_wrt_typ (S n1) cd1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cd1).
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_typ_rec_degree_conts_wrt_typ_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_open_conts_wrt_typ_rec :
forall cs1 A1 n1,
  degree_conts_wrt_typ (S n1) cs1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_conts_wrt_typ n1 (open_conts_wrt_typ_rec n1 A1 cs1).
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_typ_rec_degree_conts_wrt_typ_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_rec_degree_conts_wrt_typ_open_conts_wrt_exp_rec_mutual :
(forall cd1 e1 n1 n2,
  degree_contd_wrt_typ n1 cd1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cd1)) /\
(forall cs1 e1 n1 n2,
  degree_conts_wrt_typ n1 cs1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_conts_wrt_typ n1 (open_conts_wrt_exp_rec n2 e1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_rec :
forall cd1 e1 n1 n2,
  degree_contd_wrt_typ n1 cd1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cd1).
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_exp_rec_degree_conts_wrt_typ_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_open_conts_wrt_exp_rec :
forall cs1 e1 n1 n2,
  degree_conts_wrt_typ n1 cs1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_conts_wrt_typ n1 (open_conts_wrt_exp_rec n2 e1 cs1).
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_exp_rec_degree_conts_wrt_typ_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_open_conts_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_rec_degree_conts_wrt_exp_open_conts_wrt_typ_rec_mutual :
(forall cd1 A1 n1 n2,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cd1)) /\
(forall cs1 A1 n1 n2,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp n1 (open_conts_wrt_typ_rec n2 A1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_rec :
forall cd1 A1 n1 n2,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cd1).
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_typ_rec_degree_conts_wrt_exp_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_open_conts_wrt_typ_rec :
forall cs1 A1 n1 n2,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp n1 (open_conts_wrt_typ_rec n2 A1 cs1).
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_typ_rec_degree_conts_wrt_exp_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_rec_degree_conts_wrt_exp_open_conts_wrt_exp_rec_mutual :
(forall cd1 e1 n1,
  degree_contd_wrt_exp (S n1) cd1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cd1)) /\
(forall cs1 e1 n1,
  degree_conts_wrt_exp (S n1) cs1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_conts_wrt_exp n1 (open_conts_wrt_exp_rec n1 e1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_rec :
forall cd1 e1 n1,
  degree_contd_wrt_exp (S n1) cd1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cd1).
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_exp_rec_degree_conts_wrt_exp_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_open_conts_wrt_exp_rec :
forall cs1 e1 n1,
  degree_conts_wrt_exp (S n1) cs1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_conts_wrt_exp n1 (open_conts_wrt_exp_rec n1 e1 cs1).
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_exp_rec_degree_conts_wrt_exp_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_open_conts_wrt_exp_rec : lngen.

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

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_typ :
forall cd1 A1,
  degree_contd_wrt_typ 1 cd1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_contd_wrt_typ 0 (open_contd_wrt_typ cd1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_typ : lngen.

Lemma degree_conts_wrt_typ_open_conts_wrt_typ :
forall cs1 A1,
  degree_conts_wrt_typ 1 cs1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_conts_wrt_typ 0 (open_conts_wrt_typ cs1 A1).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_open_conts_wrt_typ : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_exp :
forall cd1 e1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (open_contd_wrt_exp cd1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_open_contd_wrt_exp : lngen.

Lemma degree_conts_wrt_typ_open_conts_wrt_exp :
forall cs1 e1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_conts_wrt_typ n1 (open_conts_wrt_exp cs1 e1).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_open_conts_wrt_exp : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_typ :
forall cd1 A1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp n1 (open_contd_wrt_typ cd1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_typ : lngen.

Lemma degree_conts_wrt_exp_open_conts_wrt_typ :
forall cs1 A1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp n1 (open_conts_wrt_typ cs1 A1).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_open_conts_wrt_typ : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_exp :
forall cd1 e1,
  degree_contd_wrt_exp 1 cd1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_contd_wrt_exp 0 (open_contd_wrt_exp cd1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_open_contd_wrt_exp : lngen.

Lemma degree_conts_wrt_exp_open_conts_wrt_exp :
forall cs1 e1,
  degree_conts_wrt_exp 1 cs1 ->
  degree_exp_wrt_exp 0 e1 ->
  degree_conts_wrt_exp 0 (open_conts_wrt_exp cs1 e1).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_open_conts_wrt_exp : lngen.

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

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv_degree_conts_wrt_typ_open_conts_wrt_typ_rec_inv_mutual :
(forall cd1 A1 n1,
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cd1) ->
  degree_contd_wrt_typ (S n1) cd1) /\
(forall cs1 A1 n1,
  degree_conts_wrt_typ n1 (open_conts_wrt_typ_rec n1 A1 cs1) ->
  degree_conts_wrt_typ (S n1) cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv :
forall cd1 A1 n1,
  degree_contd_wrt_typ n1 (open_contd_wrt_typ_rec n1 A1 cd1) ->
  degree_contd_wrt_typ (S n1) cd1.
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv_degree_conts_wrt_typ_open_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_open_conts_wrt_typ_rec_inv :
forall cs1 A1 n1,
  degree_conts_wrt_typ n1 (open_conts_wrt_typ_rec n1 A1 cs1) ->
  degree_conts_wrt_typ (S n1) cs1.
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_typ_rec_inv_degree_conts_wrt_typ_open_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_open_conts_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv_degree_conts_wrt_typ_open_conts_wrt_exp_rec_inv_mutual :
(forall cd1 e1 n1 n2,
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cd1) ->
  degree_contd_wrt_typ n1 cd1) /\
(forall cs1 e1 n1 n2,
  degree_conts_wrt_typ n1 (open_conts_wrt_exp_rec n2 e1 cs1) ->
  degree_conts_wrt_typ n1 cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv :
forall cd1 e1 n1 n2,
  degree_contd_wrt_typ n1 (open_contd_wrt_exp_rec n2 e1 cd1) ->
  degree_contd_wrt_typ n1 cd1.
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv_degree_conts_wrt_typ_open_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_typ_open_conts_wrt_exp_rec_inv :
forall cs1 e1 n1 n2,
  degree_conts_wrt_typ n1 (open_conts_wrt_exp_rec n2 e1 cs1) ->
  degree_conts_wrt_typ n1 cs1.
Proof.
pose proof degree_contd_wrt_typ_open_contd_wrt_exp_rec_inv_degree_conts_wrt_typ_open_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_open_conts_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv_degree_conts_wrt_exp_open_conts_wrt_typ_rec_inv_mutual :
(forall cd1 A1 n1 n2,
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cd1) ->
  degree_contd_wrt_exp n1 cd1) /\
(forall cs1 A1 n1 n2,
  degree_conts_wrt_exp n1 (open_conts_wrt_typ_rec n2 A1 cs1) ->
  degree_conts_wrt_exp n1 cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv :
forall cd1 A1 n1 n2,
  degree_contd_wrt_exp n1 (open_contd_wrt_typ_rec n2 A1 cd1) ->
  degree_contd_wrt_exp n1 cd1.
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv_degree_conts_wrt_exp_open_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_open_conts_wrt_typ_rec_inv :
forall cs1 A1 n1 n2,
  degree_conts_wrt_exp n1 (open_conts_wrt_typ_rec n2 A1 cs1) ->
  degree_conts_wrt_exp n1 cs1.
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_typ_rec_inv_degree_conts_wrt_exp_open_conts_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_open_conts_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv_degree_conts_wrt_exp_open_conts_wrt_exp_rec_inv_mutual :
(forall cd1 e1 n1,
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cd1) ->
  degree_contd_wrt_exp (S n1) cd1) /\
(forall cs1 e1 n1,
  degree_conts_wrt_exp n1 (open_conts_wrt_exp_rec n1 e1 cs1) ->
  degree_conts_wrt_exp (S n1) cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv :
forall cd1 e1 n1,
  degree_contd_wrt_exp n1 (open_contd_wrt_exp_rec n1 e1 cd1) ->
  degree_contd_wrt_exp (S n1) cd1.
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv_degree_conts_wrt_exp_open_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_conts_wrt_exp_open_conts_wrt_exp_rec_inv :
forall cs1 e1 n1,
  degree_conts_wrt_exp n1 (open_conts_wrt_exp_rec n1 e1 cs1) ->
  degree_conts_wrt_exp (S n1) cs1.
Proof.
pose proof degree_contd_wrt_exp_open_contd_wrt_exp_rec_inv_degree_conts_wrt_exp_open_conts_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_open_conts_wrt_exp_rec_inv : lngen.

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

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_typ_inv :
forall cd1 A1,
  degree_contd_wrt_typ 0 (open_contd_wrt_typ cd1 A1) ->
  degree_contd_wrt_typ 1 cd1.
Proof.
unfold open_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_typ_inv : lngen.

Lemma degree_conts_wrt_typ_open_conts_wrt_typ_inv :
forall cs1 A1,
  degree_conts_wrt_typ 0 (open_conts_wrt_typ cs1 A1) ->
  degree_conts_wrt_typ 1 cs1.
Proof.
unfold open_conts_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_open_conts_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_typ_open_contd_wrt_exp_inv :
forall cd1 e1 n1,
  degree_contd_wrt_typ n1 (open_contd_wrt_exp cd1 e1) ->
  degree_contd_wrt_typ n1 cd1.
Proof.
unfold open_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_typ_open_contd_wrt_exp_inv : lngen.

Lemma degree_conts_wrt_typ_open_conts_wrt_exp_inv :
forall cs1 e1 n1,
  degree_conts_wrt_typ n1 (open_conts_wrt_exp cs1 e1) ->
  degree_conts_wrt_typ n1 cs1.
Proof.
unfold open_conts_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_typ_open_conts_wrt_exp_inv : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_typ_inv :
forall cd1 A1 n1,
  degree_contd_wrt_exp n1 (open_contd_wrt_typ cd1 A1) ->
  degree_contd_wrt_exp n1 cd1.
Proof.
unfold open_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_typ_inv : lngen.

Lemma degree_conts_wrt_exp_open_conts_wrt_typ_inv :
forall cs1 A1 n1,
  degree_conts_wrt_exp n1 (open_conts_wrt_typ cs1 A1) ->
  degree_conts_wrt_exp n1 cs1.
Proof.
unfold open_conts_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_open_conts_wrt_typ_inv : lngen.

Lemma degree_contd_wrt_exp_open_contd_wrt_exp_inv :
forall cd1 e1,
  degree_contd_wrt_exp 0 (open_contd_wrt_exp cd1 e1) ->
  degree_contd_wrt_exp 1 cd1.
Proof.
unfold open_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_contd_wrt_exp_open_contd_wrt_exp_inv : lngen.

Lemma degree_conts_wrt_exp_open_conts_wrt_exp_inv :
forall cs1 e1,
  degree_conts_wrt_exp 0 (open_conts_wrt_exp cs1 e1) ->
  degree_conts_wrt_exp 1 cs1.
Proof.
unfold open_conts_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_conts_wrt_exp_open_conts_wrt_exp_inv : lngen.

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

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_inj_close_conts_wrt_typ_rec_inj_mutual :
(forall cd1 cd2 X1 n1,
  close_contd_wrt_typ_rec n1 X1 cd1 = close_contd_wrt_typ_rec n1 X1 cd2 ->
  cd1 = cd2) /\
(forall cs1 cs2 X1 n1,
  close_conts_wrt_typ_rec n1 X1 cs1 = close_conts_wrt_typ_rec n1 X1 cs2 ->
  cs1 = cs2).
Proof.
apply_mutual_ind contd_conts_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_inj :
forall cd1 cd2 X1 n1,
  close_contd_wrt_typ_rec n1 X1 cd1 = close_contd_wrt_typ_rec n1 X1 cd2 ->
  cd1 = cd2.
Proof.
pose proof close_contd_wrt_typ_rec_inj_close_conts_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_contd_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_conts_wrt_typ_rec_inj :
forall cs1 cs2 X1 n1,
  close_conts_wrt_typ_rec n1 X1 cs1 = close_conts_wrt_typ_rec n1 X1 cs2 ->
  cs1 = cs2.
Proof.
pose proof close_contd_wrt_typ_rec_inj_close_conts_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_conts_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_inj_close_conts_wrt_exp_rec_inj_mutual :
(forall cd1 cd2 x1 n1,
  close_contd_wrt_exp_rec n1 x1 cd1 = close_contd_wrt_exp_rec n1 x1 cd2 ->
  cd1 = cd2) /\
(forall cs1 cs2 x1 n1,
  close_conts_wrt_exp_rec n1 x1 cs1 = close_conts_wrt_exp_rec n1 x1 cs2 ->
  cs1 = cs2).
Proof.
apply_mutual_ind contd_conts_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_inj :
forall cd1 cd2 x1 n1,
  close_contd_wrt_exp_rec n1 x1 cd1 = close_contd_wrt_exp_rec n1 x1 cd2 ->
  cd1 = cd2.
Proof.
pose proof close_contd_wrt_exp_rec_inj_close_conts_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_contd_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_conts_wrt_exp_rec_inj :
forall cs1 cs2 x1 n1,
  close_conts_wrt_exp_rec n1 x1 cs1 = close_conts_wrt_exp_rec n1 x1 cs2 ->
  cs1 = cs2.
Proof.
pose proof close_contd_wrt_exp_rec_inj_close_conts_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_conts_wrt_exp_rec_inj : lngen.

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

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_contd_wrt_typ_inj :
forall cd1 cd2 X1,
  close_contd_wrt_typ X1 cd1 = close_contd_wrt_typ X1 cd2 ->
  cd1 = cd2.
Proof.
unfold close_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_contd_wrt_typ_inj : lngen.

Lemma close_conts_wrt_typ_inj :
forall cs1 cs2 X1,
  close_conts_wrt_typ X1 cs1 = close_conts_wrt_typ X1 cs2 ->
  cs1 = cs2.
Proof.
unfold close_conts_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_conts_wrt_typ_inj : lngen.

Lemma close_contd_wrt_exp_inj :
forall cd1 cd2 x1,
  close_contd_wrt_exp x1 cd1 = close_contd_wrt_exp x1 cd2 ->
  cd1 = cd2.
Proof.
unfold close_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_contd_wrt_exp_inj : lngen.

Lemma close_conts_wrt_exp_inj :
forall cs1 cs2 x1,
  close_conts_wrt_exp x1 cs1 = close_conts_wrt_exp x1 cs2 ->
  cs1 = cs2.
Proof.
unfold close_conts_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_conts_wrt_exp_inj : lngen.

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

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1,
  X1 `notin` ftvar_in_contd cd1 ->
  close_contd_wrt_typ_rec n1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1) = cd1) /\
(forall cs1 X1 n1,
  X1 `notin` ftvar_in_conts cs1 ->
  close_conts_wrt_typ_rec n1 X1 (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1) = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_open_contd_wrt_typ_rec :
forall cd1 X1 n1,
  X1 `notin` ftvar_in_contd cd1 ->
  close_contd_wrt_typ_rec n1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1) = cd1.
Proof.
pose proof close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_rec_open_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_rec_open_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_conts_wrt_typ_rec_open_conts_wrt_typ_rec :
forall cs1 X1 n1,
  X1 `notin` ftvar_in_conts cs1 ->
  close_conts_wrt_typ_rec n1 X1 (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1) = cs1.
Proof.
pose proof close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_conts_wrt_typ_rec_open_conts_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_conts_wrt_typ_rec_open_conts_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1,
  x1 `notin` fvar_in_contd cd1 ->
  close_contd_wrt_exp_rec n1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1) = cd1) /\
(forall cs1 x1 n1,
  x1 `notin` fvar_in_conts cs1 ->
  close_conts_wrt_exp_rec n1 x1 (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1) = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_open_contd_wrt_exp_rec :
forall cd1 x1 n1,
  x1 `notin` fvar_in_contd cd1 ->
  close_contd_wrt_exp_rec n1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1) = cd1.
Proof.
pose proof close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_rec_open_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_rec_open_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_conts_wrt_exp_rec_open_conts_wrt_exp_rec :
forall cs1 x1 n1,
  x1 `notin` fvar_in_conts cs1 ->
  close_conts_wrt_exp_rec n1 x1 (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1) = cs1.
Proof.
pose proof close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_conts_wrt_exp_rec_open_conts_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_conts_wrt_exp_rec_open_conts_wrt_exp_rec using solve [auto] : lngen.

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

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (typ_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

Lemma close_contd_wrt_typ_open_contd_wrt_typ :
forall cd1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  close_contd_wrt_typ X1 (open_contd_wrt_typ cd1 (typ_var_f X1)) = cd1.
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_open_contd_wrt_typ : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_open_contd_wrt_typ using solve [auto] : lngen.

Lemma close_conts_wrt_typ_open_conts_wrt_typ :
forall cs1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  close_conts_wrt_typ X1 (open_conts_wrt_typ cs1 (typ_var_f X1)) = cs1.
Proof.
unfold close_conts_wrt_typ; unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_conts_wrt_typ_open_conts_wrt_typ : lngen.
#[export] Hint Rewrite close_conts_wrt_typ_open_conts_wrt_typ using solve [auto] : lngen.

Lemma close_contd_wrt_exp_open_contd_wrt_exp :
forall cd1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  close_contd_wrt_exp x1 (open_contd_wrt_exp cd1 (exp_var_f x1)) = cd1.
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_open_contd_wrt_exp : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_open_contd_wrt_exp using solve [auto] : lngen.

Lemma close_conts_wrt_exp_open_conts_wrt_exp :
forall cs1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  close_conts_wrt_exp x1 (open_conts_wrt_exp cs1 (exp_var_f x1)) = cs1.
Proof.
unfold close_conts_wrt_exp; unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_conts_wrt_exp_open_conts_wrt_exp : lngen.
#[export] Hint Rewrite close_conts_wrt_exp_open_conts_wrt_exp using solve [auto] : lngen.

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

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_close_contd_wrt_typ_rec_open_conts_wrt_typ_rec_close_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1,
  open_contd_wrt_typ_rec n1 (typ_var_f X1) (close_contd_wrt_typ_rec n1 X1 cd1) = cd1) /\
(forall cs1 X1 n1,
  open_conts_wrt_typ_rec n1 (typ_var_f X1) (close_conts_wrt_typ_rec n1 X1 cs1) = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_close_contd_wrt_typ_rec :
forall cd1 X1 n1,
  open_contd_wrt_typ_rec n1 (typ_var_f X1) (close_contd_wrt_typ_rec n1 X1 cd1) = cd1.
Proof.
pose proof open_contd_wrt_typ_rec_close_contd_wrt_typ_rec_open_conts_wrt_typ_rec_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_rec_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_rec_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_conts_wrt_typ_rec_close_conts_wrt_typ_rec :
forall cs1 X1 n1,
  open_conts_wrt_typ_rec n1 (typ_var_f X1) (close_conts_wrt_typ_rec n1 X1 cs1) = cs1.
Proof.
pose proof open_contd_wrt_typ_rec_close_contd_wrt_typ_rec_open_conts_wrt_typ_rec_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_conts_wrt_typ_rec_close_conts_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_conts_wrt_typ_rec_close_conts_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_close_contd_wrt_exp_rec_open_conts_wrt_exp_rec_close_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1,
  open_contd_wrt_exp_rec n1 (exp_var_f x1) (close_contd_wrt_exp_rec n1 x1 cd1) = cd1) /\
(forall cs1 x1 n1,
  open_conts_wrt_exp_rec n1 (exp_var_f x1) (close_conts_wrt_exp_rec n1 x1 cs1) = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_close_contd_wrt_exp_rec :
forall cd1 x1 n1,
  open_contd_wrt_exp_rec n1 (exp_var_f x1) (close_contd_wrt_exp_rec n1 x1 cd1) = cd1.
Proof.
pose proof open_contd_wrt_exp_rec_close_contd_wrt_exp_rec_open_conts_wrt_exp_rec_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_rec_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_rec_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_conts_wrt_exp_rec_close_conts_wrt_exp_rec :
forall cs1 x1 n1,
  open_conts_wrt_exp_rec n1 (exp_var_f x1) (close_conts_wrt_exp_rec n1 x1 cs1) = cs1.
Proof.
pose proof open_contd_wrt_exp_rec_close_contd_wrt_exp_rec_open_conts_wrt_exp_rec_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_conts_wrt_exp_rec_close_conts_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_conts_wrt_exp_rec_close_conts_wrt_exp_rec using solve [auto] : lngen.

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

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (typ_var_f X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma open_contd_wrt_typ_close_contd_wrt_typ :
forall cd1 X1,
  open_contd_wrt_typ (close_contd_wrt_typ X1 cd1) (typ_var_f X1) = cd1.
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_close_contd_wrt_typ using solve [auto] : lngen.

Lemma open_conts_wrt_typ_close_conts_wrt_typ :
forall cs1 X1,
  open_conts_wrt_typ (close_conts_wrt_typ X1 cs1) (typ_var_f X1) = cs1.
Proof.
unfold close_conts_wrt_typ; unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_conts_wrt_typ_close_conts_wrt_typ : lngen.
#[export] Hint Rewrite open_conts_wrt_typ_close_conts_wrt_typ using solve [auto] : lngen.

Lemma open_contd_wrt_exp_close_contd_wrt_exp :
forall cd1 x1,
  open_contd_wrt_exp (close_contd_wrt_exp x1 cd1) (exp_var_f x1) = cd1.
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_close_contd_wrt_exp using solve [auto] : lngen.

Lemma open_conts_wrt_exp_close_conts_wrt_exp :
forall cs1 x1,
  open_conts_wrt_exp (close_conts_wrt_exp x1 cs1) (exp_var_f x1) = cs1.
Proof.
unfold close_conts_wrt_exp; unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_conts_wrt_exp_close_conts_wrt_exp : lngen.
#[export] Hint Rewrite open_conts_wrt_exp_close_conts_wrt_exp using solve [auto] : lngen.

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

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_inj_open_conts_wrt_typ_rec_inj_mutual :
(forall cd2 cd1 X1 n1,
  X1 `notin` ftvar_in_contd cd2 ->
  X1 `notin` ftvar_in_contd cd1 ->
  open_contd_wrt_typ_rec n1 (typ_var_f X1) cd2 = open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1 ->
  cd2 = cd1) /\
(forall cs2 cs1 X1 n1,
  X1 `notin` ftvar_in_conts cs2 ->
  X1 `notin` ftvar_in_conts cs1 ->
  open_conts_wrt_typ_rec n1 (typ_var_f X1) cs2 = open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1 ->
  cs2 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_inj :
forall cd2 cd1 X1 n1,
  X1 `notin` ftvar_in_contd cd2 ->
  X1 `notin` ftvar_in_contd cd1 ->
  open_contd_wrt_typ_rec n1 (typ_var_f X1) cd2 = open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1 ->
  cd2 = cd1.
Proof.
pose proof open_contd_wrt_typ_rec_inj_open_conts_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_contd_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_conts_wrt_typ_rec_inj :
forall cs2 cs1 X1 n1,
  X1 `notin` ftvar_in_conts cs2 ->
  X1 `notin` ftvar_in_conts cs1 ->
  open_conts_wrt_typ_rec n1 (typ_var_f X1) cs2 = open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1 ->
  cs2 = cs1.
Proof.
pose proof open_contd_wrt_typ_rec_inj_open_conts_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_conts_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_inj_open_conts_wrt_exp_rec_inj_mutual :
(forall cd2 cd1 x1 n1,
  x1 `notin` fvar_in_contd cd2 ->
  x1 `notin` fvar_in_contd cd1 ->
  open_contd_wrt_exp_rec n1 (exp_var_f x1) cd2 = open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1 ->
  cd2 = cd1) /\
(forall cs2 cs1 x1 n1,
  x1 `notin` fvar_in_conts cs2 ->
  x1 `notin` fvar_in_conts cs1 ->
  open_conts_wrt_exp_rec n1 (exp_var_f x1) cs2 = open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1 ->
  cs2 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_inj :
forall cd2 cd1 x1 n1,
  x1 `notin` fvar_in_contd cd2 ->
  x1 `notin` fvar_in_contd cd1 ->
  open_contd_wrt_exp_rec n1 (exp_var_f x1) cd2 = open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1 ->
  cd2 = cd1.
Proof.
pose proof open_contd_wrt_exp_rec_inj_open_conts_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_contd_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_conts_wrt_exp_rec_inj :
forall cs2 cs1 x1 n1,
  x1 `notin` fvar_in_conts cs2 ->
  x1 `notin` fvar_in_conts cs1 ->
  open_conts_wrt_exp_rec n1 (exp_var_f x1) cs2 = open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1 ->
  cs2 = cs1.
Proof.
pose proof open_contd_wrt_exp_rec_inj_open_conts_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_conts_wrt_exp_rec_inj : lngen.

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

Lemma open_contd_wrt_typ_inj :
forall cd2 cd1 X1,
  X1 `notin` ftvar_in_contd cd2 ->
  X1 `notin` ftvar_in_contd cd1 ->
  open_contd_wrt_typ cd2 (typ_var_f X1) = open_contd_wrt_typ cd1 (typ_var_f X1) ->
  cd2 = cd1.
Proof.
unfold open_contd_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_contd_wrt_typ_inj : lngen.

Lemma open_conts_wrt_typ_inj :
forall cs2 cs1 X1,
  X1 `notin` ftvar_in_conts cs2 ->
  X1 `notin` ftvar_in_conts cs1 ->
  open_conts_wrt_typ cs2 (typ_var_f X1) = open_conts_wrt_typ cs1 (typ_var_f X1) ->
  cs2 = cs1.
Proof.
unfold open_conts_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_conts_wrt_typ_inj : lngen.

Lemma open_contd_wrt_exp_inj :
forall cd2 cd1 x1,
  x1 `notin` fvar_in_contd cd2 ->
  x1 `notin` fvar_in_contd cd1 ->
  open_contd_wrt_exp cd2 (exp_var_f x1) = open_contd_wrt_exp cd1 (exp_var_f x1) ->
  cd2 = cd1.
Proof.
unfold open_contd_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_contd_wrt_exp_inj : lngen.

Lemma open_conts_wrt_exp_inj :
forall cs2 cs1 x1,
  x1 `notin` fvar_in_conts cs2 ->
  x1 `notin` fvar_in_conts cs1 ->
  open_conts_wrt_exp cs2 (exp_var_f x1) = open_conts_wrt_exp cs1 (exp_var_f x1) ->
  cs2 = cs1.
Proof.
unfold open_conts_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_conts_wrt_exp_inj : lngen.

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

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_contd_wrt_typ_of_lc_contd_degree_conts_wrt_typ_of_lc_conts_mutual :
(forall cd1,
  lc_contd cd1 ->
  degree_contd_wrt_typ 0 cd1) /\
(forall cs1,
  lc_conts cs1 ->
  degree_conts_wrt_typ 0 cs1).
Proof.
apply_mutual_ind lc_contd_lc_conts_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_contd_wrt_typ_of_lc_contd :
forall cd1,
  lc_contd cd1 ->
  degree_contd_wrt_typ 0 cd1.
Proof.
pose proof degree_contd_wrt_typ_of_lc_contd_degree_conts_wrt_typ_of_lc_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_typ_of_lc_contd : lngen.

Lemma degree_conts_wrt_typ_of_lc_conts :
forall cs1,
  lc_conts cs1 ->
  degree_conts_wrt_typ 0 cs1.
Proof.
pose proof degree_contd_wrt_typ_of_lc_contd_degree_conts_wrt_typ_of_lc_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_typ_of_lc_conts : lngen.

(* begin hide *)

Lemma degree_contd_wrt_exp_of_lc_contd_degree_conts_wrt_exp_of_lc_conts_mutual :
(forall cd1,
  lc_contd cd1 ->
  degree_contd_wrt_exp 0 cd1) /\
(forall cs1,
  lc_conts cs1 ->
  degree_conts_wrt_exp 0 cs1).
Proof.
apply_mutual_ind lc_contd_lc_conts_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_contd_wrt_exp_of_lc_contd :
forall cd1,
  lc_contd cd1 ->
  degree_contd_wrt_exp 0 cd1.
Proof.
pose proof degree_contd_wrt_exp_of_lc_contd_degree_conts_wrt_exp_of_lc_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_contd_wrt_exp_of_lc_contd : lngen.

Lemma degree_conts_wrt_exp_of_lc_conts :
forall cs1,
  lc_conts cs1 ->
  degree_conts_wrt_exp 0 cs1.
Proof.
pose proof degree_contd_wrt_exp_of_lc_contd_degree_conts_wrt_exp_of_lc_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_conts_wrt_exp_of_lc_conts : lngen.

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

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
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

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_degree : lngen.

(* begin hide *)

Lemma lc_contd_of_degree_lc_conts_of_degree_size_mutual :
forall i1,
(forall cd1,
  size_contd cd1 = i1 ->
  degree_contd_wrt_typ 0 cd1 ->
  degree_contd_wrt_exp 0 cd1 ->
  lc_contd cd1) /\
(forall cs1,
  size_conts cs1 = i1 ->
  degree_conts_wrt_typ 0 cs1 ->
  degree_conts_wrt_exp 0 cs1 ->
  lc_conts cs1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind contd_conts_mutind;
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

Lemma lc_contd_of_degree :
forall cd1,
  degree_contd_wrt_typ 0 cd1 ->
  degree_contd_wrt_exp 0 cd1 ->
  lc_contd cd1.
Proof.
intros cd1; intros;
pose proof (lc_contd_of_degree_lc_conts_of_degree_size_mutual (size_contd cd1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_contd_of_degree : lngen.

Lemma lc_conts_of_degree :
forall cs1,
  degree_conts_wrt_typ 0 cs1 ->
  degree_conts_wrt_exp 0 cs1 ->
  lc_conts cs1.
Proof.
intros cs1; intros;
pose proof (lc_contd_of_degree_lc_conts_of_degree_size_mutual (size_conts cs1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_conts_of_degree : lngen.

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

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Ltac contd_conts_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_contd_wrt_typ_of_lc_contd in J1;
              let J2 := fresh in pose proof H as J2; apply degree_contd_wrt_exp_of_lc_contd in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_conts_wrt_typ_of_lc_conts in J1;
              let J2 := fresh in pose proof H as J2; apply degree_conts_wrt_exp_of_lc_conts in J2; clear H
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
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_tabs_exists :
forall X1 e1,
  lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)) ->
  lc_exp (exp_tabs e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
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
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_typ : lngen.

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
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_contd_wrt_typ :
forall cd1 A1,
  body_contd_wrt_typ cd1 ->
  lc_typ A1 ->
  lc_contd (open_contd_wrt_typ cd1 A1).
Proof.
unfold body_contd_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
contd_conts_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_contd_wrt_typ : lngen.

Lemma lc_body_conts_wrt_typ :
forall cs1 A1,
  body_conts_wrt_typ cs1 ->
  lc_typ A1 ->
  lc_conts (open_conts_wrt_typ cs1 A1).
Proof.
unfold body_conts_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
contd_conts_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_conts_wrt_typ : lngen.

Lemma lc_body_contd_wrt_exp :
forall cd1 e1,
  body_contd_wrt_exp cd1 ->
  lc_exp e1 ->
  lc_contd (open_contd_wrt_exp cd1 e1).
Proof.
unfold body_contd_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
contd_conts_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_contd_wrt_exp : lngen.

Lemma lc_body_conts_wrt_exp :
forall cs1 e1,
  body_conts_wrt_exp cs1 ->
  lc_exp e1 ->
  lc_conts (open_conts_wrt_exp cs1 e1).
Proof.
unfold body_conts_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
contd_conts_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_conts_wrt_exp : lngen.

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
forall e1,
  lc_exp (exp_tabs e1) ->
  body_exp_wrt_typ e1.
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

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_contd_unique_lc_conts_unique_mutual :
(forall cd1 (proof2 proof3 : lc_contd cd1), proof2 = proof3) /\
(forall cs1 (proof2 proof3 : lc_conts cs1), proof2 = proof3).
Proof.
apply_mutual_ind lc_contd_lc_conts_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_contd_unique :
forall cd1 (proof2 proof3 : lc_contd cd1), proof2 = proof3.
Proof.
pose proof lc_contd_unique_lc_conts_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_contd_unique : lngen.

Lemma lc_conts_unique :
forall cs1 (proof2 proof3 : lc_conts cs1), proof2 = proof3.
Proof.
pose proof lc_contd_unique_lc_conts_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_conts_unique : lngen.

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

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_contd_of_lc_set_contd_lc_conts_of_lc_set_conts_mutual :
(forall cd1, lc_set_contd cd1 -> lc_contd cd1) /\
(forall cs1, lc_set_conts cs1 -> lc_conts cs1).
Proof.
apply_mutual_ind lc_set_contd_lc_set_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_contd_of_lc_set_contd :
forall cd1, lc_set_contd cd1 -> lc_contd cd1.
Proof.
pose proof lc_contd_of_lc_set_contd_lc_conts_of_lc_set_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_contd_of_lc_set_contd : lngen.

Lemma lc_conts_of_lc_set_conts :
forall cs1, lc_set_conts cs1 -> lc_conts cs1.
Proof.
pose proof lc_contd_of_lc_set_contd_lc_conts_of_lc_set_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_conts_of_lc_set_conts : lngen.

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

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
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

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_set_contd_of_lc_contd_lc_set_conts_of_lc_conts_size_mutual :
forall i1,
(forall cd1,
  size_contd cd1 = i1 ->
  lc_contd cd1 ->
  lc_set_contd cd1) *
(forall cs1,
  size_conts cs1 = i1 ->
  lc_conts cs1 ->
  lc_set_conts cs1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind contd_conts_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_contd_of_lc_contd
 | apply lc_set_conts_of_lc_conts
 | apply lc_set_exp_of_lc_exp
 | apply lc_set_typ_of_lc_typ
 | apply lc_set_contd_of_lc_contd
 | apply lc_set_conts_of_lc_conts
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

Lemma lc_set_contd_of_lc_contd :
forall cd1,
  lc_contd cd1 ->
  lc_set_contd cd1.
Proof.
intros cd1; intros;
pose proof (lc_set_contd_of_lc_contd_lc_set_conts_of_lc_conts_size_mutual (size_contd cd1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_contd_of_lc_contd : lngen.

Lemma lc_set_conts_of_lc_conts :
forall cs1,
  lc_conts cs1 ->
  lc_set_conts cs1.
Proof.
intros cs1; intros;
pose proof (lc_set_contd_of_lc_contd_lc_set_conts_of_lc_conts_size_mutual (size_conts cs1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_conts_of_lc_conts : lngen.

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
 | apply lc_set_contd_of_lc_contd
 | apply lc_set_conts_of_lc_conts
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

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_degree_contd_wrt_typ_close_conts_wrt_typ_rec_degree_conts_wrt_typ_mutual :
(forall cd1 X1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  X1 `notin` ftvar_in_contd cd1 ->
  close_contd_wrt_typ_rec n1 X1 cd1 = cd1) /\
(forall cs1 X1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  X1 `notin` ftvar_in_conts cs1 ->
  close_conts_wrt_typ_rec n1 X1 cs1 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_typ_rec_degree_contd_wrt_typ :
forall cd1 X1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  X1 `notin` ftvar_in_contd cd1 ->
  close_contd_wrt_typ_rec n1 X1 cd1 = cd1.
Proof.
pose proof close_contd_wrt_typ_rec_degree_contd_wrt_typ_close_conts_wrt_typ_rec_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_rec_degree_contd_wrt_typ : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_rec_degree_contd_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_conts_wrt_typ_rec_degree_conts_wrt_typ :
forall cs1 X1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  X1 `notin` ftvar_in_conts cs1 ->
  close_conts_wrt_typ_rec n1 X1 cs1 = cs1.
Proof.
pose proof close_contd_wrt_typ_rec_degree_contd_wrt_typ_close_conts_wrt_typ_rec_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_conts_wrt_typ_rec_degree_conts_wrt_typ : lngen.
#[export] Hint Rewrite close_conts_wrt_typ_rec_degree_conts_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_degree_contd_wrt_exp_close_conts_wrt_exp_rec_degree_conts_wrt_exp_mutual :
(forall cd1 x1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  x1 `notin` fvar_in_contd cd1 ->
  close_contd_wrt_exp_rec n1 x1 cd1 = cd1) /\
(forall cs1 x1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  x1 `notin` fvar_in_conts cs1 ->
  close_conts_wrt_exp_rec n1 x1 cs1 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_contd_wrt_exp_rec_degree_contd_wrt_exp :
forall cd1 x1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  x1 `notin` fvar_in_contd cd1 ->
  close_contd_wrt_exp_rec n1 x1 cd1 = cd1.
Proof.
pose proof close_contd_wrt_exp_rec_degree_contd_wrt_exp_close_conts_wrt_exp_rec_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_rec_degree_contd_wrt_exp : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_rec_degree_contd_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_conts_wrt_exp_rec_degree_conts_wrt_exp :
forall cs1 x1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  x1 `notin` fvar_in_conts cs1 ->
  close_conts_wrt_exp_rec n1 x1 cs1 = cs1.
Proof.
pose proof close_contd_wrt_exp_rec_degree_contd_wrt_exp_close_conts_wrt_exp_rec_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_conts_wrt_exp_rec_degree_conts_wrt_exp : lngen.
#[export] Hint Rewrite close_conts_wrt_exp_rec_degree_conts_wrt_exp using solve [auto] : lngen.

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

Lemma close_contd_wrt_typ_lc_contd :
forall cd1 X1,
  lc_contd cd1 ->
  X1 `notin` ftvar_in_contd cd1 ->
  close_contd_wrt_typ X1 cd1 = cd1.
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_typ_lc_contd : lngen.
#[export] Hint Rewrite close_contd_wrt_typ_lc_contd using solve [auto] : lngen.

Lemma close_conts_wrt_typ_lc_conts :
forall cs1 X1,
  lc_conts cs1 ->
  X1 `notin` ftvar_in_conts cs1 ->
  close_conts_wrt_typ X1 cs1 = cs1.
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_conts_wrt_typ_lc_conts : lngen.
#[export] Hint Rewrite close_conts_wrt_typ_lc_conts using solve [auto] : lngen.

Lemma close_contd_wrt_exp_lc_contd :
forall cd1 x1,
  lc_contd cd1 ->
  x1 `notin` fvar_in_contd cd1 ->
  close_contd_wrt_exp x1 cd1 = cd1.
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_contd_wrt_exp_lc_contd : lngen.
#[export] Hint Rewrite close_contd_wrt_exp_lc_contd using solve [auto] : lngen.

Lemma close_conts_wrt_exp_lc_conts :
forall cs1 x1,
  lc_conts cs1 ->
  x1 `notin` fvar_in_conts cs1 ->
  close_conts_wrt_exp x1 cs1 = cs1.
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_conts_wrt_exp_lc_conts : lngen.
#[export] Hint Rewrite close_conts_wrt_exp_lc_conts using solve [auto] : lngen.

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

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_degree_contd_wrt_typ_open_conts_wrt_typ_rec_degree_conts_wrt_typ_mutual :
(forall cd1 A1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  open_contd_wrt_typ_rec n1 A1 cd1 = cd1) /\
(forall cs1 A1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  open_conts_wrt_typ_rec n1 A1 cs1 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_typ_rec_degree_contd_wrt_typ :
forall cd1 A1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  open_contd_wrt_typ_rec n1 A1 cd1 = cd1.
Proof.
pose proof open_contd_wrt_typ_rec_degree_contd_wrt_typ_open_conts_wrt_typ_rec_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_rec_degree_contd_wrt_typ : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_rec_degree_contd_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_conts_wrt_typ_rec_degree_conts_wrt_typ :
forall cs1 A1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  open_conts_wrt_typ_rec n1 A1 cs1 = cs1.
Proof.
pose proof open_contd_wrt_typ_rec_degree_contd_wrt_typ_open_conts_wrt_typ_rec_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_conts_wrt_typ_rec_degree_conts_wrt_typ : lngen.
#[export] Hint Rewrite open_conts_wrt_typ_rec_degree_conts_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_degree_contd_wrt_exp_open_conts_wrt_exp_rec_degree_conts_wrt_exp_mutual :
(forall cd1 e1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  open_contd_wrt_exp_rec n1 e1 cd1 = cd1) /\
(forall cs1 e1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  open_conts_wrt_exp_rec n1 e1 cs1 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_contd_wrt_exp_rec_degree_contd_wrt_exp :
forall cd1 e1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  open_contd_wrt_exp_rec n1 e1 cd1 = cd1.
Proof.
pose proof open_contd_wrt_exp_rec_degree_contd_wrt_exp_open_conts_wrt_exp_rec_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_rec_degree_contd_wrt_exp : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_rec_degree_contd_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_conts_wrt_exp_rec_degree_conts_wrt_exp :
forall cs1 e1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  open_conts_wrt_exp_rec n1 e1 cs1 = cs1.
Proof.
pose proof open_contd_wrt_exp_rec_degree_contd_wrt_exp_open_conts_wrt_exp_rec_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_conts_wrt_exp_rec_degree_conts_wrt_exp : lngen.
#[export] Hint Rewrite open_conts_wrt_exp_rec_degree_conts_wrt_exp using solve [auto] : lngen.

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

Lemma open_exp_wrt_typ_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 A1 = e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma open_contd_wrt_typ_lc_contd :
forall cd1 A1,
  lc_contd cd1 ->
  open_contd_wrt_typ cd1 A1 = cd1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_typ_lc_contd : lngen.
#[export] Hint Rewrite open_contd_wrt_typ_lc_contd using solve [auto] : lngen.

Lemma open_conts_wrt_typ_lc_conts :
forall cs1 A1,
  lc_conts cs1 ->
  open_conts_wrt_typ cs1 A1 = cs1.
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_conts_wrt_typ_lc_conts : lngen.
#[export] Hint Rewrite open_conts_wrt_typ_lc_conts using solve [auto] : lngen.

Lemma open_contd_wrt_exp_lc_contd :
forall cd1 e1,
  lc_contd cd1 ->
  open_contd_wrt_exp cd1 e1 = cd1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_contd_wrt_exp_lc_contd : lngen.
#[export] Hint Rewrite open_contd_wrt_exp_lc_contd using solve [auto] : lngen.

Lemma open_conts_wrt_exp_lc_conts :
forall cs1 e1,
  lc_conts cs1 ->
  open_conts_wrt_exp cs1 e1 = cs1.
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_conts_wrt_exp_lc_conts : lngen.
#[export] Hint Rewrite open_conts_wrt_exp_lc_conts using solve [auto] : lngen.

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

Lemma ftvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  ftvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  ftvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
pose proof fvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_close_contd_wrt_typ_rec_ftvar_in_conts_close_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1,
  ftvar_in_contd (close_contd_wrt_typ_rec n1 X1 cd1) [=] remove X1 (ftvar_in_contd cd1)) /\
(forall cs1 X1 n1,
  ftvar_in_conts (close_conts_wrt_typ_rec n1 X1 cs1) [=] remove X1 (ftvar_in_conts cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_close_contd_wrt_typ_rec :
forall cd1 X1 n1,
  ftvar_in_contd (close_contd_wrt_typ_rec n1 X1 cd1) [=] remove X1 (ftvar_in_contd cd1).
Proof.
pose proof ftvar_in_contd_close_contd_wrt_typ_rec_ftvar_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_conts_close_conts_wrt_typ_rec :
forall cs1 X1 n1,
  ftvar_in_conts (close_conts_wrt_typ_rec n1 X1 cs1) [=] remove X1 (ftvar_in_conts cs1).
Proof.
pose proof ftvar_in_contd_close_contd_wrt_typ_rec_ftvar_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_close_conts_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_conts_close_conts_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_close_contd_wrt_exp_rec_ftvar_in_conts_close_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1,
  ftvar_in_contd (close_contd_wrt_exp_rec n1 x1 cd1) [=] ftvar_in_contd cd1) /\
(forall cs1 x1 n1,
  ftvar_in_conts (close_conts_wrt_exp_rec n1 x1 cs1) [=] ftvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_close_contd_wrt_exp_rec :
forall cd1 x1 n1,
  ftvar_in_contd (close_contd_wrt_exp_rec n1 x1 cd1) [=] ftvar_in_contd cd1.
Proof.
pose proof ftvar_in_contd_close_contd_wrt_exp_rec_ftvar_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_conts_close_conts_wrt_exp_rec :
forall cs1 x1 n1,
  ftvar_in_conts (close_conts_wrt_exp_rec n1 x1 cs1) [=] ftvar_in_conts cs1.
Proof.
pose proof ftvar_in_contd_close_contd_wrt_exp_rec_ftvar_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_close_conts_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_conts_close_conts_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_close_contd_wrt_typ_rec_fvar_in_conts_close_conts_wrt_typ_rec_mutual :
(forall cd1 X1 n1,
  fvar_in_contd (close_contd_wrt_typ_rec n1 X1 cd1) [=] fvar_in_contd cd1) /\
(forall cs1 X1 n1,
  fvar_in_conts (close_conts_wrt_typ_rec n1 X1 cs1) [=] fvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_close_contd_wrt_typ_rec :
forall cd1 X1 n1,
  fvar_in_contd (close_contd_wrt_typ_rec n1 X1 cd1) [=] fvar_in_contd cd1.
Proof.
pose proof fvar_in_contd_close_contd_wrt_typ_rec_fvar_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_conts_close_conts_wrt_typ_rec :
forall cs1 X1 n1,
  fvar_in_conts (close_conts_wrt_typ_rec n1 X1 cs1) [=] fvar_in_conts cs1.
Proof.
pose proof fvar_in_contd_close_contd_wrt_typ_rec_fvar_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_close_conts_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_conts_close_conts_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_close_contd_wrt_exp_rec_fvar_in_conts_close_conts_wrt_exp_rec_mutual :
(forall cd1 x1 n1,
  fvar_in_contd (close_contd_wrt_exp_rec n1 x1 cd1) [=] remove x1 (fvar_in_contd cd1)) /\
(forall cs1 x1 n1,
  fvar_in_conts (close_conts_wrt_exp_rec n1 x1 cs1) [=] remove x1 (fvar_in_conts cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_close_contd_wrt_exp_rec :
forall cd1 x1 n1,
  fvar_in_contd (close_contd_wrt_exp_rec n1 x1 cd1) [=] remove x1 (fvar_in_contd cd1).
Proof.
pose proof fvar_in_contd_close_contd_wrt_exp_rec_fvar_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_conts_close_conts_wrt_exp_rec :
forall cs1 x1 n1,
  fvar_in_conts (close_conts_wrt_exp_rec n1 x1 cs1) [=] remove x1 (fvar_in_conts cs1).
Proof.
pose proof fvar_in_contd_close_contd_wrt_exp_rec_fvar_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_close_conts_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_conts_close_conts_wrt_exp_rec using solve [auto] : lngen.

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

Lemma ftvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  ftvar_in_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  ftvar_in_exp (close_exp_wrt_exp x1 e1) [=] ftvar_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  fvar_in_exp (close_exp_wrt_typ X1 e1) [=] fvar_in_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fvar_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_contd_close_contd_wrt_typ :
forall cd1 X1,
  ftvar_in_contd (close_contd_wrt_typ X1 cd1) [=] remove X1 (ftvar_in_contd cd1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_conts_close_conts_wrt_typ :
forall cs1 X1,
  ftvar_in_conts (close_conts_wrt_typ X1 cs1) [=] remove X1 (ftvar_in_conts cs1).
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_conts_close_conts_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_conts_close_conts_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_contd_close_contd_wrt_exp :
forall cd1 x1,
  ftvar_in_contd (close_contd_wrt_exp x1 cd1) [=] ftvar_in_contd cd1.
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_contd_close_contd_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_conts_close_conts_wrt_exp :
forall cs1 x1,
  ftvar_in_conts (close_conts_wrt_exp x1 cs1) [=] ftvar_in_conts cs1.
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_conts_close_conts_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_conts_close_conts_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_contd_close_contd_wrt_typ :
forall cd1 X1,
  fvar_in_contd (close_contd_wrt_typ X1 cd1) [=] fvar_in_contd cd1.
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_conts_close_conts_wrt_typ :
forall cs1 X1,
  fvar_in_conts (close_conts_wrt_typ X1 cs1) [=] fvar_in_conts cs1.
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_conts_close_conts_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_conts_close_conts_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_contd_close_contd_wrt_exp :
forall cd1 x1,
  fvar_in_contd (close_contd_wrt_exp x1 cd1) [=] remove x1 (fvar_in_contd cd1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_close_contd_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_contd_close_contd_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_conts_close_conts_wrt_exp :
forall cs1 x1,
  fvar_in_conts (close_conts_wrt_exp x1 cs1) [=] remove x1 (fvar_in_conts cs1).
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_conts_close_conts_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_conts_close_conts_wrt_exp using solve [auto] : lngen.

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

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_typ_rec_lower_ftvar_in_conts_open_conts_wrt_typ_rec_lower_mutual :
(forall cd1 A1 n1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1)) /\
(forall cs1 A1 n1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_typ_rec_lower :
forall cd1 A1 n1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1).
Proof.
pose proof ftvar_in_contd_open_contd_wrt_typ_rec_lower_ftvar_in_conts_open_conts_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_conts_open_conts_wrt_typ_rec_lower :
forall cs1 A1 n1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1).
Proof.
pose proof ftvar_in_contd_open_contd_wrt_typ_rec_lower_ftvar_in_conts_open_conts_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_exp_rec_lower_ftvar_in_conts_open_conts_wrt_exp_rec_lower_mutual :
(forall cd1 e1 n1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1)) /\
(forall cs1 e1 n1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_exp_rec_lower :
forall cd1 e1 n1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1).
Proof.
pose proof ftvar_in_contd_open_contd_wrt_exp_rec_lower_ftvar_in_conts_open_conts_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_conts_open_conts_wrt_exp_rec_lower :
forall cs1 e1 n1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1).
Proof.
pose proof ftvar_in_contd_open_contd_wrt_exp_rec_lower_ftvar_in_conts_open_conts_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_typ_rec_lower_fvar_in_conts_open_conts_wrt_typ_rec_lower_mutual :
(forall cd1 A1 n1,
  fvar_in_contd cd1 [<=] fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1)) /\
(forall cs1 A1 n1,
  fvar_in_conts cs1 [<=] fvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_typ_rec_lower :
forall cd1 A1 n1,
  fvar_in_contd cd1 [<=] fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1).
Proof.
pose proof fvar_in_contd_open_contd_wrt_typ_rec_lower_fvar_in_conts_open_conts_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_conts_open_conts_wrt_typ_rec_lower :
forall cs1 A1 n1,
  fvar_in_conts cs1 [<=] fvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1).
Proof.
pose proof fvar_in_contd_open_contd_wrt_typ_rec_lower_fvar_in_conts_open_conts_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_exp_rec_lower_fvar_in_conts_open_conts_wrt_exp_rec_lower_mutual :
(forall cd1 e1 n1,
  fvar_in_contd cd1 [<=] fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1)) /\
(forall cs1 e1 n1,
  fvar_in_conts cs1 [<=] fvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_exp_rec_lower :
forall cd1 e1 n1,
  fvar_in_contd cd1 [<=] fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1).
Proof.
pose proof fvar_in_contd_open_contd_wrt_exp_rec_lower_fvar_in_conts_open_conts_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_conts_open_conts_wrt_exp_rec_lower :
forall cs1 e1 n1,
  fvar_in_conts cs1 [<=] fvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1).
Proof.
pose proof fvar_in_contd_open_contd_wrt_exp_rec_lower_fvar_in_conts_open_conts_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_exp_rec_lower : lngen.

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

Lemma ftvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma ftvar_in_contd_open_contd_wrt_typ_lower :
forall cd1 A1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (open_contd_wrt_typ cd1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_lower : lngen.

Lemma ftvar_in_conts_open_conts_wrt_typ_lower :
forall cs1 A1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (open_conts_wrt_typ cs1 A1).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_typ_lower : lngen.

Lemma ftvar_in_contd_open_contd_wrt_exp_lower :
forall cd1 e1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (open_contd_wrt_exp cd1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_lower : lngen.

Lemma ftvar_in_conts_open_conts_wrt_exp_lower :
forall cs1 e1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (open_conts_wrt_exp cs1 e1).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_exp_lower : lngen.

Lemma fvar_in_contd_open_contd_wrt_typ_lower :
forall cd1 A1,
  fvar_in_contd cd1 [<=] fvar_in_contd (open_contd_wrt_typ cd1 A1).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_lower : lngen.

Lemma fvar_in_conts_open_conts_wrt_typ_lower :
forall cs1 A1,
  fvar_in_conts cs1 [<=] fvar_in_conts (open_conts_wrt_typ cs1 A1).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_typ_lower : lngen.

Lemma fvar_in_contd_open_contd_wrt_exp_lower :
forall cd1 e1,
  fvar_in_contd cd1 [<=] fvar_in_contd (open_contd_wrt_exp cd1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_lower : lngen.

Lemma fvar_in_conts_open_conts_wrt_exp_lower :
forall cs1 e1,
  fvar_in_conts cs1 [<=] fvar_in_conts (open_conts_wrt_exp cs1 e1).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_exp_lower : lngen.

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

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fvar_in_exp e2 `union` fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_typ_rec_upper_ftvar_in_conts_open_conts_wrt_typ_rec_upper_mutual :
(forall cd1 A1 n1,
  ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1) [<=] ftvar_in_typ A1 `union` ftvar_in_contd cd1) /\
(forall cs1 A1 n1,
  ftvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1) [<=] ftvar_in_typ A1 `union` ftvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_typ_rec_upper :
forall cd1 A1 n1,
  ftvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1) [<=] ftvar_in_typ A1 `union` ftvar_in_contd cd1.
Proof.
pose proof ftvar_in_contd_open_contd_wrt_typ_rec_upper_ftvar_in_conts_open_conts_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_conts_open_conts_wrt_typ_rec_upper :
forall cs1 A1 n1,
  ftvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1) [<=] ftvar_in_typ A1 `union` ftvar_in_conts cs1.
Proof.
pose proof ftvar_in_contd_open_contd_wrt_typ_rec_upper_ftvar_in_conts_open_conts_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_exp_rec_upper_ftvar_in_conts_open_conts_wrt_exp_rec_upper_mutual :
(forall cd1 e1 n1,
  ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cd1) /\
(forall cs1 e1 n1,
  ftvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1) [<=] ftvar_in_exp e1 `union` ftvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_contd_open_contd_wrt_exp_rec_upper :
forall cd1 e1 n1,
  ftvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cd1.
Proof.
pose proof ftvar_in_contd_open_contd_wrt_exp_rec_upper_ftvar_in_conts_open_conts_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_conts_open_conts_wrt_exp_rec_upper :
forall cs1 e1 n1,
  ftvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1) [<=] ftvar_in_exp e1 `union` ftvar_in_conts cs1.
Proof.
pose proof ftvar_in_contd_open_contd_wrt_exp_rec_upper_ftvar_in_conts_open_conts_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_typ_rec_upper_fvar_in_conts_open_conts_wrt_typ_rec_upper_mutual :
(forall cd1 A1 n1,
  fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1) [<=] fvar_in_contd cd1) /\
(forall cs1 A1 n1,
  fvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1) [<=] fvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_typ_rec_upper :
forall cd1 A1 n1,
  fvar_in_contd (open_contd_wrt_typ_rec n1 A1 cd1) [<=] fvar_in_contd cd1.
Proof.
pose proof fvar_in_contd_open_contd_wrt_typ_rec_upper_fvar_in_conts_open_conts_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_conts_open_conts_wrt_typ_rec_upper :
forall cs1 A1 n1,
  fvar_in_conts (open_conts_wrt_typ_rec n1 A1 cs1) [<=] fvar_in_conts cs1.
Proof.
pose proof fvar_in_contd_open_contd_wrt_typ_rec_upper_fvar_in_conts_open_conts_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_exp_rec_upper_fvar_in_conts_open_conts_wrt_exp_rec_upper_mutual :
(forall cd1 e1 n1,
  fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1) [<=] fvar_in_exp e1 `union` fvar_in_contd cd1) /\
(forall cs1 e1 n1,
  fvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1) [<=] fvar_in_exp e1 `union` fvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_contd_open_contd_wrt_exp_rec_upper :
forall cd1 e1 n1,
  fvar_in_contd (open_contd_wrt_exp_rec n1 e1 cd1) [<=] fvar_in_exp e1 `union` fvar_in_contd cd1.
Proof.
pose proof fvar_in_contd_open_contd_wrt_exp_rec_upper_fvar_in_conts_open_conts_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_conts_open_conts_wrt_exp_rec_upper :
forall cs1 e1 n1,
  fvar_in_conts (open_conts_wrt_exp_rec n1 e1 cs1) [<=] fvar_in_exp e1 `union` fvar_in_conts cs1.
Proof.
pose proof fvar_in_contd_open_contd_wrt_exp_rec_upper_fvar_in_conts_open_conts_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_exp_rec_upper : lngen.

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

Lemma ftvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  ftvar_in_exp (open_exp_wrt_typ e1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  ftvar_in_exp (open_exp_wrt_exp e1 e2) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  fvar_in_exp (open_exp_wrt_typ e1 A1) [<=] fvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fvar_in_exp (open_exp_wrt_exp e1 e2) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma ftvar_in_contd_open_contd_wrt_typ_upper :
forall cd1 A1,
  ftvar_in_contd (open_contd_wrt_typ cd1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_contd cd1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_typ_upper : lngen.

Lemma ftvar_in_conts_open_conts_wrt_typ_upper :
forall cs1 A1,
  ftvar_in_conts (open_conts_wrt_typ cs1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_conts cs1.
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_typ_upper : lngen.

Lemma ftvar_in_contd_open_contd_wrt_exp_upper :
forall cd1 e1,
  ftvar_in_contd (open_contd_wrt_exp cd1 e1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cd1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_contd_open_contd_wrt_exp_upper : lngen.

Lemma ftvar_in_conts_open_conts_wrt_exp_upper :
forall cs1 e1,
  ftvar_in_conts (open_conts_wrt_exp cs1 e1) [<=] ftvar_in_exp e1 `union` ftvar_in_conts cs1.
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_conts_open_conts_wrt_exp_upper : lngen.

Lemma fvar_in_contd_open_contd_wrt_typ_upper :
forall cd1 A1,
  fvar_in_contd (open_contd_wrt_typ cd1 A1) [<=] fvar_in_contd cd1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_typ_upper : lngen.

Lemma fvar_in_conts_open_conts_wrt_typ_upper :
forall cs1 A1,
  fvar_in_conts (open_conts_wrt_typ cs1 A1) [<=] fvar_in_conts cs1.
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_typ_upper : lngen.

Lemma fvar_in_contd_open_contd_wrt_exp_upper :
forall cd1 e1,
  fvar_in_contd (open_contd_wrt_exp cd1 e1) [<=] fvar_in_exp e1 `union` fvar_in_contd cd1.
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_contd_open_contd_wrt_exp_upper : lngen.

Lemma fvar_in_conts_open_conts_wrt_exp_upper :
forall cs1 e1,
  fvar_in_conts (open_conts_wrt_exp cs1 e1) [<=] fvar_in_exp e1 `union` fvar_in_conts cs1.
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_conts_open_conts_wrt_exp_upper : lngen.

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

Lemma ftvar_in_typ_subst_typ_in_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [=] ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_fresh :
forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [=] ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_fresh : lngen.
#[export] Hint Rewrite ftvar_in_typ_subst_typ_in_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_fresh_mutual :
(forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  ftvar_in_abind (subst_typ_in_abind A1 X1 ab1) [=] ftvar_in_abind ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_fresh :
forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  ftvar_in_abind (subst_typ_in_abind A1 X1 ab1) [=] ftvar_in_abind ab1.
Proof.
pose proof ftvar_in_abind_subst_typ_in_abind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_typ_in_abind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_abind_subst_typ_in_abind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_fresh :
forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_typ_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh :
forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] fvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fvar_in_exp e1 ->
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fvar_in_exp e1 ->
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_fresh : lngen.
#[export] Hint Rewrite fvar_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_fresh_ftvar_in_conts_subst_typ_in_conts_fresh_mutual :
(forall cd1 A1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  ftvar_in_contd (subst_typ_in_contd A1 X1 cd1) [=] ftvar_in_contd cd1) /\
(forall cs1 A1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  ftvar_in_conts (subst_typ_in_conts A1 X1 cs1) [=] ftvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_fresh :
forall cd1 A1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  ftvar_in_contd (subst_typ_in_contd A1 X1 cd1) [=] ftvar_in_contd cd1.
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_fresh_ftvar_in_conts_subst_typ_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_typ_in_contd_fresh : lngen.
#[export] Hint Rewrite ftvar_in_contd_subst_typ_in_contd_fresh using solve [auto] : lngen.

Lemma ftvar_in_conts_subst_typ_in_conts_fresh :
forall cs1 A1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  ftvar_in_conts (subst_typ_in_conts A1 X1 cs1) [=] ftvar_in_conts cs1.
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_fresh_ftvar_in_conts_subst_typ_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_typ_in_conts_fresh : lngen.
#[export] Hint Rewrite ftvar_in_conts_subst_typ_in_conts_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_fresh_ftvar_in_conts_subst_exp_in_conts_fresh_mutual :
(forall cd1 A1 X1,
  fvar_in_contd (subst_typ_in_contd A1 X1 cd1) [=] fvar_in_contd cd1) /\
(forall cs1 A1 X1,
  fvar_in_conts (subst_typ_in_conts A1 X1 cs1) [=] fvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_fresh :
forall cd1 A1 X1,
  fvar_in_contd (subst_typ_in_contd A1 X1 cd1) [=] fvar_in_contd cd1.
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_fresh_ftvar_in_conts_subst_exp_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_exp_in_contd_fresh : lngen.
#[export] Hint Rewrite ftvar_in_contd_subst_exp_in_contd_fresh using solve [auto] : lngen.

Lemma ftvar_in_conts_subst_exp_in_conts_fresh :
forall cs1 A1 X1,
  fvar_in_conts (subst_typ_in_conts A1 X1 cs1) [=] fvar_in_conts cs1.
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_fresh_ftvar_in_conts_subst_exp_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_exp_in_conts_fresh : lngen.
#[export] Hint Rewrite ftvar_in_conts_subst_exp_in_conts_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_exp_in_contd_fresh_fvar_in_conts_subst_exp_in_conts_fresh_mutual :
(forall cd1 e1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  fvar_in_contd (subst_exp_in_contd e1 x1 cd1) [=] fvar_in_contd cd1) /\
(forall cs1 e1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  fvar_in_conts (subst_exp_in_conts e1 x1 cs1) [=] fvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_exp_in_contd_fresh :
forall cd1 e1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  fvar_in_contd (subst_exp_in_contd e1 x1 cd1) [=] fvar_in_contd cd1.
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_fresh_fvar_in_conts_subst_exp_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_exp_in_contd_fresh : lngen.
#[export] Hint Rewrite fvar_in_contd_subst_exp_in_contd_fresh using solve [auto] : lngen.

Lemma fvar_in_conts_subst_exp_in_conts_fresh :
forall cs1 e1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  fvar_in_conts (subst_exp_in_conts e1 x1 cs1) [=] fvar_in_conts cs1.
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_fresh_fvar_in_conts_subst_exp_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_exp_in_conts_fresh : lngen.
#[export] Hint Rewrite fvar_in_conts_subst_exp_in_conts_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_fresh_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [=] ftvar_in_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_fresh :
forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [=] ftvar_in_dbind db1.
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_dbind_subst_typ_in_dbind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_typ_in_work_fresh_mutual :
(forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  ftvar_in_work (subst_typ_in_work A1 X1 w1) [=] ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_typ_in_work_fresh :
forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  ftvar_in_work (subst_typ_in_work A1 X1 w1) [=] ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_subst_typ_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_typ_in_work_fresh : lngen.
#[export] Hint Rewrite ftvar_in_work_subst_typ_in_work_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_exp_in_work_fresh_mutual :
(forall w1 A1 X1,
  fvar_in_work (subst_typ_in_work A1 X1 w1) [=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_exp_in_work_fresh :
forall w1 A1 X1,
  fvar_in_work (subst_typ_in_work A1 X1 w1) [=] fvar_in_work w1.
Proof.
pose proof ftvar_in_work_subst_exp_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_exp_in_work_fresh : lngen.
#[export] Hint Rewrite ftvar_in_work_subst_exp_in_work_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_exp_in_work_fresh_mutual :
(forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  fvar_in_work (subst_exp_in_work e1 x1 w1) [=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_exp_in_work_fresh :
forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  fvar_in_work (subst_exp_in_work e1 x1 w1) [=] fvar_in_work w1.
Proof.
pose proof fvar_in_work_subst_exp_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_exp_in_work_fresh : lngen.
#[export] Hint Rewrite fvar_in_work_subst_exp_in_work_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_lower :
forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_lower : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_lower_mutual :
(forall ab1 A1 X1,
  remove X1 (ftvar_in_abind ab1) [<=] ftvar_in_abind (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_lower :
forall ab1 A1 X1,
  remove X1 (ftvar_in_abind ab1) [<=] ftvar_in_abind (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof ftvar_in_abind_subst_typ_in_abind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_typ_in_abind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_lower :
forall e1 A1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 A1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_typ_in_exp_lower :
forall e1 A1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof fvar_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_typ_in_exp_lower : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fvar_in_exp e1) [<=] fvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  remove x1 (fvar_in_exp e1) [<=] fvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_lower_ftvar_in_conts_subst_typ_in_conts_lower_mutual :
(forall cd1 A1 X1,
  remove X1 (ftvar_in_contd cd1) [<=] ftvar_in_contd (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1,
  remove X1 (ftvar_in_conts cs1) [<=] ftvar_in_conts (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_lower :
forall cd1 A1 X1,
  remove X1 (ftvar_in_contd cd1) [<=] ftvar_in_contd (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_lower_ftvar_in_conts_subst_typ_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_typ_in_contd_lower : lngen.

Lemma ftvar_in_conts_subst_typ_in_conts_lower :
forall cs1 A1 X1,
  remove X1 (ftvar_in_conts cs1) [<=] ftvar_in_conts (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_lower_ftvar_in_conts_subst_typ_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_typ_in_conts_lower : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_lower_ftvar_in_conts_subst_exp_in_conts_lower_mutual :
(forall cd1 e1 x1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_lower :
forall cd1 e1 x1,
  ftvar_in_contd cd1 [<=] ftvar_in_contd (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_lower_ftvar_in_conts_subst_exp_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_exp_in_contd_lower : lngen.

Lemma ftvar_in_conts_subst_exp_in_conts_lower :
forall cs1 e1 x1,
  ftvar_in_conts cs1 [<=] ftvar_in_conts (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_lower_ftvar_in_conts_subst_exp_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_exp_in_conts_lower : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_typ_in_contd_lower_fvar_in_conts_subst_typ_in_conts_lower_mutual :
(forall cd1 A1 X1,
  fvar_in_contd cd1 [<=] fvar_in_contd (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1,
  fvar_in_conts cs1 [<=] fvar_in_conts (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_typ_in_contd_lower :
forall cd1 A1 X1,
  fvar_in_contd cd1 [<=] fvar_in_contd (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof fvar_in_contd_subst_typ_in_contd_lower_fvar_in_conts_subst_typ_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_typ_in_contd_lower : lngen.

Lemma fvar_in_conts_subst_typ_in_conts_lower :
forall cs1 A1 X1,
  fvar_in_conts cs1 [<=] fvar_in_conts (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof fvar_in_contd_subst_typ_in_contd_lower_fvar_in_conts_subst_typ_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_typ_in_conts_lower : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_exp_in_contd_lower_fvar_in_conts_subst_exp_in_conts_lower_mutual :
(forall cd1 e1 x1,
  remove x1 (fvar_in_contd cd1) [<=] fvar_in_contd (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1,
  remove x1 (fvar_in_conts cs1) [<=] fvar_in_conts (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_exp_in_contd_lower :
forall cd1 e1 x1,
  remove x1 (fvar_in_contd cd1) [<=] fvar_in_contd (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_lower_fvar_in_conts_subst_exp_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_exp_in_contd_lower : lngen.

Lemma fvar_in_conts_subst_exp_in_conts_lower :
forall cs1 e1 x1,
  remove x1 (fvar_in_conts cs1) [<=] fvar_in_conts (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_lower_fvar_in_conts_subst_exp_in_conts_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_exp_in_conts_lower : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_lower_mutual :
(forall db1 A1 X1,
  remove X1 (ftvar_in_dbind db1) [<=] ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_lower :
forall db1 A1 X1,
  remove X1 (ftvar_in_dbind db1) [<=] ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_typ_in_work_lower_mutual :
(forall w1 A1 X1,
  remove X1 (ftvar_in_work w1) [<=] ftvar_in_work (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_typ_in_work_lower :
forall w1 A1 X1,
  remove X1 (ftvar_in_work w1) [<=] ftvar_in_work (subst_typ_in_work A1 X1 w1).
Proof.
pose proof ftvar_in_work_subst_typ_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_typ_in_work_lower : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_exp_in_work_lower_mutual :
(forall w1 e1 x1,
  ftvar_in_work w1 [<=] ftvar_in_work (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_exp_in_work_lower :
forall w1 e1 x1,
  ftvar_in_work w1 [<=] ftvar_in_work (subst_exp_in_work e1 x1 w1).
Proof.
pose proof ftvar_in_work_subst_exp_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_exp_in_work_lower : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_typ_in_work_lower_mutual :
(forall w1 A1 X1,
  fvar_in_work w1 [<=] fvar_in_work (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_typ_in_work_lower :
forall w1 A1 X1,
  fvar_in_work w1 [<=] fvar_in_work (subst_typ_in_work A1 X1 w1).
Proof.
pose proof fvar_in_work_subst_typ_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_typ_in_work_lower : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_exp_in_work_lower_mutual :
(forall w1 e1 x1,
  remove x1 (fvar_in_work w1) [<=] fvar_in_work (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_exp_in_work_lower :
forall w1 e1 x1,
  remove x1 (fvar_in_work w1) [<=] fvar_in_work (subst_exp_in_work e1 x1 w1).
Proof.
pose proof fvar_in_work_subst_exp_in_work_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_exp_in_work_lower : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_notin : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_notin_mutual :
(forall ab1 A1 X1 X2,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_abind (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_notin :
forall ab1 A1 X1 X2,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_abind (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof ftvar_in_abind_subst_typ_in_abind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_typ_in_abind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_typ_in_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof fvar_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_notin_ftvar_in_conts_subst_typ_in_conts_notin_mutual :
(forall cd1 A1 X1 X2,
  X2 `notin` ftvar_in_contd cd1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_contd (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1 X2,
  X2 `notin` ftvar_in_conts cs1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_conts (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_notin :
forall cd1 A1 X1 X2,
  X2 `notin` ftvar_in_contd cd1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_contd (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_notin_ftvar_in_conts_subst_typ_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_typ_in_contd_notin : lngen.

Lemma ftvar_in_conts_subst_typ_in_conts_notin :
forall cs1 A1 X1 X2,
  X2 `notin` ftvar_in_conts cs1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_conts (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_notin_ftvar_in_conts_subst_typ_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_typ_in_conts_notin : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_notin_ftvar_in_conts_subst_exp_in_conts_notin_mutual :
(forall cd1 e1 x1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_contd (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_conts (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_notin :
forall cd1 e1 x1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_contd (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_notin_ftvar_in_conts_subst_exp_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_exp_in_contd_notin : lngen.

Lemma ftvar_in_conts_subst_exp_in_conts_notin :
forall cs1 e1 x1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_conts (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_notin_ftvar_in_conts_subst_exp_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_exp_in_conts_notin : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_typ_in_contd_notin_fvar_in_conts_subst_typ_in_conts_notin_mutual :
(forall cd1 A1 X1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  x1 `notin` fvar_in_contd (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  x1 `notin` fvar_in_conts (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_typ_in_contd_notin :
forall cd1 A1 X1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  x1 `notin` fvar_in_contd (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof fvar_in_contd_subst_typ_in_contd_notin_fvar_in_conts_subst_typ_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_typ_in_contd_notin : lngen.

Lemma fvar_in_conts_subst_typ_in_conts_notin :
forall cs1 A1 X1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  x1 `notin` fvar_in_conts (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof fvar_in_contd_subst_typ_in_contd_notin_fvar_in_conts_subst_typ_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_typ_in_conts_notin : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_exp_in_contd_notin_fvar_in_conts_subst_exp_in_conts_notin_mutual :
(forall cd1 e1 x1 x2,
  x2 `notin` fvar_in_contd cd1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_contd (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1 x2,
  x2 `notin` fvar_in_conts cs1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_conts (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_exp_in_contd_notin :
forall cd1 e1 x1 x2,
  x2 `notin` fvar_in_contd cd1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_contd (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_notin_fvar_in_conts_subst_exp_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_exp_in_contd_notin : lngen.

Lemma fvar_in_conts_subst_exp_in_conts_notin :
forall cs1 e1 x1 x2,
  x2 `notin` fvar_in_conts cs1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_conts (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_notin_fvar_in_conts_subst_exp_in_conts_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_exp_in_conts_notin : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_notin_mutual :
(forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_notin :
forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_typ_in_work_notin_mutual :
(forall w1 A1 X1 X2,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_work (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_typ_in_work_notin :
forall w1 A1 X1 X2,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_work (subst_typ_in_work A1 X1 w1).
Proof.
pose proof ftvar_in_work_subst_typ_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_typ_in_work_notin : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_exp_in_work_notin_mutual :
(forall w1 e1 x1 X1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_work (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_exp_in_work_notin :
forall w1 e1 x1 X1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_work (subst_exp_in_work e1 x1 w1).
Proof.
pose proof ftvar_in_work_subst_exp_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_exp_in_work_notin : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_typ_in_work_notin_mutual :
(forall w1 A1 X1 x1,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_work (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_typ_in_work_notin :
forall w1 A1 X1 x1,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_work (subst_typ_in_work A1 X1 w1).
Proof.
pose proof fvar_in_work_subst_typ_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_typ_in_work_notin : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_exp_in_work_notin_mutual :
(forall w1 e1 x1 x2,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_work (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_exp_in_work_notin :
forall w1 e1 x1 x2,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_work (subst_exp_in_work e1 x1 w1).
Proof.
pose proof fvar_in_work_subst_exp_in_work_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_exp_in_work_notin : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_upper_mutual :
(forall A1 A2 X1,
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_upper :
forall A1 A2 X1,
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_upper : lngen.

(* begin hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_upper_mutual :
(forall ab1 A1 X1,
  ftvar_in_abind (subst_typ_in_abind A1 X1 ab1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_abind ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_abind_subst_typ_in_abind_upper :
forall ab1 A1 X1,
  ftvar_in_abind (subst_typ_in_abind A1 X1 ab1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_abind ab1).
Proof.
pose proof ftvar_in_abind_subst_typ_in_abind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_abind_subst_typ_in_abind_upper : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 A1 X1,
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_upper :
forall e1 A1 X1,
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  ftvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  ftvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_typ_in_exp_upper :
forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_typ_in_exp_upper : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fvar_in_exp e2 `union` remove x1 (fvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fvar_in_exp e2 `union` remove x1 (fvar_in_exp e1).
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_upper_ftvar_in_conts_subst_typ_in_conts_upper_mutual :
(forall cd1 A1 X1,
  ftvar_in_contd (subst_typ_in_contd A1 X1 cd1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_contd cd1)) /\
(forall cs1 A1 X1,
  ftvar_in_conts (subst_typ_in_conts A1 X1 cs1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_conts cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_typ_in_contd_upper :
forall cd1 A1 X1,
  ftvar_in_contd (subst_typ_in_contd A1 X1 cd1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_contd cd1).
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_upper_ftvar_in_conts_subst_typ_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_typ_in_contd_upper : lngen.

Lemma ftvar_in_conts_subst_typ_in_conts_upper :
forall cs1 A1 X1,
  ftvar_in_conts (subst_typ_in_conts A1 X1 cs1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_conts cs1).
Proof.
pose proof ftvar_in_contd_subst_typ_in_contd_upper_ftvar_in_conts_subst_typ_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_typ_in_conts_upper : lngen.

(* begin hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_upper_ftvar_in_conts_subst_exp_in_conts_upper_mutual :
(forall cd1 e1 x1,
  ftvar_in_contd (subst_exp_in_contd e1 x1 cd1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cd1) /\
(forall cs1 e1 x1,
  ftvar_in_conts (subst_exp_in_conts e1 x1 cs1) [<=] ftvar_in_exp e1 `union` ftvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_contd_subst_exp_in_contd_upper :
forall cd1 e1 x1,
  ftvar_in_contd (subst_exp_in_contd e1 x1 cd1) [<=] ftvar_in_exp e1 `union` ftvar_in_contd cd1.
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_upper_ftvar_in_conts_subst_exp_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_contd_subst_exp_in_contd_upper : lngen.

Lemma ftvar_in_conts_subst_exp_in_conts_upper :
forall cs1 e1 x1,
  ftvar_in_conts (subst_exp_in_conts e1 x1 cs1) [<=] ftvar_in_exp e1 `union` ftvar_in_conts cs1.
Proof.
pose proof ftvar_in_contd_subst_exp_in_contd_upper_ftvar_in_conts_subst_exp_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_conts_subst_exp_in_conts_upper : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_typ_in_contd_upper_fvar_in_conts_subst_typ_in_conts_upper_mutual :
(forall cd1 A1 X1,
  fvar_in_contd (subst_typ_in_contd A1 X1 cd1) [<=] fvar_in_contd cd1) /\
(forall cs1 A1 X1,
  fvar_in_conts (subst_typ_in_conts A1 X1 cs1) [<=] fvar_in_conts cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_typ_in_contd_upper :
forall cd1 A1 X1,
  fvar_in_contd (subst_typ_in_contd A1 X1 cd1) [<=] fvar_in_contd cd1.
Proof.
pose proof fvar_in_contd_subst_typ_in_contd_upper_fvar_in_conts_subst_typ_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_typ_in_contd_upper : lngen.

Lemma fvar_in_conts_subst_typ_in_conts_upper :
forall cs1 A1 X1,
  fvar_in_conts (subst_typ_in_conts A1 X1 cs1) [<=] fvar_in_conts cs1.
Proof.
pose proof fvar_in_contd_subst_typ_in_contd_upper_fvar_in_conts_subst_typ_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_typ_in_conts_upper : lngen.

(* begin hide *)

Lemma fvar_in_contd_subst_exp_in_contd_upper_fvar_in_conts_subst_exp_in_conts_upper_mutual :
(forall cd1 e1 x1,
  fvar_in_contd (subst_exp_in_contd e1 x1 cd1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_contd cd1)) /\
(forall cs1 e1 x1,
  fvar_in_conts (subst_exp_in_conts e1 x1 cs1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_conts cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_contd_subst_exp_in_contd_upper :
forall cd1 e1 x1,
  fvar_in_contd (subst_exp_in_contd e1 x1 cd1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_contd cd1).
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_upper_fvar_in_conts_subst_exp_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_contd_subst_exp_in_contd_upper : lngen.

Lemma fvar_in_conts_subst_exp_in_conts_upper :
forall cs1 e1 x1,
  fvar_in_conts (subst_exp_in_conts e1 x1 cs1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_conts cs1).
Proof.
pose proof fvar_in_contd_subst_exp_in_contd_upper_fvar_in_conts_subst_exp_in_conts_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_conts_subst_exp_in_conts_upper : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_upper_mutual :
(forall db1 A1 X1,
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_dbind db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_upper :
forall db1 A1 X1,
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_dbind db1).
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_upper : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_typ_in_work_upper_mutual :
(forall w1 A1 X1,
  ftvar_in_work (subst_typ_in_work A1 X1 w1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_work w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_typ_in_work_upper :
forall w1 A1 X1,
  ftvar_in_work (subst_typ_in_work A1 X1 w1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_work w1).
Proof.
pose proof ftvar_in_work_subst_typ_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_typ_in_work_upper : lngen.

(* begin hide *)

Lemma ftvar_in_work_subst_exp_in_work_upper_mutual :
(forall w1 e1 x1,
  ftvar_in_work (subst_exp_in_work e1 x1 w1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_work_subst_exp_in_work_upper :
forall w1 e1 x1,
  ftvar_in_work (subst_exp_in_work e1 x1 w1) [<=] ftvar_in_exp e1 `union` ftvar_in_work w1.
Proof.
pose proof ftvar_in_work_subst_exp_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_work_subst_exp_in_work_upper : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_typ_in_work_upper_mutual :
(forall w1 A1 X1,
  fvar_in_work (subst_typ_in_work A1 X1 w1) [<=] fvar_in_work w1).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_typ_in_work_upper :
forall w1 A1 X1,
  fvar_in_work (subst_typ_in_work A1 X1 w1) [<=] fvar_in_work w1.
Proof.
pose proof fvar_in_work_subst_typ_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_typ_in_work_upper : lngen.

(* begin hide *)

Lemma fvar_in_work_subst_exp_in_work_upper_mutual :
(forall w1 e1 x1,
  fvar_in_work (subst_exp_in_work e1 x1 w1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_work w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_work_subst_exp_in_work_upper :
forall w1 e1 x1,
  fvar_in_work (subst_exp_in_work e1 x1 w1) [<=] fvar_in_exp e1 `union` remove x1 (fvar_in_work w1).
Proof.
pose proof fvar_in_work_subst_exp_in_work_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_work_subst_exp_in_work_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 A2).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_close_abind_wrt_typ_rec_mutual :
(forall ab1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_abind A1 X1 (close_abind_wrt_typ_rec n1 X2 ab1) = close_abind_wrt_typ_rec n1 X2 (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_close_abind_wrt_typ_rec :
forall ab1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_abind A1 X1 (close_abind_wrt_typ_rec n1 X2 ab1) = close_abind_wrt_typ_rec n1 X2 (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof subst_typ_in_abind_close_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_close_abind_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  subst_typ_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp A1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  subst_typ_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp A1 x1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_close_contd_wrt_typ_rec_subst_typ_in_conts_close_conts_wrt_typ_rec_mutual :
(forall cd1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_contd A1 X1 (close_contd_wrt_typ_rec n1 X2 cd1) = close_contd_wrt_typ_rec n1 X2 (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_conts A1 X1 (close_conts_wrt_typ_rec n1 X2 cs1) = close_conts_wrt_typ_rec n1 X2 (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_close_contd_wrt_typ_rec :
forall cd1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_contd A1 X1 (close_contd_wrt_typ_rec n1 X2 cd1) = close_contd_wrt_typ_rec n1 X2 (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_typ_rec_subst_typ_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_typ_rec : lngen.

Lemma subst_typ_in_conts_close_conts_wrt_typ_rec :
forall cs1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_conts A1 X1 (close_conts_wrt_typ_rec n1 X2 cs1) = close_conts_wrt_typ_rec n1 X2 (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_typ_rec_subst_typ_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_close_contd_wrt_exp_rec_subst_typ_in_conts_close_conts_wrt_exp_rec_mutual :
(forall cd1 A1 x1 X1 n1,
  subst_typ_in_contd A1 x1 (close_contd_wrt_exp_rec n1 X1 cd1) = close_contd_wrt_exp_rec n1 X1 (subst_typ_in_contd A1 x1 cd1)) /\
(forall cs1 A1 x1 X1 n1,
  subst_typ_in_conts A1 x1 (close_conts_wrt_exp_rec n1 X1 cs1) = close_conts_wrt_exp_rec n1 X1 (subst_typ_in_conts A1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_close_contd_wrt_exp_rec :
forall cd1 A1 x1 X1 n1,
  subst_typ_in_contd A1 x1 (close_contd_wrt_exp_rec n1 X1 cd1) = close_contd_wrt_exp_rec n1 X1 (subst_typ_in_contd A1 x1 cd1).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_exp_rec_subst_typ_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_exp_rec : lngen.

Lemma subst_typ_in_conts_close_conts_wrt_exp_rec :
forall cs1 A1 x1 X1 n1,
  subst_typ_in_conts A1 x1 (close_conts_wrt_exp_rec n1 X1 cs1) = close_conts_wrt_exp_rec n1 X1 (subst_typ_in_conts A1 x1 cs1).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_exp_rec_subst_typ_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_close_contd_wrt_typ_rec_subst_exp_in_conts_close_conts_wrt_typ_rec_mutual :
(forall cd1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_contd e1 X1 (close_contd_wrt_typ_rec n1 x1 cd1) = close_contd_wrt_typ_rec n1 x1 (subst_exp_in_contd e1 X1 cd1)) /\
(forall cs1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_conts e1 X1 (close_conts_wrt_typ_rec n1 x1 cs1) = close_conts_wrt_typ_rec n1 x1 (subst_exp_in_conts e1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_close_contd_wrt_typ_rec :
forall cd1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_contd e1 X1 (close_contd_wrt_typ_rec n1 x1 cd1) = close_contd_wrt_typ_rec n1 x1 (subst_exp_in_contd e1 X1 cd1).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_typ_rec_subst_exp_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_typ_rec : lngen.

Lemma subst_exp_in_conts_close_conts_wrt_typ_rec :
forall cs1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_conts e1 X1 (close_conts_wrt_typ_rec n1 x1 cs1) = close_conts_wrt_typ_rec n1 x1 (subst_exp_in_conts e1 X1 cs1).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_typ_rec_subst_exp_in_conts_close_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_close_contd_wrt_exp_rec_subst_exp_in_conts_close_conts_wrt_exp_rec_mutual :
(forall cd1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_contd e1 x1 (close_contd_wrt_exp_rec n1 x2 cd1) = close_contd_wrt_exp_rec n1 x2 (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_conts e1 x1 (close_conts_wrt_exp_rec n1 x2 cs1) = close_conts_wrt_exp_rec n1 x2 (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_close_contd_wrt_exp_rec :
forall cd1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_contd e1 x1 (close_contd_wrt_exp_rec n1 x2 cd1) = close_contd_wrt_exp_rec n1 x2 (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_exp_rec_subst_exp_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_exp_rec : lngen.

Lemma subst_exp_in_conts_close_conts_wrt_exp_rec :
forall cs1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_conts e1 x1 (close_conts_wrt_exp_rec n1 x2 cs1) = close_conts_wrt_exp_rec n1 x2 (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_exp_rec_subst_exp_in_conts_close_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_dbind A1 X1 (close_dbind_wrt_typ_rec n1 X2 db1) = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec :
forall db1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_dbind A1 X1 (close_dbind_wrt_typ_rec n1 X2 db1) = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_work_close_work_wrt_typ_rec_mutual :
(forall w1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_work A1 X1 (close_work_wrt_typ_rec n1 X2 w1) = close_work_wrt_typ_rec n1 X2 (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_close_work_wrt_typ_rec :
forall w1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_work A1 X1 (close_work_wrt_typ_rec n1 X2 w1) = close_work_wrt_typ_rec n1 X2 (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_work_close_work_wrt_exp_rec_mutual :
(forall w1 A1 x1 X1 n1,
  subst_typ_in_work A1 x1 (close_work_wrt_exp_rec n1 X1 w1) = close_work_wrt_exp_rec n1 X1 (subst_typ_in_work A1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_close_work_wrt_exp_rec :
forall w1 A1 x1 X1 n1,
  subst_typ_in_work A1 x1 (close_work_wrt_exp_rec n1 X1 w1) = close_work_wrt_exp_rec n1 X1 (subst_typ_in_work A1 x1 w1).
Proof.
pose proof subst_typ_in_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_work_close_work_wrt_typ_rec_mutual :
(forall w1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_work e1 X1 (close_work_wrt_typ_rec n1 x1 w1) = close_work_wrt_typ_rec n1 x1 (subst_exp_in_work e1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_close_work_wrt_typ_rec :
forall w1 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_work e1 X1 (close_work_wrt_typ_rec n1 x1 w1) = close_work_wrt_typ_rec n1 x1 (subst_exp_in_work e1 X1 w1).
Proof.
pose proof subst_exp_in_work_close_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_work_close_work_wrt_exp_rec_mutual :
(forall w1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_work e1 x1 (close_work_wrt_exp_rec n1 x2 w1) = close_work_wrt_exp_rec n1 x2 (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_close_work_wrt_exp_rec :
forall w1 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_work e1 x1 (close_work_wrt_exp_rec n1 x2 w1) = close_work_wrt_exp_rec n1 x2 (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_close_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_exp_rec : lngen.

Lemma subst_typ_in_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ : lngen.

Lemma subst_typ_in_abind_close_abind_wrt_typ :
forall ab1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_abind A1 X1 (close_abind_wrt_typ X2 ab1) = close_abind_wrt_typ X2 (subst_typ_in_abind A1 X1 ab1).
Proof.
unfold close_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_close_abind_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  lc_typ A1 ->  subst_typ_in_exp A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_typ_in_exp A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_exp_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_typ_in_contd_close_contd_wrt_typ :
forall cd1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_contd A1 X1 (close_contd_wrt_typ X2 cd1) = close_contd_wrt_typ X2 (subst_typ_in_contd A1 X1 cd1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_typ : lngen.

Lemma subst_typ_in_conts_close_conts_wrt_typ :
forall cs1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_conts A1 X1 (close_conts_wrt_typ X2 cs1) = close_conts_wrt_typ X2 (subst_typ_in_conts A1 X1 cs1).
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_typ : lngen.

Lemma subst_typ_in_contd_close_contd_wrt_exp :
forall cd1 A1 x1 X1,
  lc_typ A1 ->  subst_typ_in_contd A1 x1 (close_contd_wrt_exp X1 cd1) = close_contd_wrt_exp X1 (subst_typ_in_contd A1 x1 cd1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_exp : lngen.

Lemma subst_typ_in_conts_close_conts_wrt_exp :
forall cs1 A1 x1 X1,
  lc_typ A1 ->  subst_typ_in_conts A1 x1 (close_conts_wrt_exp X1 cs1) = close_conts_wrt_exp X1 (subst_typ_in_conts A1 x1 cs1).
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_exp : lngen.

Lemma subst_exp_in_contd_close_contd_wrt_typ :
forall cd1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_contd e1 X1 (close_contd_wrt_typ x1 cd1) = close_contd_wrt_typ x1 (subst_exp_in_contd e1 X1 cd1).
Proof.
unfold close_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_typ : lngen.

Lemma subst_exp_in_conts_close_conts_wrt_typ :
forall cs1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_conts e1 X1 (close_conts_wrt_typ x1 cs1) = close_conts_wrt_typ x1 (subst_exp_in_conts e1 X1 cs1).
Proof.
unfold close_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_typ : lngen.

Lemma subst_exp_in_contd_close_contd_wrt_exp :
forall cd1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_contd e1 x1 (close_contd_wrt_exp x2 cd1) = close_contd_wrt_exp x2 (subst_exp_in_contd e1 x1 cd1).
Proof.
unfold close_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_exp : lngen.

Lemma subst_exp_in_conts_close_conts_wrt_exp :
forall cs1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_conts e1 x1 (close_conts_wrt_exp x2 cs1) = close_conts_wrt_exp x2 (subst_exp_in_conts e1 x1 cs1).
Proof.
unfold close_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_exp : lngen.

Lemma subst_typ_in_dbind_close_dbind_wrt_typ :
forall db1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_dbind A1 X1 (close_dbind_wrt_typ X2 db1) = close_dbind_wrt_typ X2 (subst_typ_in_dbind A1 X1 db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ : lngen.

Lemma subst_typ_in_work_close_work_wrt_typ :
forall w1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_work A1 X1 (close_work_wrt_typ X2 w1) = close_work_wrt_typ X2 (subst_typ_in_work A1 X1 w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_typ : lngen.

Lemma subst_typ_in_work_close_work_wrt_exp :
forall w1 A1 x1 X1,
  lc_typ A1 ->  subst_typ_in_work A1 x1 (close_work_wrt_exp X1 w1) = close_work_wrt_exp X1 (subst_typ_in_work A1 x1 w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_exp : lngen.

Lemma subst_exp_in_work_close_work_wrt_typ :
forall w1 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_work e1 X1 (close_work_wrt_typ x1 w1) = close_work_wrt_typ x1 (subst_exp_in_work e1 X1 w1).
Proof.
unfold close_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_typ : lngen.

Lemma subst_exp_in_work_close_work_wrt_exp :
forall w1 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_work e1 x1 (close_work_wrt_exp x2 w1) = close_work_wrt_exp x2 (subst_exp_in_work e1 x1 w1).
Proof.
unfold close_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof subst_typ_in_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_degree_abind_wrt_typ_mutual :
(forall ab1 A1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_abind_wrt_typ n1 (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_degree_abind_wrt_typ :
forall ab1 A1 X1 n1,
  degree_abind_wrt_typ n1 ab1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_abind_wrt_typ n1 (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof subst_typ_in_abind_degree_abind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_degree_abind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_degree_contd_wrt_typ_subst_typ_in_conts_degree_conts_wrt_typ_mutual :
(forall cd1 A1 X1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_conts_wrt_typ n1 (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_degree_contd_wrt_typ :
forall cd1 A1 X1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_contd_wrt_typ n1 (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_degree_contd_wrt_typ_subst_typ_in_conts_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_degree_contd_wrt_typ : lngen.

Lemma subst_typ_in_conts_degree_conts_wrt_typ :
forall cs1 A1 X1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_conts_wrt_typ n1 (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_degree_contd_wrt_typ_subst_typ_in_conts_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_degree_conts_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_degree_contd_wrt_exp_subst_typ_in_conts_degree_conts_wrt_exp_mutual :
(forall cd1 A1 X1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp n1 (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp n1 (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_degree_contd_wrt_exp :
forall cd1 A1 X1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_contd_wrt_exp n1 (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_degree_contd_wrt_exp_subst_typ_in_conts_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_degree_contd_wrt_exp : lngen.

Lemma subst_typ_in_conts_degree_conts_wrt_exp :
forall cs1 A1 X1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_conts_wrt_exp n1 (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_degree_contd_wrt_exp_subst_typ_in_conts_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_degree_conts_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_degree_contd_wrt_typ_subst_exp_in_conts_degree_conts_wrt_typ_mutual :
(forall cd1 e1 x1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_conts_wrt_typ n1 (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_degree_contd_wrt_typ :
forall cd1 e1 x1 n1,
  degree_contd_wrt_typ n1 cd1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_contd_wrt_typ n1 (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_degree_contd_wrt_typ_subst_exp_in_conts_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_degree_contd_wrt_typ : lngen.

Lemma subst_exp_in_conts_degree_conts_wrt_typ :
forall cs1 e1 x1 n1,
  degree_conts_wrt_typ n1 cs1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_conts_wrt_typ n1 (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_degree_contd_wrt_typ_subst_exp_in_conts_degree_conts_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_degree_conts_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_degree_contd_wrt_exp_subst_exp_in_conts_degree_conts_wrt_exp_mutual :
(forall cd1 e1 x1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_conts_wrt_exp n1 (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_degree_contd_wrt_exp :
forall cd1 e1 x1 n1,
  degree_contd_wrt_exp n1 cd1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_contd_wrt_exp n1 (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_degree_contd_wrt_exp_subst_exp_in_conts_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_degree_contd_wrt_exp : lngen.

Lemma subst_exp_in_conts_degree_conts_wrt_exp :
forall cs1 e1 x1 n1,
  degree_conts_wrt_exp n1 cs1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_conts_wrt_exp n1 (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_degree_contd_wrt_exp_subst_exp_in_conts_degree_conts_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_degree_conts_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_degree_dbind_wrt_typ_mutual :
(forall db1 A1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_degree_dbind_wrt_typ :
forall db1 A1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_degree_dbind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_work_degree_work_wrt_typ_mutual :
(forall w1 A1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_work_wrt_typ n1 (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_degree_work_wrt_typ :
forall w1 A1 X1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_work_wrt_typ n1 (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_degree_work_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_degree_work_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_work_degree_work_wrt_exp_mutual :
(forall w1 A1 X1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_degree_work_wrt_exp :
forall w1 A1 X1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_work_wrt_exp n1 (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_degree_work_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_degree_work_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_work_degree_work_wrt_typ_mutual :
(forall w1 e1 x1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_degree_work_wrt_typ :
forall w1 e1 x1 n1,
  degree_work_wrt_typ n1 w1 ->
  degree_exp_wrt_typ n1 e1 ->
  degree_work_wrt_typ n1 (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_degree_work_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_degree_work_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_in_work_degree_work_wrt_exp_mutual :
(forall w1 e1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_work_wrt_exp n1 (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_degree_work_wrt_exp :
forall w1 e1 x1 n1,
  degree_work_wrt_exp n1 w1 ->
  degree_exp_wrt_exp n1 e1 ->
  degree_work_wrt_exp n1 (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_degree_work_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_degree_work_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_typ_in_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_typ_in_typ A1 X1 A2 = A2.
Proof.
pose proof subst_typ_in_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_fresh_eq_mutual :
(forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  subst_typ_in_abind A1 X1 ab1 = ab1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_fresh_eq :
forall ab1 A1 X1,
  X1 `notin` ftvar_in_abind ab1 ->
  subst_typ_in_abind A1 X1 ab1 = ab1.
Proof.
pose proof subst_typ_in_abind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_abind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = e1.
Proof.
pose proof subst_typ_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_fresh_eq_subst_typ_in_conts_fresh_eq_mutual :
(forall cd1 A1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  subst_typ_in_contd A1 X1 cd1 = cd1) /\
(forall cs1 A1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  subst_typ_in_conts A1 X1 cs1 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_fresh_eq :
forall cd1 A1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  subst_typ_in_contd A1 X1 cd1 = cd1.
Proof.
pose proof subst_typ_in_contd_fresh_eq_subst_typ_in_conts_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_contd_fresh_eq using solve [auto] : lngen.

Lemma subst_typ_in_conts_fresh_eq :
forall cs1 A1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  subst_typ_in_conts A1 X1 cs1 = cs1.
Proof.
pose proof subst_typ_in_contd_fresh_eq_subst_typ_in_conts_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_conts_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_fresh_eq_subst_exp_in_conts_fresh_eq_mutual :
(forall cd1 e1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  subst_exp_in_contd e1 x1 cd1 = cd1) /\
(forall cs1 e1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  subst_exp_in_conts e1 x1 cs1 = cs1).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_fresh_eq :
forall cd1 e1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  subst_exp_in_contd e1 x1 cd1 = cd1.
Proof.
pose proof subst_exp_in_contd_fresh_eq_subst_exp_in_conts_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_in_contd_fresh_eq using solve [auto] : lngen.

Lemma subst_exp_in_conts_fresh_eq :
forall cs1 e1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  subst_exp_in_conts e1 x1 cs1 = cs1.
Proof.
pose proof subst_exp_in_contd_fresh_eq_subst_exp_in_conts_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_in_conts_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_fresh_eq_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  subst_typ_in_dbind A1 X1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_fresh_eq :
forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  subst_typ_in_dbind A1 X1 db1 = db1.
Proof.
pose proof subst_typ_in_dbind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_dbind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_work_fresh_eq_mutual :
(forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  subst_typ_in_work A1 X1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_fresh_eq :
forall w1 A1 X1,
  X1 `notin` ftvar_in_work w1 ->
  subst_typ_in_work A1 X1 w1 = w1.
Proof.
pose proof subst_typ_in_work_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_work_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_work_fresh_eq_mutual :
(forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  subst_exp_in_work e1 x1 w1 = w1).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_fresh_eq :
forall w1 e1 x1,
  x1 `notin` fvar_in_work w1 ->
  subst_exp_in_work e1 x1 w1 = w1.
Proof.
pose proof subst_exp_in_work_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_in_work_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X1 A2).
Proof.
pose proof subst_typ_in_typ_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_fresh_same_mutual :
(forall ab1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_fresh_same :
forall ab1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof subst_typ_in_abind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_fresh_same_subst_typ_in_conts_fresh_same_mutual :
(forall cd1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_conts (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_fresh_same :
forall cd1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_fresh_same_subst_typ_in_conts_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_fresh_same : lngen.

Lemma subst_typ_in_conts_fresh_same :
forall cs1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_conts (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_fresh_same_subst_typ_in_conts_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_fresh_same_subst_exp_in_conts_fresh_same_mutual :
(forall cd1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_conts (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_fresh_same :
forall cd1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_fresh_same_subst_exp_in_conts_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_fresh_same : lngen.

Lemma subst_exp_in_conts_fresh_same :
forall cs1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_conts (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_fresh_same_subst_exp_in_conts_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_fresh_same_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_fresh_same :
forall db1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_work_fresh_same_mutual :
(forall w1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_fresh_same :
forall w1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_work_fresh_same_mutual :
(forall w1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_fresh_same :
forall w1 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X2 A2).
Proof.
pose proof subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_fresh_mutual :
(forall ab1 A1 X1 X2,
  X1 `notin` ftvar_in_abind ab1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_typ_in_abind A1 X2 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_fresh :
forall ab1 A1 X1 X2,
  X1 `notin` ftvar_in_abind ab1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_abind (subst_typ_in_abind A1 X2 ab1).
Proof.
pose proof subst_typ_in_abind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X2 e1).
Proof.
pose proof subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x2 e2).
Proof.
pose proof subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_fresh_subst_typ_in_conts_fresh_mutual :
(forall cd1 A1 X1 X2,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_typ_in_contd A1 X2 cd1)) /\
(forall cs1 A1 X1 X2,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_conts (subst_typ_in_conts A1 X2 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_fresh :
forall cd1 A1 X1 X2,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_contd (subst_typ_in_contd A1 X2 cd1).
Proof.
pose proof subst_typ_in_contd_fresh_subst_typ_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_fresh : lngen.

Lemma subst_typ_in_conts_fresh :
forall cs1 A1 X1 X2,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_conts (subst_typ_in_conts A1 X2 cs1).
Proof.
pose proof subst_typ_in_contd_fresh_subst_typ_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_fresh_subst_exp_in_conts_fresh_mutual :
(forall cd1 e1 x1 x2,
  x1 `notin` fvar_in_contd cd1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_exp_in_contd e1 x2 cd1)) /\
(forall cs1 e1 x1 x2,
  x1 `notin` fvar_in_conts cs1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_conts (subst_exp_in_conts e1 x2 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_fresh :
forall cd1 e1 x1 x2,
  x1 `notin` fvar_in_contd cd1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_contd (subst_exp_in_contd e1 x2 cd1).
Proof.
pose proof subst_exp_in_contd_fresh_subst_exp_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_fresh : lngen.

Lemma subst_exp_in_conts_fresh :
forall cs1 e1 x1 x2,
  x1 `notin` fvar_in_conts cs1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_conts (subst_exp_in_conts e1 x2 cs1).
Proof.
pose proof subst_exp_in_contd_fresh_subst_exp_in_conts_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_fresh_mutual :
(forall db1 A1 X1 X2,
  X1 `notin` ftvar_in_dbind db1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X2 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_fresh :
forall db1 A1 X1 X2,
  X1 `notin` ftvar_in_dbind db1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X2 db1).
Proof.
pose proof subst_typ_in_dbind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_work_fresh_mutual :
(forall w1 A1 X1 X2,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_typ_in_work A1 X2 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_fresh :
forall w1 A1 X1 X2,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_work (subst_typ_in_work A1 X2 w1).
Proof.
pose proof subst_typ_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_work_fresh_mutual :
(forall w1 e1 x1 x2,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_exp_in_work e1 x2 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_fresh :
forall w1 e1 x1 x2,
  x1 `notin` fvar_in_work w1 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_work (subst_exp_in_work e1 x2 w1).
Proof.
pose proof subst_exp_in_work_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_fresh : lngen.

Lemma subst_typ_in_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (subst_typ_in_typ A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_lc_typ : lngen.

Lemma subst_typ_in_abind_lc_abind :
forall ab1 A1 X1,
  lc_abind ab1 ->
  lc_typ A1 ->
  lc_abind (subst_typ_in_abind A1 X1 ab1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_lc_abind : lngen.

Lemma subst_typ_in_exp_lc_exp :
forall e1 A1 X1,
  lc_exp e1 ->
  lc_typ A1 ->
  lc_exp (subst_typ_in_exp A1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_lc_exp : lngen.

Lemma subst_exp_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_lc_exp : lngen.

Lemma subst_typ_in_contd_lc_contd :
forall cd1 A1 X1,
  lc_contd cd1 ->
  lc_typ A1 ->
  lc_contd (subst_typ_in_contd A1 X1 cd1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_lc_contd : lngen.

Lemma subst_typ_in_conts_lc_conts :
forall cs1 A1 X1,
  lc_conts cs1 ->
  lc_typ A1 ->
  lc_conts (subst_typ_in_conts A1 X1 cs1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_lc_conts : lngen.

Lemma subst_exp_in_contd_lc_contd :
forall cd1 e1 x1,
  lc_contd cd1 ->
  lc_exp e1 ->
  lc_contd (subst_exp_in_contd e1 x1 cd1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_lc_contd : lngen.

Lemma subst_exp_in_conts_lc_conts :
forall cs1 e1 x1,
  lc_conts cs1 ->
  lc_exp e1 ->
  lc_conts (subst_exp_in_conts e1 x1 cs1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_lc_conts : lngen.

Lemma subst_typ_in_dbind_lc_dbind :
forall db1 A1 X1,
  lc_dbind db1 ->
  lc_typ A1 ->
  lc_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_lc_dbind : lngen.

Lemma subst_typ_in_work_lc_work :
forall w1 A1 X1,
  lc_work w1 ->
  lc_typ A1 ->
  lc_work (subst_typ_in_work A1 X1 w1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_lc_work : lngen.

Lemma subst_exp_in_work_lc_work :
forall w1 e1 x1,
  lc_work w1 ->
  lc_exp e1 ->
  lc_work (subst_exp_in_work e1 x1 w1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_lc_work : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_typ A1 X1 A3).
Proof.
pose proof subst_typ_in_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_abind_open_abind_wrt_typ_rec_mutual :
(forall ab1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_abind A1 X1 (open_abind_wrt_typ_rec n1 A2 ab1) = open_abind_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_abind_open_abind_wrt_typ_rec :
forall ab1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_abind A1 X1 (open_abind_wrt_typ_rec n1 A2 ab1) = open_abind_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof subst_typ_in_abind_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_open_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec :
forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_exp A1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 X1 n1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_exp A1 X1 e2).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_open_contd_wrt_typ_rec_subst_typ_in_conts_open_conts_wrt_typ_rec_mutual :
(forall cd1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_contd A1 X1 (open_contd_wrt_typ_rec n1 A2 cd1) = open_contd_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_conts A1 X1 (open_conts_wrt_typ_rec n1 A2 cs1) = open_conts_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_open_contd_wrt_typ_rec :
forall cd1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_contd A1 X1 (open_contd_wrt_typ_rec n1 A2 cd1) = open_contd_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_open_contd_wrt_typ_rec_subst_typ_in_conts_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_conts_open_conts_wrt_typ_rec :
forall cs1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_conts A1 X1 (open_conts_wrt_typ_rec n1 A2 cs1) = open_conts_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_open_contd_wrt_typ_rec_subst_typ_in_conts_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_open_contd_wrt_exp_rec_subst_typ_in_conts_open_conts_wrt_exp_rec_mutual :
(forall cd1 A1 e1 X1 n1,
  subst_typ_in_contd A1 X1 (open_contd_wrt_exp_rec n1 e1 cd1) = open_contd_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 e1 X1 n1,
  subst_typ_in_conts A1 X1 (open_conts_wrt_exp_rec n1 e1 cs1) = open_conts_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_open_contd_wrt_exp_rec :
forall cd1 A1 e1 X1 n1,
  subst_typ_in_contd A1 X1 (open_contd_wrt_exp_rec n1 e1 cd1) = open_contd_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_open_contd_wrt_exp_rec_subst_typ_in_conts_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_conts_open_conts_wrt_exp_rec :
forall cs1 A1 e1 X1 n1,
  subst_typ_in_conts A1 X1 (open_conts_wrt_exp_rec n1 e1 cs1) = open_conts_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_open_contd_wrt_exp_rec_subst_typ_in_conts_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_open_conts_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_open_contd_wrt_typ_rec_subst_exp_in_conts_open_conts_wrt_typ_rec_mutual :
(forall cd1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 (open_contd_wrt_typ_rec n1 A1 cd1) = open_contd_wrt_typ_rec n1 A1 (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 (open_conts_wrt_typ_rec n1 A1 cs1) = open_conts_wrt_typ_rec n1 A1 (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_open_contd_wrt_typ_rec :
forall cd1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 (open_contd_wrt_typ_rec n1 A1 cd1) = open_contd_wrt_typ_rec n1 A1 (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_open_contd_wrt_typ_rec_subst_exp_in_conts_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_conts_open_conts_wrt_typ_rec :
forall cs1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 (open_conts_wrt_typ_rec n1 A1 cs1) = open_conts_wrt_typ_rec n1 A1 (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_open_contd_wrt_typ_rec_subst_exp_in_conts_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_open_contd_wrt_exp_rec_subst_exp_in_conts_open_conts_wrt_exp_rec_mutual :
(forall cd1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 (open_contd_wrt_exp_rec n1 e2 cd1) = open_contd_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 (open_conts_wrt_exp_rec n1 e2 cs1) = open_conts_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_open_contd_wrt_exp_rec :
forall cd1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 (open_contd_wrt_exp_rec n1 e2 cd1) = open_contd_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_open_contd_wrt_exp_rec_subst_exp_in_conts_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_conts_open_conts_wrt_exp_rec :
forall cs1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 (open_conts_wrt_exp_rec n1 e2 cs1) = open_conts_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_open_contd_wrt_exp_rec_subst_exp_in_conts_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_open_conts_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 A2 db1) = open_dbind_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_open_dbind_wrt_typ_rec :
forall db1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 A2 db1) = open_dbind_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_open_work_wrt_typ_rec_mutual :
(forall w1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_work A1 X1 (open_work_wrt_typ_rec n1 A2 w1) = open_work_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_open_work_wrt_typ_rec :
forall w1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_work A1 X1 (open_work_wrt_typ_rec n1 A2 w1) = open_work_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_open_work_wrt_exp_rec_mutual :
(forall w1 A1 e1 X1 n1,
  subst_typ_in_work A1 X1 (open_work_wrt_exp_rec n1 e1 w1) = open_work_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_open_work_wrt_exp_rec :
forall w1 A1 e1 X1 n1,
  subst_typ_in_work A1 X1 (open_work_wrt_exp_rec n1 e1 w1) = open_work_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_open_work_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_open_work_wrt_typ_rec_mutual :
(forall w1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_work e1 x1 (open_work_wrt_typ_rec n1 A1 w1) = open_work_wrt_typ_rec n1 A1 (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_open_work_wrt_typ_rec :
forall w1 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_work e1 x1 (open_work_wrt_typ_rec n1 A1 w1) = open_work_wrt_typ_rec n1 A1 (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_open_work_wrt_exp_rec_mutual :
(forall w1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_work e1 x1 (open_work_wrt_exp_rec n1 e2 w1) = open_work_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_open_work_wrt_exp_rec :
forall w1 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_work e1 x1 (open_work_wrt_exp_rec n1 e2 w1) = open_work_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_open_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (subst_typ_in_typ A1 X1 A3) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ : lngen.

Lemma subst_typ_in_abind_open_abind_wrt_typ :
forall ab1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_abind A1 X1 (open_abind_wrt_typ ab1 A2) = open_abind_wrt_typ (subst_typ_in_abind A1 X1 ab1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_open_abind_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ :
forall e1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 A2) = open_exp_wrt_typ (subst_typ_in_exp A1 X1 e1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp :
forall e2 A1 e1 X1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_typ_in_exp A1 X1 e2) (subst_typ_in_exp A1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 A1) = open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) A1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_contd_open_contd_wrt_typ :
forall cd1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_contd A1 X1 (open_contd_wrt_typ cd1 A2) = open_contd_wrt_typ (subst_typ_in_contd A1 X1 cd1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_open_contd_wrt_typ : lngen.

Lemma subst_typ_in_conts_open_conts_wrt_typ :
forall cs1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_conts A1 X1 (open_conts_wrt_typ cs1 A2) = open_conts_wrt_typ (subst_typ_in_conts A1 X1 cs1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_open_conts_wrt_typ : lngen.

Lemma subst_typ_in_contd_open_contd_wrt_exp :
forall cd1 A1 e1 X1,
  subst_typ_in_contd A1 X1 (open_contd_wrt_exp cd1 e1) = open_contd_wrt_exp (subst_typ_in_contd A1 X1 cd1) (subst_typ_in_exp A1 X1 e1).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_open_contd_wrt_exp : lngen.

Lemma subst_typ_in_conts_open_conts_wrt_exp :
forall cs1 A1 e1 X1,
  subst_typ_in_conts A1 X1 (open_conts_wrt_exp cs1 e1) = open_conts_wrt_exp (subst_typ_in_conts A1 X1 cs1) (subst_typ_in_exp A1 X1 e1).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_open_conts_wrt_exp : lngen.

Lemma subst_exp_in_contd_open_contd_wrt_typ :
forall cd1 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 (open_contd_wrt_typ cd1 A1) = open_contd_wrt_typ (subst_exp_in_contd e1 x1 cd1) A1.
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_open_contd_wrt_typ : lngen.

Lemma subst_exp_in_conts_open_conts_wrt_typ :
forall cs1 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 (open_conts_wrt_typ cs1 A1) = open_conts_wrt_typ (subst_exp_in_conts e1 x1 cs1) A1.
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_open_conts_wrt_typ : lngen.

Lemma subst_exp_in_contd_open_contd_wrt_exp :
forall cd1 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 (open_contd_wrt_exp cd1 e2) = open_contd_wrt_exp (subst_exp_in_contd e1 x1 cd1) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_open_contd_wrt_exp : lngen.

Lemma subst_exp_in_conts_open_conts_wrt_exp :
forall cs1 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 (open_conts_wrt_exp cs1 e2) = open_conts_wrt_exp (subst_exp_in_conts e1 x1 cs1) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_open_conts_wrt_exp : lngen.

Lemma subst_typ_in_dbind_open_dbind_wrt_typ :
forall db1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 A2) = open_dbind_wrt_typ (subst_typ_in_dbind A1 X1 db1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_open_dbind_wrt_typ : lngen.

Lemma subst_typ_in_work_open_work_wrt_typ :
forall w1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_work A1 X1 (open_work_wrt_typ w1 A2) = open_work_wrt_typ (subst_typ_in_work A1 X1 w1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_open_work_wrt_typ : lngen.

Lemma subst_typ_in_work_open_work_wrt_exp :
forall w1 A1 e1 X1,
  subst_typ_in_work A1 X1 (open_work_wrt_exp w1 e1) = open_work_wrt_exp (subst_typ_in_work A1 X1 w1) (subst_typ_in_exp A1 X1 e1).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_open_work_wrt_exp : lngen.

Lemma subst_exp_in_work_open_work_wrt_typ :
forall w1 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_work e1 x1 (open_work_wrt_typ w1 A1) = open_work_wrt_typ (subst_exp_in_work e1 x1 w1) A1.
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_open_work_wrt_typ : lngen.

Lemma subst_exp_in_work_open_work_wrt_exp :
forall w1 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_work e1 x1 (open_work_wrt_exp w1 e2) = open_work_wrt_exp (subst_exp_in_work e1 x1 w1) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_open_work_wrt_exp : lngen.

Lemma subst_typ_in_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (subst_typ_in_typ A1 X1 A2) (typ_var_f X2) = subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_typ_open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_typ_in_abind_open_abind_wrt_typ_var :
forall ab1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_abind_wrt_typ (subst_typ_in_abind A1 X1 ab1) (typ_var_f X2) = subst_typ_in_abind A1 X1 (open_abind_wrt_typ ab1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_abind_open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_open_abind_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_exp_wrt_typ (subst_typ_in_exp A1 X1 e1) (typ_var_f X2) = subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_exp_wrt_exp (subst_typ_in_exp A1 X1 e1) (exp_var_f x1) = subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) (typ_var_f X1) = subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp_in_exp e1 x1 e2) (exp_var_f x2) = subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_typ_in_contd_open_contd_wrt_typ_var :
forall cd1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_contd_wrt_typ (subst_typ_in_contd A1 X1 cd1) (typ_var_f X2) = subst_typ_in_contd A1 X1 (open_contd_wrt_typ cd1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_contd_open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_open_contd_wrt_typ_var : lngen.

Lemma subst_typ_in_conts_open_conts_wrt_typ_var :
forall cs1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_conts_wrt_typ (subst_typ_in_conts A1 X1 cs1) (typ_var_f X2) = subst_typ_in_conts A1 X1 (open_conts_wrt_typ cs1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_conts_open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_open_conts_wrt_typ_var : lngen.

Lemma subst_typ_in_contd_open_contd_wrt_exp_var :
forall cd1 A1 X1 x1,
  open_contd_wrt_exp (subst_typ_in_contd A1 X1 cd1) (exp_var_f x1) = subst_typ_in_contd A1 X1 (open_contd_wrt_exp cd1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_contd_open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_open_contd_wrt_exp_var : lngen.

Lemma subst_typ_in_conts_open_conts_wrt_exp_var :
forall cs1 A1 X1 x1,
  open_conts_wrt_exp (subst_typ_in_conts A1 X1 cs1) (exp_var_f x1) = subst_typ_in_conts A1 X1 (open_conts_wrt_exp cs1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_conts_open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_open_conts_wrt_exp_var : lngen.

Lemma subst_exp_in_contd_open_contd_wrt_typ_var :
forall cd1 e1 x1 X1,
  lc_exp e1 ->
  open_contd_wrt_typ (subst_exp_in_contd e1 x1 cd1) (typ_var_f X1) = subst_exp_in_contd e1 x1 (open_contd_wrt_typ cd1 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_contd_open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_open_contd_wrt_typ_var : lngen.

Lemma subst_exp_in_conts_open_conts_wrt_typ_var :
forall cs1 e1 x1 X1,
  lc_exp e1 ->
  open_conts_wrt_typ (subst_exp_in_conts e1 x1 cs1) (typ_var_f X1) = subst_exp_in_conts e1 x1 (open_conts_wrt_typ cs1 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_conts_open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_open_conts_wrt_typ_var : lngen.

Lemma subst_exp_in_contd_open_contd_wrt_exp_var :
forall cd1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_contd_wrt_exp (subst_exp_in_contd e1 x1 cd1) (exp_var_f x2) = subst_exp_in_contd e1 x1 (open_contd_wrt_exp cd1 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_contd_open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_open_contd_wrt_exp_var : lngen.

Lemma subst_exp_in_conts_open_conts_wrt_exp_var :
forall cs1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_conts_wrt_exp (subst_exp_in_conts e1 x1 cs1) (exp_var_f x2) = subst_exp_in_conts e1 x1 (open_conts_wrt_exp cs1 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_conts_open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_open_conts_wrt_exp_var : lngen.

Lemma subst_typ_in_dbind_open_dbind_wrt_typ_var :
forall db1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_dbind_wrt_typ (subst_typ_in_dbind A1 X1 db1) (typ_var_f X2) = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_dbind_open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_open_dbind_wrt_typ_var : lngen.

Lemma subst_typ_in_work_open_work_wrt_typ_var :
forall w1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_work_wrt_typ (subst_typ_in_work A1 X1 w1) (typ_var_f X2) = subst_typ_in_work A1 X1 (open_work_wrt_typ w1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_work_open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_open_work_wrt_typ_var : lngen.

Lemma subst_typ_in_work_open_work_wrt_exp_var :
forall w1 A1 X1 x1,
  open_work_wrt_exp (subst_typ_in_work A1 X1 w1) (exp_var_f x1) = subst_typ_in_work A1 X1 (open_work_wrt_exp w1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_work_open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_open_work_wrt_exp_var : lngen.

Lemma subst_exp_in_work_open_work_wrt_typ_var :
forall w1 e1 x1 X1,
  lc_exp e1 ->
  open_work_wrt_typ (subst_exp_in_work e1 x1 w1) (typ_var_f X1) = subst_exp_in_work e1 x1 (open_work_wrt_typ w1 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_work_open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_open_work_wrt_typ_var : lngen.

Lemma subst_exp_in_work_open_work_wrt_exp_var :
forall w1 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_work_wrt_exp (subst_exp_in_work e1 x1 w1) (exp_var_f x2) = subst_exp_in_work e1 x1 (open_work_wrt_exp w1 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_work_open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_open_work_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec :
forall A1 A2 X1 n1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof subst_typ_in_typ_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_abind_spec_rec_mutual :
(forall ab1 A1 X1 n1,
  subst_typ_in_abind A1 X1 ab1 = open_abind_wrt_typ_rec n1 A1 (close_abind_wrt_typ_rec n1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_abind_spec_rec :
forall ab1 A1 X1 n1,
  subst_typ_in_abind A1 X1 ab1 = open_abind_wrt_typ_rec n1 A1 (close_abind_wrt_typ_rec n1 X1 ab1).
Proof.
pose proof subst_typ_in_abind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec :
forall e1 A1 X1 n1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof subst_typ_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_spec_rec_subst_typ_in_conts_spec_rec_mutual :
(forall cd1 A1 X1 n1,
  subst_typ_in_contd A1 X1 cd1 = open_contd_wrt_typ_rec n1 A1 (close_contd_wrt_typ_rec n1 X1 cd1)) /\
(forall cs1 A1 X1 n1,
  subst_typ_in_conts A1 X1 cs1 = open_conts_wrt_typ_rec n1 A1 (close_conts_wrt_typ_rec n1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_spec_rec :
forall cd1 A1 X1 n1,
  subst_typ_in_contd A1 X1 cd1 = open_contd_wrt_typ_rec n1 A1 (close_contd_wrt_typ_rec n1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_spec_rec_subst_typ_in_conts_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_conts_spec_rec :
forall cs1 A1 X1 n1,
  subst_typ_in_conts A1 X1 cs1 = open_conts_wrt_typ_rec n1 A1 (close_conts_wrt_typ_rec n1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_spec_rec_subst_typ_in_conts_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_spec_rec_subst_exp_in_conts_spec_rec_mutual :
(forall cd1 e1 x1 n1,
  subst_exp_in_contd e1 x1 cd1 = open_contd_wrt_exp_rec n1 e1 (close_contd_wrt_exp_rec n1 x1 cd1)) /\
(forall cs1 e1 x1 n1,
  subst_exp_in_conts e1 x1 cs1 = open_conts_wrt_exp_rec n1 e1 (close_conts_wrt_exp_rec n1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_spec_rec :
forall cd1 e1 x1 n1,
  subst_exp_in_contd e1 x1 cd1 = open_contd_wrt_exp_rec n1 e1 (close_contd_wrt_exp_rec n1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_spec_rec_subst_exp_in_conts_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_conts_spec_rec :
forall cs1 e1 x1 n1,
  subst_exp_in_conts e1 x1 cs1 = open_conts_wrt_exp_rec n1 e1 (close_conts_wrt_exp_rec n1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_spec_rec_subst_exp_in_conts_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_spec_rec_mutual :
(forall db1 A1 X1 n1,
  subst_typ_in_dbind A1 X1 db1 = open_dbind_wrt_typ_rec n1 A1 (close_dbind_wrt_typ_rec n1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_spec_rec :
forall db1 A1 X1 n1,
  subst_typ_in_dbind A1 X1 db1 = open_dbind_wrt_typ_rec n1 A1 (close_dbind_wrt_typ_rec n1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_spec_rec_mutual :
(forall w1 A1 X1 n1,
  subst_typ_in_work A1 X1 w1 = open_work_wrt_typ_rec n1 A1 (close_work_wrt_typ_rec n1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_spec_rec :
forall w1 A1 X1 n1,
  subst_typ_in_work A1 X1 w1 = open_work_wrt_typ_rec n1 A1 (close_work_wrt_typ_rec n1 X1 w1).
Proof.
pose proof subst_typ_in_work_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_spec_rec_mutual :
(forall w1 e1 x1 n1,
  subst_exp_in_work e1 x1 w1 = open_work_wrt_exp_rec n1 e1 (close_work_wrt_exp_rec n1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_spec_rec :
forall w1 e1 x1 n1,
  subst_exp_in_work e1 x1 w1 = open_work_wrt_exp_rec n1 e1 (close_work_wrt_exp_rec n1 x1 w1).
Proof.
pose proof subst_exp_in_work_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_spec_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_spec :
forall A1 A2 X1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_spec : lngen.

Lemma subst_typ_in_abind_spec :
forall ab1 A1 X1,
  subst_typ_in_abind A1 X1 ab1 = open_abind_wrt_typ (close_abind_wrt_typ X1 ab1) A1.
Proof.
unfold close_abind_wrt_typ; unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_spec : lngen.

Lemma subst_typ_in_exp_spec :
forall e1 A1 X1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) A1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec : lngen.

Lemma subst_typ_in_contd_spec :
forall cd1 A1 X1,
  subst_typ_in_contd A1 X1 cd1 = open_contd_wrt_typ (close_contd_wrt_typ X1 cd1) A1.
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_spec : lngen.

Lemma subst_typ_in_conts_spec :
forall cs1 A1 X1,
  subst_typ_in_conts A1 X1 cs1 = open_conts_wrt_typ (close_conts_wrt_typ X1 cs1) A1.
Proof.
unfold close_conts_wrt_typ; unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_spec : lngen.

Lemma subst_exp_in_contd_spec :
forall cd1 e1 x1,
  subst_exp_in_contd e1 x1 cd1 = open_contd_wrt_exp (close_contd_wrt_exp x1 cd1) e1.
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_spec : lngen.

Lemma subst_exp_in_conts_spec :
forall cs1 e1 x1,
  subst_exp_in_conts e1 x1 cs1 = open_conts_wrt_exp (close_conts_wrt_exp x1 cs1) e1.
Proof.
unfold close_conts_wrt_exp; unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_spec : lngen.

Lemma subst_typ_in_dbind_spec :
forall db1 A1 X1,
  subst_typ_in_dbind A1 X1 db1 = open_dbind_wrt_typ (close_dbind_wrt_typ X1 db1) A1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_spec : lngen.

Lemma subst_typ_in_work_spec :
forall w1 A1 X1,
  subst_typ_in_work A1 X1 w1 = open_work_wrt_typ (close_work_wrt_typ X1 w1) A1.
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_spec : lngen.

Lemma subst_exp_in_work_spec :
forall w1 e1 x1,
  subst_exp_in_work e1 x1 w1 = open_work_wrt_exp (close_work_wrt_exp x1 w1) e1.
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_spec : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_typ_in_typ A2 X1 (subst_typ_in_typ A3 X2 A1) = subst_typ_in_typ (subst_typ_in_typ A2 X1 A3) X2 (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_typ_in_typ A2 X1 (subst_typ_in_typ A3 X2 A1) = subst_typ_in_typ (subst_typ_in_typ A2 X1 A3) X2 (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof subst_typ_in_typ_subst_typ_in_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_subst_typ_in_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_subst_typ_in_abind_mutual :
(forall ab1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_abind A1 X1 (subst_typ_in_abind A2 X2 ab1) = subst_typ_in_abind (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_abind A1 X1 ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_subst_typ_in_abind :
forall ab1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_abind A1 X1 (subst_typ_in_abind A2 X2 ab1) = subst_typ_in_abind (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_abind A1 X1 ab1).
Proof.
pose proof subst_typ_in_abind_subst_typ_in_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_subst_typ_in_abind : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_exp A1 X1 (subst_typ_in_exp A2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp :
forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_exp A1 X1 (subst_typ_in_exp A2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp_mutual :
(forall e1 A1 e2 x1 X1,
  subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp A1 X1 e2) x1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp :
forall e1 A1 e2 x1 X1,
  subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp A1 X1 e2) x1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp A1 X1 e1) = subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp :
forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp A1 X1 e1) = subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_subst_typ_in_contd_subst_typ_in_conts_subst_typ_in_conts_mutual :
(forall cd1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_contd A1 X1 (subst_typ_in_contd A2 X2 cd1) = subst_typ_in_contd (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_conts A1 X1 (subst_typ_in_conts A2 X2 cs1) = subst_typ_in_conts (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_subst_typ_in_contd :
forall cd1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_contd A1 X1 (subst_typ_in_contd A2 X2 cd1) = subst_typ_in_contd (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_subst_typ_in_contd_subst_typ_in_conts_subst_typ_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_subst_typ_in_contd : lngen.

Lemma subst_typ_in_conts_subst_typ_in_conts :
forall cs1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_conts A1 X1 (subst_typ_in_conts A2 X2 cs1) = subst_typ_in_conts (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_subst_typ_in_contd_subst_typ_in_conts_subst_typ_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_subst_typ_in_conts : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_subst_exp_in_contd_subst_typ_in_conts_subst_exp_in_conts_mutual :
(forall cd1 A1 e1 x1 X1,
  subst_typ_in_contd A1 X1 (subst_exp_in_contd e1 x1 cd1) = subst_exp_in_contd (subst_typ_in_exp A1 X1 e1) x1 (subst_typ_in_contd A1 X1 cd1)) /\
(forall cs1 A1 e1 x1 X1,
  subst_typ_in_conts A1 X1 (subst_exp_in_conts e1 x1 cs1) = subst_exp_in_conts (subst_typ_in_exp A1 X1 e1) x1 (subst_typ_in_conts A1 X1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_subst_exp_in_contd :
forall cd1 A1 e1 x1 X1,
  subst_typ_in_contd A1 X1 (subst_exp_in_contd e1 x1 cd1) = subst_exp_in_contd (subst_typ_in_exp A1 X1 e1) x1 (subst_typ_in_contd A1 X1 cd1).
Proof.
pose proof subst_typ_in_contd_subst_exp_in_contd_subst_typ_in_conts_subst_exp_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_subst_exp_in_contd : lngen.

Lemma subst_typ_in_conts_subst_exp_in_conts :
forall cs1 A1 e1 x1 X1,
  subst_typ_in_conts A1 X1 (subst_exp_in_conts e1 x1 cs1) = subst_exp_in_conts (subst_typ_in_exp A1 X1 e1) x1 (subst_typ_in_conts A1 X1 cs1).
Proof.
pose proof subst_typ_in_contd_subst_exp_in_contd_subst_typ_in_conts_subst_exp_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_subst_exp_in_conts : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_subst_typ_in_contd_subst_exp_in_conts_subst_typ_in_conts_mutual :
(forall cd1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_contd e1 x1 (subst_typ_in_contd A1 X1 cd1) = subst_typ_in_contd A1 X1 (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_conts e1 x1 (subst_typ_in_conts A1 X1 cs1) = subst_typ_in_conts A1 X1 (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_subst_typ_in_contd :
forall cd1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_contd e1 x1 (subst_typ_in_contd A1 X1 cd1) = subst_typ_in_contd A1 X1 (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_subst_typ_in_contd_subst_exp_in_conts_subst_typ_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_subst_typ_in_contd : lngen.

Lemma subst_exp_in_conts_subst_typ_in_conts :
forall cs1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_conts e1 x1 (subst_typ_in_conts A1 X1 cs1) = subst_typ_in_conts A1 X1 (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_subst_typ_in_contd_subst_exp_in_conts_subst_typ_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_subst_typ_in_conts : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_subst_exp_in_contd_subst_exp_in_conts_subst_exp_in_conts_mutual :
(forall cd1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_exp_in_contd e1 x1 (subst_exp_in_contd e2 x2 cd1) = subst_exp_in_contd (subst_exp_in_exp e1 x1 e2) x2 (subst_exp_in_contd e1 x1 cd1)) /\
(forall cs1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_exp_in_conts e1 x1 (subst_exp_in_conts e2 x2 cs1) = subst_exp_in_conts (subst_exp_in_exp e1 x1 e2) x2 (subst_exp_in_conts e1 x1 cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_subst_exp_in_contd :
forall cd1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_exp_in_contd e1 x1 (subst_exp_in_contd e2 x2 cd1) = subst_exp_in_contd (subst_exp_in_exp e1 x1 e2) x2 (subst_exp_in_contd e1 x1 cd1).
Proof.
pose proof subst_exp_in_contd_subst_exp_in_contd_subst_exp_in_conts_subst_exp_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_subst_exp_in_contd : lngen.

Lemma subst_exp_in_conts_subst_exp_in_conts :
forall cs1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_exp_in_conts e1 x1 (subst_exp_in_conts e2 x2 cs1) = subst_exp_in_conts (subst_exp_in_exp e1 x1 e2) x2 (subst_exp_in_conts e1 x1 cs1).
Proof.
pose proof subst_exp_in_contd_subst_exp_in_contd_subst_exp_in_conts_subst_exp_in_conts_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_subst_exp_in_conts : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_subst_typ_in_dbind_mutual :
(forall db1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_dbind A1 X1 (subst_typ_in_dbind A2 X2 db1) = subst_typ_in_dbind (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_subst_typ_in_dbind :
forall db1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_dbind A1 X1 (subst_typ_in_dbind A2 X2 db1) = subst_typ_in_dbind (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_subst_typ_in_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_subst_typ_in_dbind : lngen.

(* begin hide *)

Lemma subst_typ_in_work_subst_typ_in_work_mutual :
(forall w1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_work A1 X1 (subst_typ_in_work A2 X2 w1) = subst_typ_in_work (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_subst_typ_in_work :
forall w1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_work A1 X1 (subst_typ_in_work A2 X2 w1) = subst_typ_in_work (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_subst_typ_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_subst_typ_in_work : lngen.

(* begin hide *)

Lemma subst_typ_in_work_subst_exp_in_work_mutual :
(forall w1 A1 e1 x1 X1,
  subst_typ_in_work A1 X1 (subst_exp_in_work e1 x1 w1) = subst_exp_in_work (subst_typ_in_exp A1 X1 e1) x1 (subst_typ_in_work A1 X1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_subst_exp_in_work :
forall w1 A1 e1 x1 X1,
  subst_typ_in_work A1 X1 (subst_exp_in_work e1 x1 w1) = subst_exp_in_work (subst_typ_in_exp A1 X1 e1) x1 (subst_typ_in_work A1 X1 w1).
Proof.
pose proof subst_typ_in_work_subst_exp_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_subst_exp_in_work : lngen.

(* begin hide *)

Lemma subst_exp_in_work_subst_typ_in_work_mutual :
(forall w1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_work e1 x1 (subst_typ_in_work A1 X1 w1) = subst_typ_in_work A1 X1 (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_subst_typ_in_work :
forall w1 e1 A1 X1 x1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_work e1 x1 (subst_typ_in_work A1 X1 w1) = subst_typ_in_work A1 X1 (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_subst_typ_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_subst_typ_in_work : lngen.

(* begin hide *)

Lemma subst_exp_in_work_subst_exp_in_work_mutual :
(forall w1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_exp_in_work e1 x1 (subst_exp_in_work e2 x2 w1) = subst_exp_in_work (subst_exp_in_exp e1 x1 e2) x2 (subst_exp_in_work e1 x1 w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_subst_exp_in_work :
forall w1 e1 e2 x2 x1,
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  subst_exp_in_work e1 x1 (subst_exp_in_work e2 x2 w1) = subst_exp_in_work (subst_exp_in_exp e1 x1 e2) x2 (subst_exp_in_work e1 x1 w1).
Proof.
pose proof subst_exp_in_work_subst_exp_in_work_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_subst_exp_in_work : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2)).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec_mutual :
(forall ab1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_abind A1 X1 ab1 = close_abind_wrt_typ_rec n1 X2 (subst_typ_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X2) ab1))).
Proof.
apply_mutual_ind abind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec :
forall ab1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_abind A1 X1 ab1 = close_abind_wrt_typ_rec n1 X2 (subst_typ_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X2) ab1)).
Proof.
pose proof subst_typ_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_close_abind_wrt_typ_rec_open_abind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_subst_typ_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual :
(forall cd1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_contd cd1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_contd A1 X1 cd1 = close_contd_wrt_typ_rec n1 X2 (subst_typ_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X2) cd1))) *
(forall cs1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_conts cs1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_conts A1 X1 cs1 = close_conts_wrt_typ_rec n1 X2 (subst_typ_in_conts A1 X1 (open_conts_wrt_typ_rec n1 (typ_var_f X2) cs1))).
Proof.
apply_mutual_ind contd_conts_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec :
forall cd1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_contd cd1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_contd A1 X1 cd1 = close_contd_wrt_typ_rec n1 X2 (subst_typ_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X2) cd1)).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_subst_typ_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec :
forall cs1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_conts cs1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_conts A1 X1 cs1 = close_conts_wrt_typ_rec n1 X2 (subst_typ_in_conts A1 X1 (open_conts_wrt_typ_rec n1 (typ_var_f X2) cs1)).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_subst_typ_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_subst_typ_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual :
(forall cd1 A1 X1 x1 n1,
  x1 `notin` fvar_in_contd cd1 ->
  subst_typ_in_contd A1 X1 cd1 = close_contd_wrt_exp_rec n1 x1 (subst_typ_in_contd A1 X1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1))) *
(forall cs1 A1 X1 x1 n1,
  x1 `notin` fvar_in_conts cs1 ->
  subst_typ_in_conts A1 X1 cs1 = close_conts_wrt_exp_rec n1 x1 (subst_typ_in_conts A1 X1 (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1))).
Proof.
apply_mutual_ind contd_conts_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec :
forall cd1 A1 X1 x1 n1,
  x1 `notin` fvar_in_contd cd1 ->
  subst_typ_in_contd A1 X1 cd1 = close_contd_wrt_exp_rec n1 x1 (subst_typ_in_contd A1 X1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1)).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_subst_typ_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec :
forall cs1 A1 X1 x1 n1,
  x1 `notin` fvar_in_conts cs1 ->
  subst_typ_in_conts A1 X1 cs1 = close_conts_wrt_exp_rec n1 x1 (subst_typ_in_conts A1 X1 (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1)).
Proof.
pose proof subst_typ_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_subst_typ_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_subst_exp_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual :
(forall cd1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_contd e1 x1 cd1 = close_contd_wrt_typ_rec n1 X1 (subst_exp_in_contd e1 x1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1))) *
(forall cs1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_conts e1 x1 cs1 = close_conts_wrt_typ_rec n1 X1 (subst_exp_in_conts e1 x1 (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1))).
Proof.
apply_mutual_ind contd_conts_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec :
forall cd1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_contd e1 x1 cd1 = close_contd_wrt_typ_rec n1 X1 (subst_exp_in_contd e1 x1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1)).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_subst_exp_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec :
forall cs1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_conts e1 x1 cs1 = close_conts_wrt_typ_rec n1 X1 (subst_exp_in_conts e1 x1 (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1)).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_typ_rec_open_contd_wrt_typ_rec_subst_exp_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_typ_rec_open_conts_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_subst_exp_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual :
(forall cd1 e1 x1 x2 n1,
  x2 `notin` fvar_in_contd cd1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_contd e1 x1 cd1 = close_contd_wrt_exp_rec n1 x2 (subst_exp_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x2) cd1))) *
(forall cs1 e1 x1 x2 n1,
  x2 `notin` fvar_in_conts cs1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_conts e1 x1 cs1 = close_conts_wrt_exp_rec n1 x2 (subst_exp_in_conts e1 x1 (open_conts_wrt_exp_rec n1 (exp_var_f x2) cs1))).
Proof.
apply_mutual_ind contd_conts_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec :
forall cd1 e1 x1 x2 n1,
  x2 `notin` fvar_in_contd cd1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_contd e1 x1 cd1 = close_contd_wrt_exp_rec n1 x2 (subst_exp_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x2) cd1)).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_subst_exp_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec :
forall cs1 e1 x1 x2 n1,
  x2 `notin` fvar_in_conts cs1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_conts e1 x1 cs1 = close_conts_wrt_exp_rec n1 x2 (subst_exp_in_conts e1 x1 (open_conts_wrt_exp_rec n1 (exp_var_f x2) cs1)).
Proof.
pose proof subst_exp_in_contd_close_contd_wrt_exp_rec_open_contd_wrt_exp_rec_subst_exp_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_exp_rec_open_conts_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_dbind A1 X1 db1 = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X2) db1))).
Proof.
apply_mutual_ind dbind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec :
forall db1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_dbind A1 X1 db1 = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X2) db1)).
Proof.
pose proof subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual :
(forall w1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_work A1 X1 w1 = close_work_wrt_typ_rec n1 X2 (subst_typ_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X2) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec :
forall w1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_work A1 X1 w1 = close_work_wrt_typ_rec n1 X2 (subst_typ_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X2) w1)).
Proof.
pose proof subst_typ_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual :
(forall w1 A1 X1 x1 n1,
  x1 `notin` fvar_in_work w1 ->
  subst_typ_in_work A1 X1 w1 = close_work_wrt_exp_rec n1 x1 (subst_typ_in_work A1 X1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec :
forall w1 A1 X1 x1 n1,
  x1 `notin` fvar_in_work w1 ->
  subst_typ_in_work A1 X1 w1 = close_work_wrt_exp_rec n1 x1 (subst_typ_in_work A1 X1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1)).
Proof.
pose proof subst_typ_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual :
(forall w1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_work e1 x1 w1 = close_work_wrt_typ_rec n1 X1 (subst_exp_in_work e1 x1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec :
forall w1 e1 x1 X1 n1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_work e1 x1 w1 = close_work_wrt_typ_rec n1 X1 (subst_exp_in_work e1 x1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1)).
Proof.
pose proof subst_exp_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_typ_rec_open_work_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual :
(forall w1 e1 x1 x2 n1,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_work e1 x1 w1 = close_work_wrt_exp_rec n1 x2 (subst_exp_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x2) w1))).
Proof.
apply_mutual_ind work_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec :
forall w1 e1 x1 x2 n1,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_work e1 x1 w1 = close_work_wrt_exp_rec n1 x2 (subst_exp_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x2) w1)).
Proof.
pose proof subst_exp_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_exp_rec_open_work_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_typ_in_abind_close_abind_wrt_typ_open_abind_wrt_typ :
forall ab1 A1 X1 X2,
  X2 `notin` ftvar_in_abind ab1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_abind A1 X1 ab1 = close_abind_wrt_typ X2 (subst_typ_in_abind A1 X1 (open_abind_wrt_typ ab1 (typ_var_f X2))).
Proof.
unfold close_abind_wrt_typ; unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_close_abind_wrt_typ_open_abind_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_contd_close_contd_wrt_typ_open_contd_wrt_typ :
forall cd1 A1 X1 X2,
  X2 `notin` ftvar_in_contd cd1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_contd A1 X1 cd1 = close_contd_wrt_typ X2 (subst_typ_in_contd A1 X1 (open_contd_wrt_typ cd1 (typ_var_f X2))).
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_typ_open_contd_wrt_typ : lngen.

Lemma subst_typ_in_conts_close_conts_wrt_typ_open_conts_wrt_typ :
forall cs1 A1 X1 X2,
  X2 `notin` ftvar_in_conts cs1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_conts A1 X1 cs1 = close_conts_wrt_typ X2 (subst_typ_in_conts A1 X1 (open_conts_wrt_typ cs1 (typ_var_f X2))).
Proof.
unfold close_conts_wrt_typ; unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_typ_open_conts_wrt_typ : lngen.

Lemma subst_typ_in_contd_close_contd_wrt_exp_open_contd_wrt_exp :
forall cd1 A1 X1 x1,
  x1 `notin` fvar_in_contd cd1 ->
  lc_typ A1 ->
  subst_typ_in_contd A1 X1 cd1 = close_contd_wrt_exp x1 (subst_typ_in_contd A1 X1 (open_contd_wrt_exp cd1 (exp_var_f x1))).
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_close_contd_wrt_exp_open_contd_wrt_exp : lngen.

Lemma subst_typ_in_conts_close_conts_wrt_exp_open_conts_wrt_exp :
forall cs1 A1 X1 x1,
  x1 `notin` fvar_in_conts cs1 ->
  lc_typ A1 ->
  subst_typ_in_conts A1 X1 cs1 = close_conts_wrt_exp x1 (subst_typ_in_conts A1 X1 (open_conts_wrt_exp cs1 (exp_var_f x1))).
Proof.
unfold close_conts_wrt_exp; unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_close_conts_wrt_exp_open_conts_wrt_exp : lngen.

Lemma subst_exp_in_contd_close_contd_wrt_typ_open_contd_wrt_typ :
forall cd1 e1 x1 X1,
  X1 `notin` ftvar_in_contd cd1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 cd1 = close_contd_wrt_typ X1 (subst_exp_in_contd e1 x1 (open_contd_wrt_typ cd1 (typ_var_f X1))).
Proof.
unfold close_contd_wrt_typ; unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_typ_open_contd_wrt_typ : lngen.

Lemma subst_exp_in_conts_close_conts_wrt_typ_open_conts_wrt_typ :
forall cs1 e1 x1 X1,
  X1 `notin` ftvar_in_conts cs1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 cs1 = close_conts_wrt_typ X1 (subst_exp_in_conts e1 x1 (open_conts_wrt_typ cs1 (typ_var_f X1))).
Proof.
unfold close_conts_wrt_typ; unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_typ_open_conts_wrt_typ : lngen.

Lemma subst_exp_in_contd_close_contd_wrt_exp_open_contd_wrt_exp :
forall cd1 e1 x1 x2,
  x2 `notin` fvar_in_contd cd1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_contd e1 x1 cd1 = close_contd_wrt_exp x2 (subst_exp_in_contd e1 x1 (open_contd_wrt_exp cd1 (exp_var_f x2))).
Proof.
unfold close_contd_wrt_exp; unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_close_contd_wrt_exp_open_contd_wrt_exp : lngen.

Lemma subst_exp_in_conts_close_conts_wrt_exp_open_conts_wrt_exp :
forall cs1 e1 x1 x2,
  x2 `notin` fvar_in_conts cs1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_conts e1 x1 cs1 = close_conts_wrt_exp x2 (subst_exp_in_conts e1 x1 (open_conts_wrt_exp cs1 (exp_var_f x2))).
Proof.
unfold close_conts_wrt_exp; unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_close_conts_wrt_exp_open_conts_wrt_exp : lngen.

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 db1 = close_dbind_wrt_typ X2 (subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X2))).
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ_open_dbind_wrt_typ : lngen.

Lemma subst_typ_in_work_close_work_wrt_typ_open_work_wrt_typ :
forall w1 A1 X1 X2,
  X2 `notin` ftvar_in_work w1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_work A1 X1 w1 = close_work_wrt_typ X2 (subst_typ_in_work A1 X1 (open_work_wrt_typ w1 (typ_var_f X2))).
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_typ_open_work_wrt_typ : lngen.

Lemma subst_typ_in_work_close_work_wrt_exp_open_work_wrt_exp :
forall w1 A1 X1 x1,
  x1 `notin` fvar_in_work w1 ->
  lc_typ A1 ->
  subst_typ_in_work A1 X1 w1 = close_work_wrt_exp x1 (subst_typ_in_work A1 X1 (open_work_wrt_exp w1 (exp_var_f x1))).
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_close_work_wrt_exp_open_work_wrt_exp : lngen.

Lemma subst_exp_in_work_close_work_wrt_typ_open_work_wrt_typ :
forall w1 e1 x1 X1,
  X1 `notin` ftvar_in_work w1 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_work e1 x1 w1 = close_work_wrt_typ X1 (subst_exp_in_work e1 x1 (open_work_wrt_typ w1 (typ_var_f X1))).
Proof.
unfold close_work_wrt_typ; unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_typ_open_work_wrt_typ : lngen.

Lemma subst_exp_in_work_close_work_wrt_exp_open_work_wrt_exp :
forall w1 e1 x1 x2,
  x2 `notin` fvar_in_work w1 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_work e1 x1 w1 = close_work_wrt_exp x2 (subst_exp_in_work e1 x1 (open_work_wrt_exp w1 (exp_var_f x2))).
Proof.
unfold close_work_wrt_exp; unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_close_work_wrt_exp_open_work_wrt_exp : lngen.

Lemma subst_typ_in_typ_typ_all :
forall X2 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_typ A2 `union` singleton X1 ->
  subst_typ_in_typ A1 X1 (typ_all A2) = typ_all (close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_typ_all : lngen.

Lemma subst_typ_in_exp_exp_abs :
forall x1 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 (exp_abs e1) = exp_abs (close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_exp_abs : lngen.

Lemma subst_typ_in_exp_exp_tabs :
forall X2 e1 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_exp e1 `union` singleton X1 ->
  subst_typ_in_exp A1 X1 (exp_tabs e1) = exp_tabs (close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_exp_tabs : lngen.

Lemma subst_exp_in_exp_exp_abs :
forall x2 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fvar_in_exp e1 `union` fvar_in_exp e2 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_abs e2) = exp_abs (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_abs : lngen.

Lemma subst_exp_in_exp_exp_tabs :
forall X1 e2 e1 x1,
  lc_exp e1 ->
  X1 `notin` ftvar_in_exp e1 `union` ftvar_in_exp e2 ->
  subst_exp_in_exp e1 x1 (exp_tabs e2) = exp_tabs (close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_tabs : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1).
Proof.
pose proof subst_typ_in_typ_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_abind_intro_rec_mutual :
(forall ab1 X1 A1 n1,
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ_rec n1 A1 ab1 = subst_typ_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_abind_intro_rec :
forall ab1 X1 A1 n1,
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ_rec n1 A1 ab1 = subst_typ_in_abind A1 X1 (open_abind_wrt_typ_rec n1 (typ_var_f X1) ab1).
Proof.
pose proof subst_typ_in_abind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_abind_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_abind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1).
Proof.
pose proof subst_typ_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof subst_exp_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_contd_intro_rec_subst_typ_in_conts_intro_rec_mutual :
(forall cd1 X1 A1 n1,
  X1 `notin` ftvar_in_contd cd1 ->
  open_contd_wrt_typ_rec n1 A1 cd1 = subst_typ_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1)) /\
(forall cs1 X1 A1 n1,
  X1 `notin` ftvar_in_conts cs1 ->
  open_conts_wrt_typ_rec n1 A1 cs1 = subst_typ_in_conts A1 X1 (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_contd_intro_rec :
forall cd1 X1 A1 n1,
  X1 `notin` ftvar_in_contd cd1 ->
  open_contd_wrt_typ_rec n1 A1 cd1 = subst_typ_in_contd A1 X1 (open_contd_wrt_typ_rec n1 (typ_var_f X1) cd1).
Proof.
pose proof subst_typ_in_contd_intro_rec_subst_typ_in_conts_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_contd_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_contd_intro_rec using solve [auto] : lngen.

Lemma subst_typ_in_conts_intro_rec :
forall cs1 X1 A1 n1,
  X1 `notin` ftvar_in_conts cs1 ->
  open_conts_wrt_typ_rec n1 A1 cs1 = subst_typ_in_conts A1 X1 (open_conts_wrt_typ_rec n1 (typ_var_f X1) cs1).
Proof.
pose proof subst_typ_in_contd_intro_rec_subst_typ_in_conts_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_conts_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_conts_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_contd_intro_rec_subst_exp_in_conts_intro_rec_mutual :
(forall cd1 x1 e1 n1,
  x1 `notin` fvar_in_contd cd1 ->
  open_contd_wrt_exp_rec n1 e1 cd1 = subst_exp_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1)) /\
(forall cs1 x1 e1 n1,
  x1 `notin` fvar_in_conts cs1 ->
  open_conts_wrt_exp_rec n1 e1 cs1 = subst_exp_in_conts e1 x1 (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1)).
Proof.
apply_mutual_ind contd_conts_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_contd_intro_rec :
forall cd1 x1 e1 n1,
  x1 `notin` fvar_in_contd cd1 ->
  open_contd_wrt_exp_rec n1 e1 cd1 = subst_exp_in_contd e1 x1 (open_contd_wrt_exp_rec n1 (exp_var_f x1) cd1).
Proof.
pose proof subst_exp_in_contd_intro_rec_subst_exp_in_conts_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_contd_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_in_contd_intro_rec using solve [auto] : lngen.

Lemma subst_exp_in_conts_intro_rec :
forall cs1 x1 e1 n1,
  x1 `notin` fvar_in_conts cs1 ->
  open_conts_wrt_exp_rec n1 e1 cs1 = subst_exp_in_conts e1 x1 (open_conts_wrt_exp_rec n1 (exp_var_f x1) cs1).
Proof.
pose proof subst_exp_in_contd_intro_rec_subst_exp_in_conts_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_conts_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_in_conts_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_intro_rec_mutual :
(forall db1 X1 A1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_intro_rec :
forall db1 X1 A1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1).
Proof.
pose proof subst_typ_in_dbind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_dbind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_work_intro_rec_mutual :
(forall w1 X1 A1 n1,
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ_rec n1 A1 w1 = subst_typ_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_work_intro_rec :
forall w1 X1 A1 n1,
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ_rec n1 A1 w1 = subst_typ_in_work A1 X1 (open_work_wrt_typ_rec n1 (typ_var_f X1) w1).
Proof.
pose proof subst_typ_in_work_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_work_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_work_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_work_intro_rec_mutual :
(forall w1 x1 e1 n1,
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp_rec n1 e1 w1 = subst_exp_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1)).
Proof.
apply_mutual_ind work_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_work_intro_rec :
forall w1 x1 e1 n1,
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp_rec n1 e1 w1 = subst_exp_in_work e1 x1 (open_work_wrt_exp_rec n1 (exp_var_f x1) w1).
Proof.
pose proof subst_exp_in_work_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_work_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_in_work_intro_rec using solve [auto] : lngen.

Lemma subst_typ_in_typ_intro :
forall X1 A1 A2,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A1 A2 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ A1 (typ_var_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_intro : lngen.

Lemma subst_typ_in_abind_intro :
forall X1 ab1 A1,
  X1 `notin` ftvar_in_abind ab1 ->
  open_abind_wrt_typ ab1 A1 = subst_typ_in_abind A1 X1 (open_abind_wrt_typ ab1 (typ_var_f X1)).
Proof.
unfold open_abind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_abind_intro : lngen.

Lemma subst_typ_in_exp_intro :
forall X1 e1 A1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ e1 A1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X1)).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_intro : lngen.

Lemma subst_exp_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro : lngen.

Lemma subst_typ_in_contd_intro :
forall X1 cd1 A1,
  X1 `notin` ftvar_in_contd cd1 ->
  open_contd_wrt_typ cd1 A1 = subst_typ_in_contd A1 X1 (open_contd_wrt_typ cd1 (typ_var_f X1)).
Proof.
unfold open_contd_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_contd_intro : lngen.

Lemma subst_typ_in_conts_intro :
forall X1 cs1 A1,
  X1 `notin` ftvar_in_conts cs1 ->
  open_conts_wrt_typ cs1 A1 = subst_typ_in_conts A1 X1 (open_conts_wrt_typ cs1 (typ_var_f X1)).
Proof.
unfold open_conts_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_conts_intro : lngen.

Lemma subst_exp_in_contd_intro :
forall x1 cd1 e1,
  x1 `notin` fvar_in_contd cd1 ->
  open_contd_wrt_exp cd1 e1 = subst_exp_in_contd e1 x1 (open_contd_wrt_exp cd1 (exp_var_f x1)).
Proof.
unfold open_contd_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_contd_intro : lngen.

Lemma subst_exp_in_conts_intro :
forall x1 cs1 e1,
  x1 `notin` fvar_in_conts cs1 ->
  open_conts_wrt_exp cs1 e1 = subst_exp_in_conts e1 x1 (open_conts_wrt_exp cs1 (exp_var_f x1)).
Proof.
unfold open_conts_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_conts_intro : lngen.

Lemma subst_typ_in_dbind_intro :
forall X1 db1 A1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ db1 A1 = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X1)).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_intro : lngen.

Lemma subst_typ_in_work_intro :
forall X1 w1 A1,
  X1 `notin` ftvar_in_work w1 ->
  open_work_wrt_typ w1 A1 = subst_typ_in_work A1 X1 (open_work_wrt_typ w1 (typ_var_f X1)).
Proof.
unfold open_work_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_work_intro : lngen.

Lemma subst_exp_in_work_intro :
forall x1 w1 e1,
  x1 `notin` fvar_in_work w1 ->
  open_work_wrt_exp w1 e1 = subst_exp_in_work e1 x1 (open_work_wrt_exp w1 (exp_var_f x1)).
Proof.
unfold open_work_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_work_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
