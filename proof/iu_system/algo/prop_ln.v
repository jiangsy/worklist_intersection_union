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

Scheme atyp_ind' := Induction for atyp Sort Prop.

Combined Scheme atyp_mutind from atyp_ind'.

Scheme atyp_rec' := Induction for atyp Sort Set.

Combined Scheme atyp_mutrec from atyp_rec'.

Scheme abody_ind' := Induction for abody Sort Prop
  with aexp_ind' := Induction for aexp Sort Prop.

Combined Scheme abody_aexp_mutind from abody_ind',aexp_ind'.

Scheme abody_rec' := Induction for abody Sort Set
  with aexp_rec' := Induction for aexp Sort Set.

Combined Scheme abody_aexp_mutrec from abody_rec',aexp_rec'.

Scheme abind_ind' := Induction for abind Sort Prop.

Combined Scheme abind_mutind from abind_ind'.

Scheme abind_rec' := Induction for abind Sort Set.

Combined Scheme abind_mutrec from abind_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_atyp (A1 : atyp) {struct A1} : nat :=
  match A1 with
    | atyp_unit => 1
    | atyp_top => 1
    | atyp_bot => 1
    | atyp_tvar_f X1 => 1
    | atyp_tvar_b n1 => 1
    | atyp_arrow A2 A3 => 1 + (size_atyp A2) + (size_atyp A3)
    | atyp_all A2 => 1 + (size_atyp A2)
    | atyp_union A2 A3 => 1 + (size_atyp A2) + (size_atyp A3)
    | atyp_intersection A2 A3 => 1 + (size_atyp A2) + (size_atyp A3)
  end.

Fixpoint size_abody (abody1 : abody) {struct abody1} : nat :=
  match abody1 with
    | abody_anno e1 A1 => 1 + (size_aexp e1) + (size_atyp A1)
  end

with size_aexp (e1 : aexp) {struct e1} : nat :=
  match e1 with
    | a_exp_unit => 1
    | a_exp_top => 1
    | a_exp_var_f x1 => 1
    | a_exp_var_b n1 => 1
    | a_exp_abs e2 => 1 + (size_aexp e2)
    | a_exp_app e2 e3 => 1 + (size_aexp e2) + (size_aexp e3)
    | a_exp_tabs abody1 => 1 + (size_abody abody1)
    | a_exp_tapp e2 A1 => 1 + (size_aexp e2) + (size_atyp A1)
    | a_exp_anno e2 A1 => 1 + (size_aexp e2) + (size_atyp A1)
  end.

Fixpoint size_abind (b1 : abind) {struct b1} : nat :=
  match b1 with
    | abind_tvarempty => 1
    | abind_stvarempty => 1
    | abind_typ A1 => 1 + (size_atyp A1)
    | abind_bound A1 A2 => 1 + (size_atyp A1) + (size_atyp A2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_atyp_wrt_atyp : nat -> atyp -> Prop :=
  | degree_wrt_atyp_atyp_unit : forall n1,
    degree_atyp_wrt_atyp n1 (atyp_unit)
  | degree_wrt_atyp_atyp_top : forall n1,
    degree_atyp_wrt_atyp n1 (atyp_top)
  | degree_wrt_atyp_atyp_bot : forall n1,
    degree_atyp_wrt_atyp n1 (atyp_bot)
  | degree_wrt_atyp_atyp_tvar_f : forall n1 X1,
    degree_atyp_wrt_atyp n1 (atyp_tvar_f X1)
  | degree_wrt_atyp_atyp_tvar_b : forall n1 n2,
    lt n2 n1 ->
    degree_atyp_wrt_atyp n1 (atyp_tvar_b n2)
  | degree_wrt_atyp_atyp_arrow : forall n1 A1 A2,
    degree_atyp_wrt_atyp n1 A1 ->
    degree_atyp_wrt_atyp n1 A2 ->
    degree_atyp_wrt_atyp n1 (atyp_arrow A1 A2)
  | degree_wrt_atyp_atyp_all : forall n1 A1,
    degree_atyp_wrt_atyp (S n1) A1 ->
    degree_atyp_wrt_atyp n1 (atyp_all A1)
  | degree_wrt_atyp_atyp_union : forall n1 A1 A2,
    degree_atyp_wrt_atyp n1 A1 ->
    degree_atyp_wrt_atyp n1 A2 ->
    degree_atyp_wrt_atyp n1 (atyp_union A1 A2)
  | degree_wrt_atyp_atyp_intersection : forall n1 A1 A2,
    degree_atyp_wrt_atyp n1 A1 ->
    degree_atyp_wrt_atyp n1 A2 ->
    degree_atyp_wrt_atyp n1 (atyp_intersection A1 A2).

Scheme degree_atyp_wrt_atyp_ind' := Induction for degree_atyp_wrt_atyp Sort Prop.

Combined Scheme degree_atyp_wrt_atyp_mutind from degree_atyp_wrt_atyp_ind'.

#[export] Hint Constructors degree_atyp_wrt_atyp : core lngen.

Inductive degree_abody_wrt_atyp : nat -> abody -> Prop :=
  | degree_wrt_atyp_abody_anno : forall n1 e1 A1,
    degree_aexp_wrt_atyp n1 e1 ->
    degree_atyp_wrt_atyp n1 A1 ->
    degree_abody_wrt_atyp n1 (abody_anno e1 A1)

with degree_aexp_wrt_atyp : nat -> aexp -> Prop :=
  | degree_wrt_atyp_a_exp_unit : forall n1,
    degree_aexp_wrt_atyp n1 (a_exp_unit)
  | degree_wrt_atyp_a_exp_top : forall n1,
    degree_aexp_wrt_atyp n1 (a_exp_top)
  | degree_wrt_atyp_a_exp_var_f : forall n1 x1,
    degree_aexp_wrt_atyp n1 (a_exp_var_f x1)
  | degree_wrt_atyp_a_exp_var_b : forall n1 n2,
    degree_aexp_wrt_atyp n1 (a_exp_var_b n2)
  | degree_wrt_atyp_a_exp_abs : forall n1 e1,
    degree_aexp_wrt_atyp n1 e1 ->
    degree_aexp_wrt_atyp n1 (a_exp_abs e1)
  | degree_wrt_atyp_a_exp_app : forall n1 e1 e2,
    degree_aexp_wrt_atyp n1 e1 ->
    degree_aexp_wrt_atyp n1 e2 ->
    degree_aexp_wrt_atyp n1 (a_exp_app e1 e2)
  | degree_wrt_atyp_a_exp_tabs : forall n1 abody1,
    degree_abody_wrt_atyp (S n1) abody1 ->
    degree_aexp_wrt_atyp n1 (a_exp_tabs abody1)
  | degree_wrt_atyp_a_exp_tapp : forall n1 e1 A1,
    degree_aexp_wrt_atyp n1 e1 ->
    degree_atyp_wrt_atyp n1 A1 ->
    degree_aexp_wrt_atyp n1 (a_exp_tapp e1 A1)
  | degree_wrt_atyp_a_exp_anno : forall n1 e1 A1,
    degree_aexp_wrt_atyp n1 e1 ->
    degree_atyp_wrt_atyp n1 A1 ->
    degree_aexp_wrt_atyp n1 (a_exp_anno e1 A1).

Inductive degree_abody_wrt_aexp : nat -> abody -> Prop :=
  | degree_wrt_aexp_abody_anno : forall n1 e1 A1,
    degree_aexp_wrt_aexp n1 e1 ->
    degree_abody_wrt_aexp n1 (abody_anno e1 A1)

with degree_aexp_wrt_aexp : nat -> aexp -> Prop :=
  | degree_wrt_aexp_a_exp_unit : forall n1,
    degree_aexp_wrt_aexp n1 (a_exp_unit)
  | degree_wrt_aexp_a_exp_top : forall n1,
    degree_aexp_wrt_aexp n1 (a_exp_top)
  | degree_wrt_aexp_a_exp_var_f : forall n1 x1,
    degree_aexp_wrt_aexp n1 (a_exp_var_f x1)
  | degree_wrt_aexp_a_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_aexp_wrt_aexp n1 (a_exp_var_b n2)
  | degree_wrt_aexp_a_exp_abs : forall n1 e1,
    degree_aexp_wrt_aexp (S n1) e1 ->
    degree_aexp_wrt_aexp n1 (a_exp_abs e1)
  | degree_wrt_aexp_a_exp_app : forall n1 e1 e2,
    degree_aexp_wrt_aexp n1 e1 ->
    degree_aexp_wrt_aexp n1 e2 ->
    degree_aexp_wrt_aexp n1 (a_exp_app e1 e2)
  | degree_wrt_aexp_a_exp_tabs : forall n1 abody1,
    degree_abody_wrt_aexp n1 abody1 ->
    degree_aexp_wrt_aexp n1 (a_exp_tabs abody1)
  | degree_wrt_aexp_a_exp_tapp : forall n1 e1 A1,
    degree_aexp_wrt_aexp n1 e1 ->
    degree_aexp_wrt_aexp n1 (a_exp_tapp e1 A1)
  | degree_wrt_aexp_a_exp_anno : forall n1 e1 A1,
    degree_aexp_wrt_aexp n1 e1 ->
    degree_aexp_wrt_aexp n1 (a_exp_anno e1 A1).

Scheme degree_abody_wrt_atyp_ind' := Induction for degree_abody_wrt_atyp Sort Prop
  with degree_aexp_wrt_atyp_ind' := Induction for degree_aexp_wrt_atyp Sort Prop.

Combined Scheme degree_abody_wrt_atyp_degree_aexp_wrt_atyp_mutind from degree_abody_wrt_atyp_ind',degree_aexp_wrt_atyp_ind'.

Scheme degree_abody_wrt_aexp_ind' := Induction for degree_abody_wrt_aexp Sort Prop
  with degree_aexp_wrt_aexp_ind' := Induction for degree_aexp_wrt_aexp Sort Prop.

Combined Scheme degree_abody_wrt_aexp_degree_aexp_wrt_aexp_mutind from degree_abody_wrt_aexp_ind',degree_aexp_wrt_aexp_ind'.

#[export] Hint Constructors degree_abody_wrt_atyp : core lngen.

#[export] Hint Constructors degree_aexp_wrt_atyp : core lngen.

#[export] Hint Constructors degree_abody_wrt_aexp : core lngen.

#[export] Hint Constructors degree_aexp_wrt_aexp : core lngen.

Inductive degree_abind_wrt_atyp : nat -> abind -> Prop :=
  | degree_wrt_atyp_abind_tvarempty : forall n1,
    degree_abind_wrt_atyp n1 (abind_tvarempty)
  | degree_wrt_atyp_abind_stvarempty : forall n1,
    degree_abind_wrt_atyp n1 (abind_stvarempty)
  | degree_wrt_atyp_abind_typ : forall n1 A1,
    degree_atyp_wrt_atyp n1 A1 ->
    degree_abind_wrt_atyp n1 (abind_typ A1)
  | degree_wrt_atyp_abind_bound : forall n1 A1 A2,
    degree_atyp_wrt_atyp n1 A1 ->
    degree_atyp_wrt_atyp n1 A2 ->
    degree_abind_wrt_atyp n1 (abind_bound A1 A2).

Scheme degree_abind_wrt_atyp_ind' := Induction for degree_abind_wrt_atyp Sort Prop.

Combined Scheme degree_abind_wrt_atyp_mutind from degree_abind_wrt_atyp_ind'.

#[export] Hint Constructors degree_abind_wrt_atyp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_atyp : atyp -> Set :=
  | lc_set_atyp_unit :
    lc_set_atyp (atyp_unit)
  | lc_set_atyp_top :
    lc_set_atyp (atyp_top)
  | lc_set_atyp_bot :
    lc_set_atyp (atyp_bot)
  | lc_set_atyp_tvar_f : forall X1,
    lc_set_atyp (atyp_tvar_f X1)
  | lc_set_atyp_arrow : forall A1 A2,
    lc_set_atyp A1 ->
    lc_set_atyp A2 ->
    lc_set_atyp (atyp_arrow A1 A2)
  | lc_set_atyp_all : forall A1,
    (forall X1 : typvar, lc_set_atyp (open_atyp_wrt_atyp A1 (atyp_tvar_f X1))) ->
    lc_set_atyp (atyp_all A1)
  | lc_set_atyp_union : forall A1 A2,
    lc_set_atyp A1 ->
    lc_set_atyp A2 ->
    lc_set_atyp (atyp_union A1 A2)
  | lc_set_atyp_intersection : forall A1 A2,
    lc_set_atyp A1 ->
    lc_set_atyp A2 ->
    lc_set_atyp (atyp_intersection A1 A2).

Scheme lc_atyp_ind' := Induction for lc_atyp Sort Prop.

Combined Scheme lc_atyp_mutind from lc_atyp_ind'.

Scheme lc_set_atyp_ind' := Induction for lc_set_atyp Sort Prop.

Combined Scheme lc_set_atyp_mutind from lc_set_atyp_ind'.

Scheme lc_set_atyp_rec' := Induction for lc_set_atyp Sort Set.

Combined Scheme lc_set_atyp_mutrec from lc_set_atyp_rec'.

#[export] Hint Constructors lc_atyp : core lngen.

#[export] Hint Constructors lc_set_atyp : core lngen.

Inductive lc_set_abody : abody -> Set :=
  | lc_set_abody_anno : forall e1 A1,
    lc_set_aexp e1 ->
    lc_set_atyp A1 ->
    lc_set_abody (abody_anno e1 A1)

with lc_set_aexp : aexp -> Set :=
  | lc_set_a_exp_unit :
    lc_set_aexp (a_exp_unit)
  | lc_set_a_exp_top :
    lc_set_aexp (a_exp_top)
  | lc_set_a_exp_var_f : forall x1,
    lc_set_aexp (a_exp_var_f x1)
  | lc_set_a_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_aexp (open_aexp_wrt_aexp e1 (a_exp_var_f x1))) ->
    lc_set_aexp (a_exp_abs e1)
  | lc_set_a_exp_app : forall e1 e2,
    lc_set_aexp e1 ->
    lc_set_aexp e2 ->
    lc_set_aexp (a_exp_app e1 e2)
  | lc_set_a_exp_tabs : forall abody1,
    (forall X1 : typvar, lc_set_abody (open_abody_wrt_atyp abody1 (atyp_tvar_f X1))) ->
    lc_set_aexp (a_exp_tabs abody1)
  | lc_set_a_exp_tapp : forall e1 A1,
    lc_set_aexp e1 ->
    lc_set_atyp A1 ->
    lc_set_aexp (a_exp_tapp e1 A1)
  | lc_set_a_exp_anno : forall e1 A1,
    lc_set_aexp e1 ->
    lc_set_atyp A1 ->
    lc_set_aexp (a_exp_anno e1 A1).

Scheme lc_abody_ind' := Induction for lc_abody Sort Prop
  with lc_aexp_ind' := Induction for lc_aexp Sort Prop.

Combined Scheme lc_abody_lc_aexp_mutind from lc_abody_ind',lc_aexp_ind'.

Scheme lc_set_abody_ind' := Induction for lc_set_abody Sort Prop
  with lc_set_aexp_ind' := Induction for lc_set_aexp Sort Prop.

Combined Scheme lc_set_abody_lc_set_aexp_mutind from lc_set_abody_ind',lc_set_aexp_ind'.

Scheme lc_set_abody_rec' := Induction for lc_set_abody Sort Set
  with lc_set_aexp_rec' := Induction for lc_set_aexp Sort Set.

Combined Scheme lc_set_abody_lc_set_aexp_mutrec from lc_set_abody_rec',lc_set_aexp_rec'.

#[export] Hint Constructors lc_abody : core lngen.

#[export] Hint Constructors lc_aexp : core lngen.

#[export] Hint Constructors lc_set_abody : core lngen.

#[export] Hint Constructors lc_set_aexp : core lngen.

Inductive lc_set_abind : abind -> Set :=
  | lc_set_abind_tvarempty :
    lc_set_abind (abind_tvarempty)
  | lc_set_abind_stvarempty :
    lc_set_abind (abind_stvarempty)
  | lc_set_abind_typ : forall A1,
    lc_set_atyp A1 ->
    lc_set_abind (abind_typ A1)
  | lc_set_abind_bound : forall A1 A2,
    lc_set_atyp A1 ->
    lc_set_atyp A2 ->
    lc_set_abind (abind_bound A1 A2).

Scheme lc_abind_ind' := Induction for lc_abind Sort Prop.

Combined Scheme lc_abind_mutind from lc_abind_ind'.

Scheme lc_set_abind_ind' := Induction for lc_set_abind Sort Prop.

Combined Scheme lc_set_abind_mutind from lc_set_abind_ind'.

Scheme lc_set_abind_rec' := Induction for lc_set_abind Sort Set.

Combined Scheme lc_set_abind_mutrec from lc_set_abind_rec'.

#[export] Hint Constructors lc_abind : core lngen.

#[export] Hint Constructors lc_set_abind : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_atyp_wrt_atyp A1 := forall X1, lc_atyp (open_atyp_wrt_atyp A1 (atyp_tvar_f X1)).

#[export] Hint Unfold body_atyp_wrt_atyp : core.

Definition body_abody_wrt_atyp abody1 := forall X1, lc_abody (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)).

Definition body_aexp_wrt_atyp e1 := forall X1, lc_aexp (open_aexp_wrt_atyp e1 (atyp_tvar_f X1)).

Definition body_abody_wrt_aexp abody1 := forall x1, lc_abody (open_abody_wrt_aexp abody1 (a_exp_var_f x1)).

Definition body_aexp_wrt_aexp e1 := forall x1, lc_aexp (open_aexp_wrt_aexp e1 (a_exp_var_f x1)).

#[export] Hint Unfold body_abody_wrt_atyp : core.

#[export] Hint Unfold body_aexp_wrt_atyp : core.

#[export] Hint Unfold body_abody_wrt_aexp : core.

#[export] Hint Unfold body_aexp_wrt_aexp : core.

Definition body_abind_wrt_atyp b1 := forall X1, lc_abind (open_abind_wrt_atyp b1 (atyp_tvar_f X1)).

#[export] Hint Unfold body_abind_wrt_atyp : core.


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

Lemma size_atyp_min_mutual :
(forall A1, 1 <= size_atyp A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_atyp_min :
forall A1, 1 <= size_atyp A1.
Proof.
pose proof size_atyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_atyp_min : lngen.

(* begin hide *)

Lemma size_abody_min_size_aexp_min_mutual :
(forall abody1, 1 <= size_abody abody1) /\
(forall e1, 1 <= size_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_abody_min :
forall abody1, 1 <= size_abody abody1.
Proof.
pose proof size_abody_min_size_aexp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_min : lngen.

Lemma size_aexp_min :
forall e1, 1 <= size_aexp e1.
Proof.
pose proof size_abody_min_size_aexp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_min : lngen.

(* begin hide *)

Lemma size_abind_min_mutual :
(forall b1, 1 <= size_abind b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_abind_min :
forall b1, 1 <= size_abind b1.
Proof.
pose proof size_abind_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_min : lngen.

(* begin hide *)

Lemma size_atyp_close_atyp_wrt_atyp_rec_mutual :
(forall A1 X1 n1,
  size_atyp (close_atyp_wrt_atyp_rec n1 X1 A1) = size_atyp A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_atyp_close_atyp_wrt_atyp_rec :
forall A1 X1 n1,
  size_atyp (close_atyp_wrt_atyp_rec n1 X1 A1) = size_atyp A1.
Proof.
pose proof size_atyp_close_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_atyp_close_atyp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite size_atyp_close_atyp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_close_abody_wrt_atyp_rec_size_aexp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1,
  size_abody (close_abody_wrt_atyp_rec n1 X1 abody1) = size_abody abody1) /\
(forall e1 X1 n1,
  size_aexp (close_aexp_wrt_atyp_rec n1 X1 e1) = size_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abody_close_abody_wrt_atyp_rec :
forall abody1 X1 n1,
  size_abody (close_abody_wrt_atyp_rec n1 X1 abody1) = size_abody abody1.
Proof.
pose proof size_abody_close_abody_wrt_atyp_rec_size_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_close_abody_wrt_atyp_rec : lngen.
#[export] Hint Rewrite size_abody_close_abody_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_aexp_close_aexp_wrt_atyp_rec :
forall e1 X1 n1,
  size_aexp (close_aexp_wrt_atyp_rec n1 X1 e1) = size_aexp e1.
Proof.
pose proof size_abody_close_abody_wrt_atyp_rec_size_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_close_aexp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite size_aexp_close_aexp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_close_abody_wrt_aexp_rec_size_aexp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1,
  size_abody (close_abody_wrt_aexp_rec n1 x1 abody1) = size_abody abody1) /\
(forall e1 x1 n1,
  size_aexp (close_aexp_wrt_aexp_rec n1 x1 e1) = size_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abody_close_abody_wrt_aexp_rec :
forall abody1 x1 n1,
  size_abody (close_abody_wrt_aexp_rec n1 x1 abody1) = size_abody abody1.
Proof.
pose proof size_abody_close_abody_wrt_aexp_rec_size_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_close_abody_wrt_aexp_rec : lngen.
#[export] Hint Rewrite size_abody_close_abody_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_aexp_close_aexp_wrt_aexp_rec :
forall e1 x1 n1,
  size_aexp (close_aexp_wrt_aexp_rec n1 x1 e1) = size_aexp e1.
Proof.
pose proof size_abody_close_abody_wrt_aexp_rec_size_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_close_aexp_wrt_aexp_rec : lngen.
#[export] Hint Rewrite size_aexp_close_aexp_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abind_close_abind_wrt_atyp_rec_mutual :
(forall b1 X1 n1,
  size_abind (close_abind_wrt_atyp_rec n1 X1 b1) = size_abind b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abind_close_abind_wrt_atyp_rec :
forall b1 X1 n1,
  size_abind (close_abind_wrt_atyp_rec n1 X1 b1) = size_abind b1.
Proof.
pose proof size_abind_close_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_close_abind_wrt_atyp_rec : lngen.
#[export] Hint Rewrite size_abind_close_abind_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_atyp_close_atyp_wrt_atyp :
forall A1 X1,
  size_atyp (close_atyp_wrt_atyp X1 A1) = size_atyp A1.
Proof.
unfold close_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_atyp_close_atyp_wrt_atyp : lngen.
#[export] Hint Rewrite size_atyp_close_atyp_wrt_atyp using solve [auto] : lngen.

Lemma size_abody_close_abody_wrt_atyp :
forall abody1 X1,
  size_abody (close_abody_wrt_atyp X1 abody1) = size_abody abody1.
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_abody_close_abody_wrt_atyp : lngen.
#[export] Hint Rewrite size_abody_close_abody_wrt_atyp using solve [auto] : lngen.

Lemma size_aexp_close_aexp_wrt_atyp :
forall e1 X1,
  size_aexp (close_aexp_wrt_atyp X1 e1) = size_aexp e1.
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_aexp_close_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite size_aexp_close_aexp_wrt_atyp using solve [auto] : lngen.

Lemma size_abody_close_abody_wrt_aexp :
forall abody1 x1,
  size_abody (close_abody_wrt_aexp x1 abody1) = size_abody abody1.
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve size_abody_close_abody_wrt_aexp : lngen.
#[export] Hint Rewrite size_abody_close_abody_wrt_aexp using solve [auto] : lngen.

Lemma size_aexp_close_aexp_wrt_aexp :
forall e1 x1,
  size_aexp (close_aexp_wrt_aexp x1 e1) = size_aexp e1.
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve size_aexp_close_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite size_aexp_close_aexp_wrt_aexp using solve [auto] : lngen.

Lemma size_abind_close_abind_wrt_atyp :
forall b1 X1,
  size_abind (close_abind_wrt_atyp X1 b1) = size_abind b1.
Proof.
unfold close_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_abind_close_abind_wrt_atyp : lngen.
#[export] Hint Rewrite size_abind_close_abind_wrt_atyp using solve [auto] : lngen.

(* begin hide *)

Lemma size_atyp_open_atyp_wrt_atyp_rec_mutual :
(forall A1 A2 n1,
  size_atyp A1 <= size_atyp (open_atyp_wrt_atyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_atyp_open_atyp_wrt_atyp_rec :
forall A1 A2 n1,
  size_atyp A1 <= size_atyp (open_atyp_wrt_atyp_rec n1 A2 A1).
Proof.
pose proof size_atyp_open_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_atyp_open_atyp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_atyp_rec_size_aexp_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 A1 n1,
  size_abody abody1 <= size_abody (open_abody_wrt_atyp_rec n1 A1 abody1)) /\
(forall e1 A1 n1,
  size_aexp e1 <= size_aexp (open_aexp_wrt_atyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_atyp_rec :
forall abody1 A1 n1,
  size_abody abody1 <= size_abody (open_abody_wrt_atyp_rec n1 A1 abody1).
Proof.
pose proof size_abody_open_abody_wrt_atyp_rec_size_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_aexp_open_aexp_wrt_atyp_rec :
forall e1 A1 n1,
  size_aexp e1 <= size_aexp (open_aexp_wrt_atyp_rec n1 A1 e1).
Proof.
pose proof size_abody_open_abody_wrt_atyp_rec_size_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_aexp_rec_size_aexp_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 e1 n1,
  size_abody abody1 <= size_abody (open_abody_wrt_aexp_rec n1 e1 abody1)) /\
(forall e1 e2 n1,
  size_aexp e1 <= size_aexp (open_aexp_wrt_aexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_aexp_rec :
forall abody1 e1 n1,
  size_abody abody1 <= size_abody (open_abody_wrt_aexp_rec n1 e1 abody1).
Proof.
pose proof size_abody_open_abody_wrt_aexp_rec_size_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_aexp_open_aexp_wrt_aexp_rec :
forall e1 e2 n1,
  size_aexp e1 <= size_aexp (open_aexp_wrt_aexp_rec n1 e2 e1).
Proof.
pose proof size_abody_open_abody_wrt_aexp_rec_size_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_atyp_rec_mutual :
(forall b1 A1 n1,
  size_abind b1 <= size_abind (open_abind_wrt_atyp_rec n1 A1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_atyp_rec :
forall b1 A1 n1,
  size_abind b1 <= size_abind (open_abind_wrt_atyp_rec n1 A1 b1).
Proof.
pose proof size_abind_open_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_atyp_rec : lngen.

(* end hide *)

Lemma size_atyp_open_atyp_wrt_atyp :
forall A1 A2,
  size_atyp A1 <= size_atyp (open_atyp_wrt_atyp A1 A2).
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_atyp_open_atyp_wrt_atyp : lngen.

Lemma size_abody_open_abody_wrt_atyp :
forall abody1 A1,
  size_abody abody1 <= size_abody (open_abody_wrt_atyp abody1 A1).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_atyp : lngen.

Lemma size_aexp_open_aexp_wrt_atyp :
forall e1 A1,
  size_aexp e1 <= size_aexp (open_aexp_wrt_atyp e1 A1).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_atyp : lngen.

Lemma size_abody_open_abody_wrt_aexp :
forall abody1 e1,
  size_abody abody1 <= size_abody (open_abody_wrt_aexp abody1 e1).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_aexp : lngen.

Lemma size_aexp_open_aexp_wrt_aexp :
forall e1 e2,
  size_aexp e1 <= size_aexp (open_aexp_wrt_aexp e1 e2).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_aexp : lngen.

Lemma size_abind_open_abind_wrt_atyp :
forall b1 A1,
  size_abind b1 <= size_abind (open_abind_wrt_atyp b1 A1).
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_atyp : lngen.

(* begin hide *)

Lemma size_atyp_open_atyp_wrt_atyp_rec_var_mutual :
(forall A1 X1 n1,
  size_atyp (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1) = size_atyp A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_atyp_open_atyp_wrt_atyp_rec_var :
forall A1 X1 n1,
  size_atyp (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1) = size_atyp A1.
Proof.
pose proof size_atyp_open_atyp_wrt_atyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_atyp_open_atyp_wrt_atyp_rec_var : lngen.
#[export] Hint Rewrite size_atyp_open_atyp_wrt_atyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_atyp_rec_var_size_aexp_open_aexp_wrt_atyp_rec_var_mutual :
(forall abody1 X1 n1,
  size_abody (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1) = size_abody abody1) /\
(forall e1 X1 n1,
  size_aexp (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1) = size_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_atyp_rec_var :
forall abody1 X1 n1,
  size_abody (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1) = size_abody abody1.
Proof.
pose proof size_abody_open_abody_wrt_atyp_rec_var_size_aexp_open_aexp_wrt_atyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_atyp_rec_var : lngen.
#[export] Hint Rewrite size_abody_open_abody_wrt_atyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_aexp_open_aexp_wrt_atyp_rec_var :
forall e1 X1 n1,
  size_aexp (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1) = size_aexp e1.
Proof.
pose proof size_abody_open_abody_wrt_atyp_rec_var_size_aexp_open_aexp_wrt_atyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_atyp_rec_var : lngen.
#[export] Hint Rewrite size_aexp_open_aexp_wrt_atyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_aexp_rec_var_size_aexp_open_aexp_wrt_aexp_rec_var_mutual :
(forall abody1 x1 n1,
  size_abody (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1) = size_abody abody1) /\
(forall e1 x1 n1,
  size_aexp (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1) = size_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abody_open_abody_wrt_aexp_rec_var :
forall abody1 x1 n1,
  size_abody (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1) = size_abody abody1.
Proof.
pose proof size_abody_open_abody_wrt_aexp_rec_var_size_aexp_open_aexp_wrt_aexp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_aexp_rec_var : lngen.
#[export] Hint Rewrite size_abody_open_abody_wrt_aexp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_aexp_open_aexp_wrt_aexp_rec_var :
forall e1 x1 n1,
  size_aexp (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1) = size_aexp e1.
Proof.
pose proof size_abody_open_abody_wrt_aexp_rec_var_size_aexp_open_aexp_wrt_aexp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_aexp_rec_var : lngen.
#[export] Hint Rewrite size_aexp_open_aexp_wrt_aexp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_atyp_rec_var_mutual :
(forall b1 X1 n1,
  size_abind (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1) = size_abind b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_abind_open_abind_wrt_atyp_rec_var :
forall b1 X1 n1,
  size_abind (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1) = size_abind b1.
Proof.
pose proof size_abind_open_abind_wrt_atyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_atyp_rec_var : lngen.
#[export] Hint Rewrite size_abind_open_abind_wrt_atyp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_atyp_open_atyp_wrt_atyp_var :
forall A1 X1,
  size_atyp (open_atyp_wrt_atyp A1 (atyp_tvar_f X1)) = size_atyp A1.
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_atyp_open_atyp_wrt_atyp_var : lngen.
#[export] Hint Rewrite size_atyp_open_atyp_wrt_atyp_var using solve [auto] : lngen.

Lemma size_abody_open_abody_wrt_atyp_var :
forall abody1 X1,
  size_abody (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)) = size_abody abody1.
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_atyp_var : lngen.
#[export] Hint Rewrite size_abody_open_abody_wrt_atyp_var using solve [auto] : lngen.

Lemma size_aexp_open_aexp_wrt_atyp_var :
forall e1 X1,
  size_aexp (open_aexp_wrt_atyp e1 (atyp_tvar_f X1)) = size_aexp e1.
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_atyp_var : lngen.
#[export] Hint Rewrite size_aexp_open_aexp_wrt_atyp_var using solve [auto] : lngen.

Lemma size_abody_open_abody_wrt_aexp_var :
forall abody1 x1,
  size_abody (open_abody_wrt_aexp abody1 (a_exp_var_f x1)) = size_abody abody1.
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve size_abody_open_abody_wrt_aexp_var : lngen.
#[export] Hint Rewrite size_abody_open_abody_wrt_aexp_var using solve [auto] : lngen.

Lemma size_aexp_open_aexp_wrt_aexp_var :
forall e1 x1,
  size_aexp (open_aexp_wrt_aexp e1 (a_exp_var_f x1)) = size_aexp e1.
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve size_aexp_open_aexp_wrt_aexp_var : lngen.
#[export] Hint Rewrite size_aexp_open_aexp_wrt_aexp_var using solve [auto] : lngen.

Lemma size_abind_open_abind_wrt_atyp_var :
forall b1 X1,
  size_abind (open_abind_wrt_atyp b1 (atyp_tvar_f X1)) = size_abind b1.
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve size_abind_open_abind_wrt_atyp_var : lngen.
#[export] Hint Rewrite size_abind_open_abind_wrt_atyp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_atyp_wrt_atyp_S_mutual :
(forall n1 A1,
  degree_atyp_wrt_atyp n1 A1 ->
  degree_atyp_wrt_atyp (S n1) A1).
Proof.
apply_mutual_ind degree_atyp_wrt_atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_atyp_wrt_atyp_S :
forall n1 A1,
  degree_atyp_wrt_atyp n1 A1 ->
  degree_atyp_wrt_atyp (S n1) A1.
Proof.
pose proof degree_atyp_wrt_atyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_S : lngen.

(* begin hide *)

Lemma degree_abody_wrt_atyp_S_degree_aexp_wrt_atyp_S_mutual :
(forall n1 abody1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_abody_wrt_atyp (S n1) abody1) /\
(forall n1 e1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp (S n1) e1).
Proof.
apply_mutual_ind degree_abody_wrt_atyp_degree_aexp_wrt_atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_abody_wrt_atyp_S :
forall n1 abody1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_abody_wrt_atyp (S n1) abody1.
Proof.
pose proof degree_abody_wrt_atyp_S_degree_aexp_wrt_atyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_S : lngen.

Lemma degree_aexp_wrt_atyp_S :
forall n1 e1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp (S n1) e1.
Proof.
pose proof degree_abody_wrt_atyp_S_degree_aexp_wrt_atyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_S : lngen.

(* begin hide *)

Lemma degree_abody_wrt_aexp_S_degree_aexp_wrt_aexp_S_mutual :
(forall n1 abody1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp (S n1) abody1) /\
(forall n1 e1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp (S n1) e1).
Proof.
apply_mutual_ind degree_abody_wrt_aexp_degree_aexp_wrt_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_abody_wrt_aexp_S :
forall n1 abody1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp (S n1) abody1.
Proof.
pose proof degree_abody_wrt_aexp_S_degree_aexp_wrt_aexp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_S : lngen.

Lemma degree_aexp_wrt_aexp_S :
forall n1 e1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp (S n1) e1.
Proof.
pose proof degree_abody_wrt_aexp_S_degree_aexp_wrt_aexp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_S : lngen.

(* begin hide *)

Lemma degree_abind_wrt_atyp_S_mutual :
(forall n1 b1,
  degree_abind_wrt_atyp n1 b1 ->
  degree_abind_wrt_atyp (S n1) b1).
Proof.
apply_mutual_ind degree_abind_wrt_atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_abind_wrt_atyp_S :
forall n1 b1,
  degree_abind_wrt_atyp n1 b1 ->
  degree_abind_wrt_atyp (S n1) b1.
Proof.
pose proof degree_abind_wrt_atyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_S : lngen.

Lemma degree_atyp_wrt_atyp_O :
forall n1 A1,
  degree_atyp_wrt_atyp O A1 ->
  degree_atyp_wrt_atyp n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_O : lngen.

Lemma degree_abody_wrt_atyp_O :
forall n1 abody1,
  degree_abody_wrt_atyp O abody1 ->
  degree_abody_wrt_atyp n1 abody1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_O : lngen.

Lemma degree_aexp_wrt_atyp_O :
forall n1 e1,
  degree_aexp_wrt_atyp O e1 ->
  degree_aexp_wrt_atyp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_O : lngen.

Lemma degree_abody_wrt_aexp_O :
forall n1 abody1,
  degree_abody_wrt_aexp O abody1 ->
  degree_abody_wrt_aexp n1 abody1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_O : lngen.

Lemma degree_aexp_wrt_aexp_O :
forall n1 e1,
  degree_aexp_wrt_aexp O e1 ->
  degree_aexp_wrt_aexp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_O : lngen.

Lemma degree_abind_wrt_atyp_O :
forall n1 b1,
  degree_abind_wrt_atyp O b1 ->
  degree_abind_wrt_atyp n1 b1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_O : lngen.

(* begin hide *)

Lemma degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec_mutual :
(forall A1 X1 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  degree_atyp_wrt_atyp (S n1) (close_atyp_wrt_atyp_rec n1 X1 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec :
forall A1 X1 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  degree_atyp_wrt_atyp (S n1) (close_atyp_wrt_atyp_rec n1 X1 A1).
Proof.
pose proof degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_abody_wrt_atyp (S n1) (close_abody_wrt_atyp_rec n1 X1 abody1)) /\
(forall e1 X1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp (S n1) (close_aexp_wrt_atyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_atyp_rec :
forall abody1 X1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_abody_wrt_atyp (S n1) (close_abody_wrt_atyp_rec n1 X1 abody1).
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_close_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec :
forall e1 X1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp (S n1) (close_aexp_wrt_atyp_rec n1 X1 e1).
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1 n2,
  degree_abody_wrt_atyp n2 abody1 ->
  degree_abody_wrt_atyp n2 (close_abody_wrt_aexp_rec n1 x1 abody1)) /\
(forall e1 x1 n1 n2,
  degree_aexp_wrt_atyp n2 e1 ->
  degree_aexp_wrt_atyp n2 (close_aexp_wrt_aexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_aexp_rec :
forall abody1 x1 n1 n2,
  degree_abody_wrt_atyp n2 abody1 ->
  degree_abody_wrt_atyp n2 (close_abody_wrt_aexp_rec n1 x1 abody1).
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_close_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec :
forall e1 x1 n1 n2,
  degree_aexp_wrt_atyp n2 e1 ->
  degree_aexp_wrt_atyp n2 (close_aexp_wrt_aexp_rec n1 x1 e1).
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1 n2,
  degree_abody_wrt_aexp n2 abody1 ->
  degree_abody_wrt_aexp n2 (close_abody_wrt_atyp_rec n1 X1 abody1)) /\
(forall e1 X1 n1 n2,
  degree_aexp_wrt_aexp n2 e1 ->
  degree_aexp_wrt_aexp n2 (close_aexp_wrt_atyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_atyp_rec :
forall abody1 X1 n1 n2,
  degree_abody_wrt_aexp n2 abody1 ->
  degree_abody_wrt_aexp n2 (close_abody_wrt_atyp_rec n1 X1 abody1).
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_close_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec :
forall e1 X1 n1 n2,
  degree_aexp_wrt_aexp n2 e1 ->
  degree_aexp_wrt_aexp n2 (close_aexp_wrt_atyp_rec n1 X1 e1).
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp (S n1) (close_abody_wrt_aexp_rec n1 x1 abody1)) /\
(forall e1 x1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp (S n1) (close_aexp_wrt_aexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_aexp_rec :
forall abody1 x1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp (S n1) (close_abody_wrt_aexp_rec n1 x1 abody1).
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_close_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec :
forall e1 x1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp (S n1) (close_aexp_wrt_aexp_rec n1 x1 e1).
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_close_abind_wrt_atyp_rec_mutual :
(forall b1 X1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  degree_abind_wrt_atyp (S n1) (close_abind_wrt_atyp_rec n1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_close_abind_wrt_atyp_rec :
forall b1 X1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  degree_abind_wrt_atyp (S n1) (close_abind_wrt_atyp_rec n1 X1 b1).
Proof.
pose proof degree_abind_wrt_atyp_close_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_close_abind_wrt_atyp_rec : lngen.

(* end hide *)

Lemma degree_atyp_wrt_atyp_close_atyp_wrt_atyp :
forall A1 X1,
  degree_atyp_wrt_atyp 0 A1 ->
  degree_atyp_wrt_atyp 1 (close_atyp_wrt_atyp X1 A1).
Proof.
unfold close_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_close_atyp_wrt_atyp : lngen.

Lemma degree_abody_wrt_atyp_close_abody_wrt_atyp :
forall abody1 X1,
  degree_abody_wrt_atyp 0 abody1 ->
  degree_abody_wrt_atyp 1 (close_abody_wrt_atyp X1 abody1).
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_close_abody_wrt_atyp : lngen.

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_atyp :
forall e1 X1,
  degree_aexp_wrt_atyp 0 e1 ->
  degree_aexp_wrt_atyp 1 (close_aexp_wrt_atyp X1 e1).
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_close_aexp_wrt_atyp : lngen.

Lemma degree_abody_wrt_atyp_close_abody_wrt_aexp :
forall abody1 x1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_abody_wrt_atyp n1 (close_abody_wrt_aexp x1 abody1).
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_close_abody_wrt_aexp : lngen.

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_aexp :
forall e1 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp n1 (close_aexp_wrt_aexp x1 e1).
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_close_aexp_wrt_aexp : lngen.

Lemma degree_abody_wrt_aexp_close_abody_wrt_atyp :
forall abody1 X1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp n1 (close_abody_wrt_atyp X1 abody1).
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_close_abody_wrt_atyp : lngen.

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_atyp :
forall e1 X1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 (close_aexp_wrt_atyp X1 e1).
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_close_aexp_wrt_atyp : lngen.

Lemma degree_abody_wrt_aexp_close_abody_wrt_aexp :
forall abody1 x1,
  degree_abody_wrt_aexp 0 abody1 ->
  degree_abody_wrt_aexp 1 (close_abody_wrt_aexp x1 abody1).
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_close_abody_wrt_aexp : lngen.

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_aexp :
forall e1 x1,
  degree_aexp_wrt_aexp 0 e1 ->
  degree_aexp_wrt_aexp 1 (close_aexp_wrt_aexp x1 e1).
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_close_aexp_wrt_aexp : lngen.

Lemma degree_abind_wrt_atyp_close_abind_wrt_atyp :
forall b1 X1,
  degree_abind_wrt_atyp 0 b1 ->
  degree_abind_wrt_atyp 1 (close_abind_wrt_atyp X1 b1).
Proof.
unfold close_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_close_abind_wrt_atyp : lngen.

(* begin hide *)

Lemma degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec_inv_mutual :
(forall A1 X1 n1,
  degree_atyp_wrt_atyp (S n1) (close_atyp_wrt_atyp_rec n1 X1 A1) ->
  degree_atyp_wrt_atyp n1 A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec_inv :
forall A1 X1 n1,
  degree_atyp_wrt_atyp (S n1) (close_atyp_wrt_atyp_rec n1 X1 A1) ->
  degree_atyp_wrt_atyp n1 A1.
Proof.
pose proof degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_atyp_wrt_atyp_close_atyp_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_inv_degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_inv_mutual :
(forall abody1 X1 n1,
  degree_abody_wrt_atyp (S n1) (close_abody_wrt_atyp_rec n1 X1 abody1) ->
  degree_abody_wrt_atyp n1 abody1) /\
(forall e1 X1 n1,
  degree_aexp_wrt_atyp (S n1) (close_aexp_wrt_atyp_rec n1 X1 e1) ->
  degree_aexp_wrt_atyp n1 e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_inv :
forall abody1 X1 n1,
  degree_abody_wrt_atyp (S n1) (close_abody_wrt_atyp_rec n1 X1 abody1) ->
  degree_abody_wrt_atyp n1 abody1.
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_inv_degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_inv :
forall e1 X1 n1,
  degree_aexp_wrt_atyp (S n1) (close_aexp_wrt_atyp_rec n1 X1 e1) ->
  degree_aexp_wrt_atyp n1 e1.
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_atyp_rec_inv_degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_close_aexp_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_inv_degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_inv_mutual :
(forall abody1 x1 n1 n2,
  degree_abody_wrt_atyp n2 (close_abody_wrt_aexp_rec n1 x1 abody1) ->
  degree_abody_wrt_atyp n2 abody1) /\
(forall e1 x1 n1 n2,
  degree_aexp_wrt_atyp n2 (close_aexp_wrt_aexp_rec n1 x1 e1) ->
  degree_aexp_wrt_atyp n2 e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_inv :
forall abody1 x1 n1 n2,
  degree_abody_wrt_atyp n2 (close_abody_wrt_aexp_rec n1 x1 abody1) ->
  degree_abody_wrt_atyp n2 abody1.
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_inv_degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_inv :
forall e1 x1 n1 n2,
  degree_aexp_wrt_atyp n2 (close_aexp_wrt_aexp_rec n1 x1 e1) ->
  degree_aexp_wrt_atyp n2 e1.
Proof.
pose proof degree_abody_wrt_atyp_close_abody_wrt_aexp_rec_inv_degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_close_aexp_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_inv_degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_inv_mutual :
(forall abody1 X1 n1 n2,
  degree_abody_wrt_aexp n2 (close_abody_wrt_atyp_rec n1 X1 abody1) ->
  degree_abody_wrt_aexp n2 abody1) /\
(forall e1 X1 n1 n2,
  degree_aexp_wrt_aexp n2 (close_aexp_wrt_atyp_rec n1 X1 e1) ->
  degree_aexp_wrt_aexp n2 e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_inv :
forall abody1 X1 n1 n2,
  degree_abody_wrt_aexp n2 (close_abody_wrt_atyp_rec n1 X1 abody1) ->
  degree_abody_wrt_aexp n2 abody1.
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_inv_degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_inv :
forall e1 X1 n1 n2,
  degree_aexp_wrt_aexp n2 (close_aexp_wrt_atyp_rec n1 X1 e1) ->
  degree_aexp_wrt_aexp n2 e1.
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_atyp_rec_inv_degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_close_aexp_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_inv_degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_inv_mutual :
(forall abody1 x1 n1,
  degree_abody_wrt_aexp (S n1) (close_abody_wrt_aexp_rec n1 x1 abody1) ->
  degree_abody_wrt_aexp n1 abody1) /\
(forall e1 x1 n1,
  degree_aexp_wrt_aexp (S n1) (close_aexp_wrt_aexp_rec n1 x1 e1) ->
  degree_aexp_wrt_aexp n1 e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_inv :
forall abody1 x1 n1,
  degree_abody_wrt_aexp (S n1) (close_abody_wrt_aexp_rec n1 x1 abody1) ->
  degree_abody_wrt_aexp n1 abody1.
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_inv_degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_inv :
forall e1 x1 n1,
  degree_aexp_wrt_aexp (S n1) (close_aexp_wrt_aexp_rec n1 x1 e1) ->
  degree_aexp_wrt_aexp n1 e1.
Proof.
pose proof degree_abody_wrt_aexp_close_abody_wrt_aexp_rec_inv_degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_close_aexp_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_close_abind_wrt_atyp_rec_inv_mutual :
(forall b1 X1 n1,
  degree_abind_wrt_atyp (S n1) (close_abind_wrt_atyp_rec n1 X1 b1) ->
  degree_abind_wrt_atyp n1 b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_close_abind_wrt_atyp_rec_inv :
forall b1 X1 n1,
  degree_abind_wrt_atyp (S n1) (close_abind_wrt_atyp_rec n1 X1 b1) ->
  degree_abind_wrt_atyp n1 b1.
Proof.
pose proof degree_abind_wrt_atyp_close_abind_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abind_wrt_atyp_close_abind_wrt_atyp_rec_inv : lngen.

(* end hide *)

Lemma degree_atyp_wrt_atyp_close_atyp_wrt_atyp_inv :
forall A1 X1,
  degree_atyp_wrt_atyp 1 (close_atyp_wrt_atyp X1 A1) ->
  degree_atyp_wrt_atyp 0 A1.
Proof.
unfold close_atyp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_atyp_wrt_atyp_close_atyp_wrt_atyp_inv : lngen.

Lemma degree_abody_wrt_atyp_close_abody_wrt_atyp_inv :
forall abody1 X1,
  degree_abody_wrt_atyp 1 (close_abody_wrt_atyp X1 abody1) ->
  degree_abody_wrt_atyp 0 abody1.
Proof.
unfold close_abody_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_close_abody_wrt_atyp_inv : lngen.

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_atyp_inv :
forall e1 X1,
  degree_aexp_wrt_atyp 1 (close_aexp_wrt_atyp X1 e1) ->
  degree_aexp_wrt_atyp 0 e1.
Proof.
unfold close_aexp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_close_aexp_wrt_atyp_inv : lngen.

Lemma degree_abody_wrt_atyp_close_abody_wrt_aexp_inv :
forall abody1 x1 n1,
  degree_abody_wrt_atyp n1 (close_abody_wrt_aexp x1 abody1) ->
  degree_abody_wrt_atyp n1 abody1.
Proof.
unfold close_abody_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_close_abody_wrt_aexp_inv : lngen.

Lemma degree_aexp_wrt_atyp_close_aexp_wrt_aexp_inv :
forall e1 x1 n1,
  degree_aexp_wrt_atyp n1 (close_aexp_wrt_aexp x1 e1) ->
  degree_aexp_wrt_atyp n1 e1.
Proof.
unfold close_aexp_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_close_aexp_wrt_aexp_inv : lngen.

Lemma degree_abody_wrt_aexp_close_abody_wrt_atyp_inv :
forall abody1 X1 n1,
  degree_abody_wrt_aexp n1 (close_abody_wrt_atyp X1 abody1) ->
  degree_abody_wrt_aexp n1 abody1.
Proof.
unfold close_abody_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_close_abody_wrt_atyp_inv : lngen.

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_atyp_inv :
forall e1 X1 n1,
  degree_aexp_wrt_aexp n1 (close_aexp_wrt_atyp X1 e1) ->
  degree_aexp_wrt_aexp n1 e1.
Proof.
unfold close_aexp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_close_aexp_wrt_atyp_inv : lngen.

Lemma degree_abody_wrt_aexp_close_abody_wrt_aexp_inv :
forall abody1 x1,
  degree_abody_wrt_aexp 1 (close_abody_wrt_aexp x1 abody1) ->
  degree_abody_wrt_aexp 0 abody1.
Proof.
unfold close_abody_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_close_abody_wrt_aexp_inv : lngen.

Lemma degree_aexp_wrt_aexp_close_aexp_wrt_aexp_inv :
forall e1 x1,
  degree_aexp_wrt_aexp 1 (close_aexp_wrt_aexp x1 e1) ->
  degree_aexp_wrt_aexp 0 e1.
Proof.
unfold close_aexp_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_close_aexp_wrt_aexp_inv : lngen.

Lemma degree_abind_wrt_atyp_close_abind_wrt_atyp_inv :
forall b1 X1,
  degree_abind_wrt_atyp 1 (close_abind_wrt_atyp X1 b1) ->
  degree_abind_wrt_atyp 0 b1.
Proof.
unfold close_abind_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abind_wrt_atyp_close_abind_wrt_atyp_inv : lngen.

(* begin hide *)

Lemma degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec_mutual :
(forall A1 A2 n1,
  degree_atyp_wrt_atyp (S n1) A1 ->
  degree_atyp_wrt_atyp n1 A2 ->
  degree_atyp_wrt_atyp n1 (open_atyp_wrt_atyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec :
forall A1 A2 n1,
  degree_atyp_wrt_atyp (S n1) A1 ->
  degree_atyp_wrt_atyp n1 A2 ->
  degree_atyp_wrt_atyp n1 (open_atyp_wrt_atyp_rec n1 A2 A1).
Proof.
pose proof degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 A1 n1,
  degree_abody_wrt_atyp (S n1) abody1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abody_wrt_atyp n1 (open_abody_wrt_atyp_rec n1 A1 abody1)) /\
(forall e1 A1 n1,
  degree_aexp_wrt_atyp (S n1) e1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_atyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_atyp_rec :
forall abody1 A1 n1,
  degree_abody_wrt_atyp (S n1) abody1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abody_wrt_atyp n1 (open_abody_wrt_atyp_rec n1 A1 abody1).
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec :
forall e1 A1 n1,
  degree_aexp_wrt_atyp (S n1) e1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_atyp_rec n1 A1 e1).
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 e1 n1 n2,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  degree_abody_wrt_atyp n1 (open_abody_wrt_aexp_rec n2 e1 abody1)) /\
(forall e1 e2 n1 n2,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp n1 e2 ->
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_aexp_rec n2 e2 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_aexp_rec :
forall abody1 e1 n1 n2,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  degree_abody_wrt_atyp n1 (open_abody_wrt_aexp_rec n2 e1 abody1).
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec :
forall e1 e2 n1 n2,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp n1 e2 ->
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_aexp_rec n2 e2 e1).
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 A1 n1 n2,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp n1 (open_abody_wrt_atyp_rec n2 A1 abody1)) /\
(forall e1 A1 n1 n2,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_atyp_rec n2 A1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_atyp_rec :
forall abody1 A1 n1 n2,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp n1 (open_abody_wrt_atyp_rec n2 A1 abody1).
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec :
forall e1 A1 n1 n2,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_atyp_rec n2 A1 e1).
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 e1 n1,
  degree_abody_wrt_aexp (S n1) abody1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  degree_abody_wrt_aexp n1 (open_abody_wrt_aexp_rec n1 e1 abody1)) /\
(forall e1 e2 n1,
  degree_aexp_wrt_aexp (S n1) e1 ->
  degree_aexp_wrt_aexp n1 e2 ->
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_aexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_aexp_rec :
forall abody1 e1 n1,
  degree_abody_wrt_aexp (S n1) abody1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  degree_abody_wrt_aexp n1 (open_abody_wrt_aexp_rec n1 e1 abody1).
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec :
forall e1 e2 n1,
  degree_aexp_wrt_aexp (S n1) e1 ->
  degree_aexp_wrt_aexp n1 e2 ->
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_aexp_rec n1 e2 e1).
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_open_abind_wrt_atyp_rec_mutual :
(forall b1 A1 n1,
  degree_abind_wrt_atyp (S n1) b1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abind_wrt_atyp n1 (open_abind_wrt_atyp_rec n1 A1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_open_abind_wrt_atyp_rec :
forall b1 A1 n1,
  degree_abind_wrt_atyp (S n1) b1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abind_wrt_atyp n1 (open_abind_wrt_atyp_rec n1 A1 b1).
Proof.
pose proof degree_abind_wrt_atyp_open_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_open_abind_wrt_atyp_rec : lngen.

(* end hide *)

Lemma degree_atyp_wrt_atyp_open_atyp_wrt_atyp :
forall A1 A2,
  degree_atyp_wrt_atyp 1 A1 ->
  degree_atyp_wrt_atyp 0 A2 ->
  degree_atyp_wrt_atyp 0 (open_atyp_wrt_atyp A1 A2).
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_open_atyp_wrt_atyp : lngen.

Lemma degree_abody_wrt_atyp_open_abody_wrt_atyp :
forall abody1 A1,
  degree_abody_wrt_atyp 1 abody1 ->
  degree_atyp_wrt_atyp 0 A1 ->
  degree_abody_wrt_atyp 0 (open_abody_wrt_atyp abody1 A1).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_open_abody_wrt_atyp : lngen.

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_atyp :
forall e1 A1,
  degree_aexp_wrt_atyp 1 e1 ->
  degree_atyp_wrt_atyp 0 A1 ->
  degree_aexp_wrt_atyp 0 (open_aexp_wrt_atyp e1 A1).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_open_aexp_wrt_atyp : lngen.

Lemma degree_abody_wrt_atyp_open_abody_wrt_aexp :
forall abody1 e1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  degree_abody_wrt_atyp n1 (open_abody_wrt_aexp abody1 e1).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_open_abody_wrt_aexp : lngen.

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_aexp :
forall e1 e2 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp n1 e2 ->
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_aexp e1 e2).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_open_aexp_wrt_aexp : lngen.

Lemma degree_abody_wrt_aexp_open_abody_wrt_atyp :
forall abody1 A1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp n1 (open_abody_wrt_atyp abody1 A1).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_open_abody_wrt_atyp : lngen.

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_atyp :
forall e1 A1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_atyp e1 A1).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_open_aexp_wrt_atyp : lngen.

Lemma degree_abody_wrt_aexp_open_abody_wrt_aexp :
forall abody1 e1,
  degree_abody_wrt_aexp 1 abody1 ->
  degree_aexp_wrt_aexp 0 e1 ->
  degree_abody_wrt_aexp 0 (open_abody_wrt_aexp abody1 e1).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_open_abody_wrt_aexp : lngen.

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_aexp :
forall e1 e2,
  degree_aexp_wrt_aexp 1 e1 ->
  degree_aexp_wrt_aexp 0 e2 ->
  degree_aexp_wrt_aexp 0 (open_aexp_wrt_aexp e1 e2).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_open_aexp_wrt_aexp : lngen.

Lemma degree_abind_wrt_atyp_open_abind_wrt_atyp :
forall b1 A1,
  degree_abind_wrt_atyp 1 b1 ->
  degree_atyp_wrt_atyp 0 A1 ->
  degree_abind_wrt_atyp 0 (open_abind_wrt_atyp b1 A1).
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_open_abind_wrt_atyp : lngen.

(* begin hide *)

Lemma degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec_inv_mutual :
(forall A1 A2 n1,
  degree_atyp_wrt_atyp n1 (open_atyp_wrt_atyp_rec n1 A2 A1) ->
  degree_atyp_wrt_atyp (S n1) A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec_inv :
forall A1 A2 n1,
  degree_atyp_wrt_atyp n1 (open_atyp_wrt_atyp_rec n1 A2 A1) ->
  degree_atyp_wrt_atyp (S n1) A1.
Proof.
pose proof degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_atyp_wrt_atyp_open_atyp_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_inv_degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_inv_mutual :
(forall abody1 A1 n1,
  degree_abody_wrt_atyp n1 (open_abody_wrt_atyp_rec n1 A1 abody1) ->
  degree_abody_wrt_atyp (S n1) abody1) /\
(forall e1 A1 n1,
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_atyp_rec n1 A1 e1) ->
  degree_aexp_wrt_atyp (S n1) e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_inv :
forall abody1 A1 n1,
  degree_abody_wrt_atyp n1 (open_abody_wrt_atyp_rec n1 A1 abody1) ->
  degree_abody_wrt_atyp (S n1) abody1.
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_inv_degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_inv :
forall e1 A1 n1,
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_atyp_rec n1 A1 e1) ->
  degree_aexp_wrt_atyp (S n1) e1.
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_atyp_rec_inv_degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_open_aexp_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_inv_degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_inv_mutual :
(forall abody1 e1 n1 n2,
  degree_abody_wrt_atyp n1 (open_abody_wrt_aexp_rec n2 e1 abody1) ->
  degree_abody_wrt_atyp n1 abody1) /\
(forall e1 e2 n1 n2,
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_aexp_rec n2 e2 e1) ->
  degree_aexp_wrt_atyp n1 e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_inv :
forall abody1 e1 n1 n2,
  degree_abody_wrt_atyp n1 (open_abody_wrt_aexp_rec n2 e1 abody1) ->
  degree_abody_wrt_atyp n1 abody1.
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_inv_degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_inv :
forall e1 e2 n1 n2,
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_aexp_rec n2 e2 e1) ->
  degree_aexp_wrt_atyp n1 e1.
Proof.
pose proof degree_abody_wrt_atyp_open_abody_wrt_aexp_rec_inv_degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_open_aexp_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_inv_degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_inv_mutual :
(forall abody1 A1 n1 n2,
  degree_abody_wrt_aexp n1 (open_abody_wrt_atyp_rec n2 A1 abody1) ->
  degree_abody_wrt_aexp n1 abody1) /\
(forall e1 A1 n1 n2,
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_atyp_rec n2 A1 e1) ->
  degree_aexp_wrt_aexp n1 e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_inv :
forall abody1 A1 n1 n2,
  degree_abody_wrt_aexp n1 (open_abody_wrt_atyp_rec n2 A1 abody1) ->
  degree_abody_wrt_aexp n1 abody1.
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_inv_degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_inv :
forall e1 A1 n1 n2,
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_atyp_rec n2 A1 e1) ->
  degree_aexp_wrt_aexp n1 e1.
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_atyp_rec_inv_degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_open_aexp_wrt_atyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_inv_degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_inv_mutual :
(forall abody1 e1 n1,
  degree_abody_wrt_aexp n1 (open_abody_wrt_aexp_rec n1 e1 abody1) ->
  degree_abody_wrt_aexp (S n1) abody1) /\
(forall e1 e2 n1,
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_aexp_rec n1 e2 e1) ->
  degree_aexp_wrt_aexp (S n1) e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_inv :
forall abody1 e1 n1,
  degree_abody_wrt_aexp n1 (open_abody_wrt_aexp_rec n1 e1 abody1) ->
  degree_abody_wrt_aexp (S n1) abody1.
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_inv_degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_inv :
forall e1 e2 n1,
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_aexp_rec n1 e2 e1) ->
  degree_aexp_wrt_aexp (S n1) e1.
Proof.
pose proof degree_abody_wrt_aexp_open_abody_wrt_aexp_rec_inv_degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_open_aexp_wrt_aexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_open_abind_wrt_atyp_rec_inv_mutual :
(forall b1 A1 n1,
  degree_abind_wrt_atyp n1 (open_abind_wrt_atyp_rec n1 A1 b1) ->
  degree_abind_wrt_atyp (S n1) b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_abind_wrt_atyp_open_abind_wrt_atyp_rec_inv :
forall b1 A1 n1,
  degree_abind_wrt_atyp n1 (open_abind_wrt_atyp_rec n1 A1 b1) ->
  degree_abind_wrt_atyp (S n1) b1.
Proof.
pose proof degree_abind_wrt_atyp_open_abind_wrt_atyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_abind_wrt_atyp_open_abind_wrt_atyp_rec_inv : lngen.

(* end hide *)

Lemma degree_atyp_wrt_atyp_open_atyp_wrt_atyp_inv :
forall A1 A2,
  degree_atyp_wrt_atyp 0 (open_atyp_wrt_atyp A1 A2) ->
  degree_atyp_wrt_atyp 1 A1.
Proof.
unfold open_atyp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_atyp_wrt_atyp_open_atyp_wrt_atyp_inv : lngen.

Lemma degree_abody_wrt_atyp_open_abody_wrt_atyp_inv :
forall abody1 A1,
  degree_abody_wrt_atyp 0 (open_abody_wrt_atyp abody1 A1) ->
  degree_abody_wrt_atyp 1 abody1.
Proof.
unfold open_abody_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_open_abody_wrt_atyp_inv : lngen.

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_atyp_inv :
forall e1 A1,
  degree_aexp_wrt_atyp 0 (open_aexp_wrt_atyp e1 A1) ->
  degree_aexp_wrt_atyp 1 e1.
Proof.
unfold open_aexp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_open_aexp_wrt_atyp_inv : lngen.

Lemma degree_abody_wrt_atyp_open_abody_wrt_aexp_inv :
forall abody1 e1 n1,
  degree_abody_wrt_atyp n1 (open_abody_wrt_aexp abody1 e1) ->
  degree_abody_wrt_atyp n1 abody1.
Proof.
unfold open_abody_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_atyp_open_abody_wrt_aexp_inv : lngen.

Lemma degree_aexp_wrt_atyp_open_aexp_wrt_aexp_inv :
forall e1 e2 n1,
  degree_aexp_wrt_atyp n1 (open_aexp_wrt_aexp e1 e2) ->
  degree_aexp_wrt_atyp n1 e1.
Proof.
unfold open_aexp_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_atyp_open_aexp_wrt_aexp_inv : lngen.

Lemma degree_abody_wrt_aexp_open_abody_wrt_atyp_inv :
forall abody1 A1 n1,
  degree_abody_wrt_aexp n1 (open_abody_wrt_atyp abody1 A1) ->
  degree_abody_wrt_aexp n1 abody1.
Proof.
unfold open_abody_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_open_abody_wrt_atyp_inv : lngen.

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_atyp_inv :
forall e1 A1 n1,
  degree_aexp_wrt_aexp n1 (open_aexp_wrt_atyp e1 A1) ->
  degree_aexp_wrt_aexp n1 e1.
Proof.
unfold open_aexp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_open_aexp_wrt_atyp_inv : lngen.

Lemma degree_abody_wrt_aexp_open_abody_wrt_aexp_inv :
forall abody1 e1,
  degree_abody_wrt_aexp 0 (open_abody_wrt_aexp abody1 e1) ->
  degree_abody_wrt_aexp 1 abody1.
Proof.
unfold open_abody_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abody_wrt_aexp_open_abody_wrt_aexp_inv : lngen.

Lemma degree_aexp_wrt_aexp_open_aexp_wrt_aexp_inv :
forall e1 e2,
  degree_aexp_wrt_aexp 0 (open_aexp_wrt_aexp e1 e2) ->
  degree_aexp_wrt_aexp 1 e1.
Proof.
unfold open_aexp_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_aexp_wrt_aexp_open_aexp_wrt_aexp_inv : lngen.

Lemma degree_abind_wrt_atyp_open_abind_wrt_atyp_inv :
forall b1 A1,
  degree_abind_wrt_atyp 0 (open_abind_wrt_atyp b1 A1) ->
  degree_abind_wrt_atyp 1 b1.
Proof.
unfold open_abind_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_abind_wrt_atyp_open_abind_wrt_atyp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_atyp_wrt_atyp_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_atyp_wrt_atyp_rec n1 X1 A1 = close_atyp_wrt_atyp_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind atyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_atyp_wrt_atyp_rec_inj :
forall A1 A2 X1 n1,
  close_atyp_wrt_atyp_rec n1 X1 A1 = close_atyp_wrt_atyp_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_atyp_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_atyp_wrt_atyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_atyp_rec_inj_close_aexp_wrt_atyp_rec_inj_mutual :
(forall abody1 abody2 X1 n1,
  close_abody_wrt_atyp_rec n1 X1 abody1 = close_abody_wrt_atyp_rec n1 X1 abody2 ->
  abody1 = abody2) /\
(forall e1 e2 X1 n1,
  close_aexp_wrt_atyp_rec n1 X1 e1 = close_aexp_wrt_atyp_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind abody_aexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_atyp_rec_inj :
forall abody1 abody2 X1 n1,
  close_abody_wrt_atyp_rec n1 X1 abody1 = close_abody_wrt_atyp_rec n1 X1 abody2 ->
  abody1 = abody2.
Proof.
pose proof close_abody_wrt_atyp_rec_inj_close_aexp_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_abody_wrt_atyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_aexp_wrt_atyp_rec_inj :
forall e1 e2 X1 n1,
  close_aexp_wrt_atyp_rec n1 X1 e1 = close_aexp_wrt_atyp_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_abody_wrt_atyp_rec_inj_close_aexp_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_aexp_wrt_atyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexp_rec_inj_close_aexp_wrt_aexp_rec_inj_mutual :
(forall abody1 abody2 x1 n1,
  close_abody_wrt_aexp_rec n1 x1 abody1 = close_abody_wrt_aexp_rec n1 x1 abody2 ->
  abody1 = abody2) /\
(forall e1 e2 x1 n1,
  close_aexp_wrt_aexp_rec n1 x1 e1 = close_aexp_wrt_aexp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind abody_aexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexp_rec_inj :
forall abody1 abody2 x1 n1,
  close_abody_wrt_aexp_rec n1 x1 abody1 = close_abody_wrt_aexp_rec n1 x1 abody2 ->
  abody1 = abody2.
Proof.
pose proof close_abody_wrt_aexp_rec_inj_close_aexp_wrt_aexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_abody_wrt_aexp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_aexp_wrt_aexp_rec_inj :
forall e1 e2 x1 n1,
  close_aexp_wrt_aexp_rec n1 x1 e1 = close_aexp_wrt_aexp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_abody_wrt_aexp_rec_inj_close_aexp_wrt_aexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_aexp_wrt_aexp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_atyp_rec_inj_mutual :
(forall b1 b2 X1 n1,
  close_abind_wrt_atyp_rec n1 X1 b1 = close_abind_wrt_atyp_rec n1 X1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind abind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_atyp_rec_inj :
forall b1 b2 X1 n1,
  close_abind_wrt_atyp_rec n1 X1 b1 = close_abind_wrt_atyp_rec n1 X1 b2 ->
  b1 = b2.
Proof.
pose proof close_abind_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_abind_wrt_atyp_rec_inj : lngen.

(* end hide *)

Lemma close_atyp_wrt_atyp_inj :
forall A1 A2 X1,
  close_atyp_wrt_atyp X1 A1 = close_atyp_wrt_atyp X1 A2 ->
  A1 = A2.
Proof.
unfold close_atyp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_atyp_wrt_atyp_inj : lngen.

Lemma close_abody_wrt_atyp_inj :
forall abody1 abody2 X1,
  close_abody_wrt_atyp X1 abody1 = close_abody_wrt_atyp X1 abody2 ->
  abody1 = abody2.
Proof.
unfold close_abody_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_abody_wrt_atyp_inj : lngen.

Lemma close_aexp_wrt_atyp_inj :
forall e1 e2 X1,
  close_aexp_wrt_atyp X1 e1 = close_aexp_wrt_atyp X1 e2 ->
  e1 = e2.
Proof.
unfold close_aexp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_aexp_wrt_atyp_inj : lngen.

Lemma close_abody_wrt_aexp_inj :
forall abody1 abody2 x1,
  close_abody_wrt_aexp x1 abody1 = close_abody_wrt_aexp x1 abody2 ->
  abody1 = abody2.
Proof.
unfold close_abody_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate close_abody_wrt_aexp_inj : lngen.

Lemma close_aexp_wrt_aexp_inj :
forall e1 e2 x1,
  close_aexp_wrt_aexp x1 e1 = close_aexp_wrt_aexp x1 e2 ->
  e1 = e2.
Proof.
unfold close_aexp_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate close_aexp_wrt_aexp_inj : lngen.

Lemma close_abind_wrt_atyp_inj :
forall b1 b2 X1,
  close_abind_wrt_atyp X1 b1 = close_abind_wrt_atyp X1 b2 ->
  b1 = b2.
Proof.
unfold close_abind_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_abind_wrt_atyp_inj : lngen.

(* begin hide *)

Lemma close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` ftv_in_atyp A1 ->
  close_atyp_wrt_atyp_rec n1 X1 (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1) = A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec :
forall A1 X1 n1,
  X1 `notin` ftv_in_atyp A1 ->
  close_atyp_wrt_atyp_rec n1 X1 (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1) = A1.
Proof.
pose proof close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1,
  X1 `notin` ftv_in_abody abody1 ->
  close_abody_wrt_atyp_rec n1 X1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1) = abody1) /\
(forall e1 X1 n1,
  X1 `notin` ftv_in_aexp e1 ->
  close_aexp_wrt_atyp_rec n1 X1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1) = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec :
forall abody1 X1 n1,
  X1 `notin` ftv_in_abody abody1 ->
  close_abody_wrt_atyp_rec n1 X1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1) = abody1.
Proof.
pose proof close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec : lngen.
#[export] Hint Rewrite close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec :
forall e1 X1 n1,
  X1 `notin` ftv_in_aexp e1 ->
  close_aexp_wrt_atyp_rec n1 X1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1) = e1.
Proof.
pose proof close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1,
  x1 `notin` fv_in_abody abody1 ->
  close_abody_wrt_aexp_rec n1 x1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1) = abody1) /\
(forall e1 x1 n1,
  x1 `notin` fv_in_aexp e1 ->
  close_aexp_wrt_aexp_rec n1 x1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec :
forall abody1 x1 n1,
  x1 `notin` fv_in_abody abody1 ->
  close_abody_wrt_aexp_rec n1 x1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1) = abody1.
Proof.
pose proof close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec : lngen.
#[export] Hint Rewrite close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec :
forall e1 x1 n1,
  x1 `notin` fv_in_aexp e1 ->
  close_aexp_wrt_aexp_rec n1 x1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1) = e1.
Proof.
pose proof close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec : lngen.
#[export] Hint Rewrite close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec_mutual :
(forall b1 X1 n1,
  X1 `notin` ftv_in_abind b1 ->
  close_abind_wrt_atyp_rec n1 X1 (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1) = b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec :
forall b1 X1 n1,
  X1 `notin` ftv_in_abind b1 ->
  close_abind_wrt_atyp_rec n1 X1 (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1) = b1.
Proof.
pose proof close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec : lngen.
#[export] Hint Rewrite close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_atyp_wrt_atyp_open_atyp_wrt_atyp :
forall A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  close_atyp_wrt_atyp X1 (open_atyp_wrt_atyp A1 (atyp_tvar_f X1)) = A1.
Proof.
unfold close_atyp_wrt_atyp; unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_atyp_wrt_atyp_open_atyp_wrt_atyp : lngen.
#[export] Hint Rewrite close_atyp_wrt_atyp_open_atyp_wrt_atyp using solve [auto] : lngen.

Lemma close_abody_wrt_atyp_open_abody_wrt_atyp :
forall abody1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  close_abody_wrt_atyp X1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)) = abody1.
Proof.
unfold close_abody_wrt_atyp; unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_abody_wrt_atyp_open_abody_wrt_atyp : lngen.
#[export] Hint Rewrite close_abody_wrt_atyp_open_abody_wrt_atyp using solve [auto] : lngen.

Lemma close_aexp_wrt_atyp_open_aexp_wrt_atyp :
forall e1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  close_aexp_wrt_atyp X1 (open_aexp_wrt_atyp e1 (atyp_tvar_f X1)) = e1.
Proof.
unfold close_aexp_wrt_atyp; unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_aexp_wrt_atyp_open_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite close_aexp_wrt_atyp_open_aexp_wrt_atyp using solve [auto] : lngen.

Lemma close_abody_wrt_aexp_open_abody_wrt_aexp :
forall abody1 x1,
  x1 `notin` fv_in_abody abody1 ->
  close_abody_wrt_aexp x1 (open_abody_wrt_aexp abody1 (a_exp_var_f x1)) = abody1.
Proof.
unfold close_abody_wrt_aexp; unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve close_abody_wrt_aexp_open_abody_wrt_aexp : lngen.
#[export] Hint Rewrite close_abody_wrt_aexp_open_abody_wrt_aexp using solve [auto] : lngen.

Lemma close_aexp_wrt_aexp_open_aexp_wrt_aexp :
forall e1 x1,
  x1 `notin` fv_in_aexp e1 ->
  close_aexp_wrt_aexp x1 (open_aexp_wrt_aexp e1 (a_exp_var_f x1)) = e1.
Proof.
unfold close_aexp_wrt_aexp; unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve close_aexp_wrt_aexp_open_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite close_aexp_wrt_aexp_open_aexp_wrt_aexp using solve [auto] : lngen.

Lemma close_abind_wrt_atyp_open_abind_wrt_atyp :
forall b1 X1,
  X1 `notin` ftv_in_abind b1 ->
  close_abind_wrt_atyp X1 (open_abind_wrt_atyp b1 (atyp_tvar_f X1)) = b1.
Proof.
unfold close_abind_wrt_atyp; unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_abind_wrt_atyp_open_abind_wrt_atyp : lngen.
#[export] Hint Rewrite close_abind_wrt_atyp_open_abind_wrt_atyp using solve [auto] : lngen.

(* begin hide *)

Lemma open_atyp_wrt_atyp_rec_close_atyp_wrt_atyp_rec_mutual :
(forall A1 X1 n1,
  open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_atyp_wrt_atyp_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_atyp_wrt_atyp_rec_close_atyp_wrt_atyp_rec :
forall A1 X1 n1,
  open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_atyp_wrt_atyp_rec n1 X1 A1) = A1.
Proof.
pose proof open_atyp_wrt_atyp_rec_close_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_atyp_wrt_atyp_rec_close_atyp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite open_atyp_wrt_atyp_rec_close_atyp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_atyp_rec_close_abody_wrt_atyp_rec_open_aexp_wrt_atyp_rec_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1,
  open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_abody_wrt_atyp_rec n1 X1 abody1) = abody1) /\
(forall e1 X1 n1,
  open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_aexp_wrt_atyp_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_atyp_rec_close_abody_wrt_atyp_rec :
forall abody1 X1 n1,
  open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_abody_wrt_atyp_rec n1 X1 abody1) = abody1.
Proof.
pose proof open_abody_wrt_atyp_rec_close_abody_wrt_atyp_rec_open_aexp_wrt_atyp_rec_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abody_wrt_atyp_rec_close_abody_wrt_atyp_rec : lngen.
#[export] Hint Rewrite open_abody_wrt_atyp_rec_close_abody_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_aexp_wrt_atyp_rec_close_aexp_wrt_atyp_rec :
forall e1 X1 n1,
  open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_aexp_wrt_atyp_rec n1 X1 e1) = e1.
Proof.
pose proof open_abody_wrt_atyp_rec_close_abody_wrt_atyp_rec_open_aexp_wrt_atyp_rec_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_aexp_wrt_atyp_rec_close_aexp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite open_aexp_wrt_atyp_rec_close_aexp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexp_rec_close_abody_wrt_aexp_rec_open_aexp_wrt_aexp_rec_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1,
  open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) (close_abody_wrt_aexp_rec n1 x1 abody1) = abody1) /\
(forall e1 x1 n1,
  open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) (close_aexp_wrt_aexp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexp_rec_close_abody_wrt_aexp_rec :
forall abody1 x1 n1,
  open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) (close_abody_wrt_aexp_rec n1 x1 abody1) = abody1.
Proof.
pose proof open_abody_wrt_aexp_rec_close_abody_wrt_aexp_rec_open_aexp_wrt_aexp_rec_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abody_wrt_aexp_rec_close_abody_wrt_aexp_rec : lngen.
#[export] Hint Rewrite open_abody_wrt_aexp_rec_close_abody_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_aexp_wrt_aexp_rec_close_aexp_wrt_aexp_rec :
forall e1 x1 n1,
  open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) (close_aexp_wrt_aexp_rec n1 x1 e1) = e1.
Proof.
pose proof open_abody_wrt_aexp_rec_close_abody_wrt_aexp_rec_open_aexp_wrt_aexp_rec_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_aexp_wrt_aexp_rec_close_aexp_wrt_aexp_rec : lngen.
#[export] Hint Rewrite open_aexp_wrt_aexp_rec_close_aexp_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_atyp_rec_close_abind_wrt_atyp_rec_mutual :
(forall b1 X1 n1,
  open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_abind_wrt_atyp_rec n1 X1 b1) = b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_atyp_rec_close_abind_wrt_atyp_rec :
forall b1 X1 n1,
  open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) (close_abind_wrt_atyp_rec n1 X1 b1) = b1.
Proof.
pose proof open_abind_wrt_atyp_rec_close_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abind_wrt_atyp_rec_close_abind_wrt_atyp_rec : lngen.
#[export] Hint Rewrite open_abind_wrt_atyp_rec_close_abind_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_atyp_wrt_atyp_close_atyp_wrt_atyp :
forall A1 X1,
  open_atyp_wrt_atyp (close_atyp_wrt_atyp X1 A1) (atyp_tvar_f X1) = A1.
Proof.
unfold close_atyp_wrt_atyp; unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_atyp_wrt_atyp_close_atyp_wrt_atyp : lngen.
#[export] Hint Rewrite open_atyp_wrt_atyp_close_atyp_wrt_atyp using solve [auto] : lngen.

Lemma open_abody_wrt_atyp_close_abody_wrt_atyp :
forall abody1 X1,
  open_abody_wrt_atyp (close_abody_wrt_atyp X1 abody1) (atyp_tvar_f X1) = abody1.
Proof.
unfold close_abody_wrt_atyp; unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_abody_wrt_atyp_close_abody_wrt_atyp : lngen.
#[export] Hint Rewrite open_abody_wrt_atyp_close_abody_wrt_atyp using solve [auto] : lngen.

Lemma open_aexp_wrt_atyp_close_aexp_wrt_atyp :
forall e1 X1,
  open_aexp_wrt_atyp (close_aexp_wrt_atyp X1 e1) (atyp_tvar_f X1) = e1.
Proof.
unfold close_aexp_wrt_atyp; unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_aexp_wrt_atyp_close_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite open_aexp_wrt_atyp_close_aexp_wrt_atyp using solve [auto] : lngen.

Lemma open_abody_wrt_aexp_close_abody_wrt_aexp :
forall abody1 x1,
  open_abody_wrt_aexp (close_abody_wrt_aexp x1 abody1) (a_exp_var_f x1) = abody1.
Proof.
unfold close_abody_wrt_aexp; unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve open_abody_wrt_aexp_close_abody_wrt_aexp : lngen.
#[export] Hint Rewrite open_abody_wrt_aexp_close_abody_wrt_aexp using solve [auto] : lngen.

Lemma open_aexp_wrt_aexp_close_aexp_wrt_aexp :
forall e1 x1,
  open_aexp_wrt_aexp (close_aexp_wrt_aexp x1 e1) (a_exp_var_f x1) = e1.
Proof.
unfold close_aexp_wrt_aexp; unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve open_aexp_wrt_aexp_close_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite open_aexp_wrt_aexp_close_aexp_wrt_aexp using solve [auto] : lngen.

Lemma open_abind_wrt_atyp_close_abind_wrt_atyp :
forall b1 X1,
  open_abind_wrt_atyp (close_abind_wrt_atyp X1 b1) (atyp_tvar_f X1) = b1.
Proof.
unfold close_abind_wrt_atyp; unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_abind_wrt_atyp_close_abind_wrt_atyp : lngen.
#[export] Hint Rewrite open_abind_wrt_atyp_close_abind_wrt_atyp using solve [auto] : lngen.

(* begin hide *)

Lemma open_atyp_wrt_atyp_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` ftv_in_atyp A2 ->
  X1 `notin` ftv_in_atyp A1 ->
  open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A2 = open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind atyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_atyp_wrt_atyp_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` ftv_in_atyp A2 ->
  X1 `notin` ftv_in_atyp A1 ->
  open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A2 = open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_atyp_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_atyp_wrt_atyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_atyp_rec_inj_open_aexp_wrt_atyp_rec_inj_mutual :
(forall abody2 abody1 X1 n1,
  X1 `notin` ftv_in_abody abody2 ->
  X1 `notin` ftv_in_abody abody1 ->
  open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody2 = open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1 ->
  abody2 = abody1) /\
(forall e2 e1 X1 n1,
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp e1 ->
  open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e2 = open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_atyp_rec_inj :
forall abody2 abody1 X1 n1,
  X1 `notin` ftv_in_abody abody2 ->
  X1 `notin` ftv_in_abody abody1 ->
  open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody2 = open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1 ->
  abody2 = abody1.
Proof.
pose proof open_abody_wrt_atyp_rec_inj_open_aexp_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_abody_wrt_atyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_aexp_wrt_atyp_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp e1 ->
  open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e2 = open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_abody_wrt_atyp_rec_inj_open_aexp_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_aexp_wrt_atyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexp_rec_inj_open_aexp_wrt_aexp_rec_inj_mutual :
(forall abody2 abody1 x1 n1,
  x1 `notin` fv_in_abody abody2 ->
  x1 `notin` fv_in_abody abody1 ->
  open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody2 = open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1 ->
  abody2 = abody1) /\
(forall e2 e1 x1 n1,
  x1 `notin` fv_in_aexp e2 ->
  x1 `notin` fv_in_aexp e1 ->
  open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e2 = open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexp_rec_inj :
forall abody2 abody1 x1 n1,
  x1 `notin` fv_in_abody abody2 ->
  x1 `notin` fv_in_abody abody1 ->
  open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody2 = open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1 ->
  abody2 = abody1.
Proof.
pose proof open_abody_wrt_aexp_rec_inj_open_aexp_wrt_aexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_abody_wrt_aexp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_aexp_wrt_aexp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_in_aexp e2 ->
  x1 `notin` fv_in_aexp e1 ->
  open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e2 = open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_abody_wrt_aexp_rec_inj_open_aexp_wrt_aexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_aexp_wrt_aexp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_atyp_rec_inj_mutual :
(forall b2 b1 X1 n1,
  X1 `notin` ftv_in_abind b2 ->
  X1 `notin` ftv_in_abind b1 ->
  open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b2 = open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind abind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_atyp_rec_inj :
forall b2 b1 X1 n1,
  X1 `notin` ftv_in_abind b2 ->
  X1 `notin` ftv_in_abind b1 ->
  open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b2 = open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1 ->
  b2 = b1.
Proof.
pose proof open_abind_wrt_atyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_abind_wrt_atyp_rec_inj : lngen.

(* end hide *)

Lemma open_atyp_wrt_atyp_inj :
forall A2 A1 X1,
  X1 `notin` ftv_in_atyp A2 ->
  X1 `notin` ftv_in_atyp A1 ->
  open_atyp_wrt_atyp A2 (atyp_tvar_f X1) = open_atyp_wrt_atyp A1 (atyp_tvar_f X1) ->
  A2 = A1.
Proof.
unfold open_atyp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_atyp_wrt_atyp_inj : lngen.

Lemma open_abody_wrt_atyp_inj :
forall abody2 abody1 X1,
  X1 `notin` ftv_in_abody abody2 ->
  X1 `notin` ftv_in_abody abody1 ->
  open_abody_wrt_atyp abody2 (atyp_tvar_f X1) = open_abody_wrt_atyp abody1 (atyp_tvar_f X1) ->
  abody2 = abody1.
Proof.
unfold open_abody_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_abody_wrt_atyp_inj : lngen.

Lemma open_aexp_wrt_atyp_inj :
forall e2 e1 X1,
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp e1 ->
  open_aexp_wrt_atyp e2 (atyp_tvar_f X1) = open_aexp_wrt_atyp e1 (atyp_tvar_f X1) ->
  e2 = e1.
Proof.
unfold open_aexp_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_aexp_wrt_atyp_inj : lngen.

Lemma open_abody_wrt_aexp_inj :
forall abody2 abody1 x1,
  x1 `notin` fv_in_abody abody2 ->
  x1 `notin` fv_in_abody abody1 ->
  open_abody_wrt_aexp abody2 (a_exp_var_f x1) = open_abody_wrt_aexp abody1 (a_exp_var_f x1) ->
  abody2 = abody1.
Proof.
unfold open_abody_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate open_abody_wrt_aexp_inj : lngen.

Lemma open_aexp_wrt_aexp_inj :
forall e2 e1 x1,
  x1 `notin` fv_in_aexp e2 ->
  x1 `notin` fv_in_aexp e1 ->
  open_aexp_wrt_aexp e2 (a_exp_var_f x1) = open_aexp_wrt_aexp e1 (a_exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_aexp_wrt_aexp; eauto with lngen.
Qed.

#[export] Hint Immediate open_aexp_wrt_aexp_inj : lngen.

Lemma open_abind_wrt_atyp_inj :
forall b2 b1 X1,
  X1 `notin` ftv_in_abind b2 ->
  X1 `notin` ftv_in_abind b1 ->
  open_abind_wrt_atyp b2 (atyp_tvar_f X1) = open_abind_wrt_atyp b1 (atyp_tvar_f X1) ->
  b2 = b1.
Proof.
unfold open_abind_wrt_atyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_abind_wrt_atyp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_atyp_wrt_atyp_of_lc_atyp_mutual :
(forall A1,
  lc_atyp A1 ->
  degree_atyp_wrt_atyp 0 A1).
Proof.
apply_mutual_ind lc_atyp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_atyp_wrt_atyp_of_lc_atyp :
forall A1,
  lc_atyp A1 ->
  degree_atyp_wrt_atyp 0 A1.
Proof.
pose proof degree_atyp_wrt_atyp_of_lc_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_atyp_wrt_atyp_of_lc_atyp : lngen.

(* begin hide *)

Lemma degree_abody_wrt_atyp_of_lc_abody_degree_aexp_wrt_atyp_of_lc_aexp_mutual :
(forall abody1,
  lc_abody abody1 ->
  degree_abody_wrt_atyp 0 abody1) /\
(forall e1,
  lc_aexp e1 ->
  degree_aexp_wrt_atyp 0 e1).
Proof.
apply_mutual_ind lc_abody_lc_aexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_abody_wrt_atyp_of_lc_abody :
forall abody1,
  lc_abody abody1 ->
  degree_abody_wrt_atyp 0 abody1.
Proof.
pose proof degree_abody_wrt_atyp_of_lc_abody_degree_aexp_wrt_atyp_of_lc_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_atyp_of_lc_abody : lngen.

Lemma degree_aexp_wrt_atyp_of_lc_aexp :
forall e1,
  lc_aexp e1 ->
  degree_aexp_wrt_atyp 0 e1.
Proof.
pose proof degree_abody_wrt_atyp_of_lc_abody_degree_aexp_wrt_atyp_of_lc_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_atyp_of_lc_aexp : lngen.

(* begin hide *)

Lemma degree_abody_wrt_aexp_of_lc_abody_degree_aexp_wrt_aexp_of_lc_aexp_mutual :
(forall abody1,
  lc_abody abody1 ->
  degree_abody_wrt_aexp 0 abody1) /\
(forall e1,
  lc_aexp e1 ->
  degree_aexp_wrt_aexp 0 e1).
Proof.
apply_mutual_ind lc_abody_lc_aexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_abody_wrt_aexp_of_lc_abody :
forall abody1,
  lc_abody abody1 ->
  degree_abody_wrt_aexp 0 abody1.
Proof.
pose proof degree_abody_wrt_aexp_of_lc_abody_degree_aexp_wrt_aexp_of_lc_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abody_wrt_aexp_of_lc_abody : lngen.

Lemma degree_aexp_wrt_aexp_of_lc_aexp :
forall e1,
  lc_aexp e1 ->
  degree_aexp_wrt_aexp 0 e1.
Proof.
pose proof degree_abody_wrt_aexp_of_lc_abody_degree_aexp_wrt_aexp_of_lc_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_aexp_wrt_aexp_of_lc_aexp : lngen.

(* begin hide *)

Lemma degree_abind_wrt_atyp_of_lc_abind_mutual :
(forall b1,
  lc_abind b1 ->
  degree_abind_wrt_atyp 0 b1).
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

Lemma degree_abind_wrt_atyp_of_lc_abind :
forall b1,
  lc_abind b1 ->
  degree_abind_wrt_atyp 0 b1.
Proof.
pose proof degree_abind_wrt_atyp_of_lc_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_abind_wrt_atyp_of_lc_abind : lngen.

(* begin hide *)

Lemma lc_atyp_of_degree_size_mutual :
forall i1,
(forall A1,
  size_atyp A1 = i1 ->
  degree_atyp_wrt_atyp 0 A1 ->
  lc_atyp A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind atyp_mutind;
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

Lemma lc_atyp_of_degree :
forall A1,
  degree_atyp_wrt_atyp 0 A1 ->
  lc_atyp A1.
Proof.
intros A1; intros;
pose proof (lc_atyp_of_degree_size_mutual (size_atyp A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_atyp_of_degree : lngen.

(* begin hide *)

Lemma lc_abody_of_degree_lc_aexp_of_degree_size_mutual :
forall i1,
(forall abody1,
  size_abody abody1 = i1 ->
  degree_abody_wrt_atyp 0 abody1 ->
  degree_abody_wrt_aexp 0 abody1 ->
  lc_abody abody1) /\
(forall e1,
  size_aexp e1 = i1 ->
  degree_aexp_wrt_atyp 0 e1 ->
  degree_aexp_wrt_aexp 0 e1 ->
  lc_aexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind abody_aexp_mutind;
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

Lemma lc_abody_of_degree :
forall abody1,
  degree_abody_wrt_atyp 0 abody1 ->
  degree_abody_wrt_aexp 0 abody1 ->
  lc_abody abody1.
Proof.
intros abody1; intros;
pose proof (lc_abody_of_degree_lc_aexp_of_degree_size_mutual (size_abody abody1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_abody_of_degree : lngen.

Lemma lc_aexp_of_degree :
forall e1,
  degree_aexp_wrt_atyp 0 e1 ->
  degree_aexp_wrt_aexp 0 e1 ->
  lc_aexp e1.
Proof.
intros e1; intros;
pose proof (lc_abody_of_degree_lc_aexp_of_degree_size_mutual (size_aexp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_aexp_of_degree : lngen.

(* begin hide *)

Lemma lc_abind_of_degree_size_mutual :
forall i1,
(forall b1,
  size_abind b1 = i1 ->
  degree_abind_wrt_atyp 0 b1 ->
  lc_abind b1).
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
forall b1,
  degree_abind_wrt_atyp 0 b1 ->
  lc_abind b1.
Proof.
intros b1; intros;
pose proof (lc_abind_of_degree_size_mutual (size_abind b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_abind_of_degree : lngen.

Ltac atyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_atyp_wrt_atyp_of_lc_atyp in J1; clear H
          end).

Ltac abody_aexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_abody_wrt_atyp_of_lc_abody in J1;
              let J2 := fresh in pose proof H as J2; apply degree_abody_wrt_aexp_of_lc_abody in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_aexp_wrt_atyp_of_lc_aexp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_aexp_wrt_aexp_of_lc_aexp in J2; clear H
          end).

Ltac abind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_abind_wrt_atyp_of_lc_abind in J1; clear H
          end).

Lemma lc_atyp_all_exists :
forall X1 A1,
  lc_atyp (open_atyp_wrt_atyp A1 (atyp_tvar_f X1)) ->
  lc_atyp (atyp_all A1).
Proof.
intros; atyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_a_exp_abs_exists :
forall x1 e1,
  lc_aexp (open_aexp_wrt_aexp e1 (a_exp_var_f x1)) ->
  lc_aexp (a_exp_abs e1).
Proof.
intros; abody_aexp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_a_exp_tabs_exists :
forall X1 abody1,
  lc_abody (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)) ->
  lc_aexp (a_exp_tabs abody1).
Proof.
intros; abody_aexp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_atyp (atyp_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_atyp_all_exists X1) : core.

#[export] Hint Extern 1 (lc_aexp (a_exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_a_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_aexp (a_exp_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_a_exp_tabs_exists X1) : core.

Lemma lc_body_atyp_wrt_atyp :
forall A1 A2,
  body_atyp_wrt_atyp A1 ->
  lc_atyp A2 ->
  lc_atyp (open_atyp_wrt_atyp A1 A2).
Proof.
unfold body_atyp_wrt_atyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
atyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_atyp_wrt_atyp : lngen.

Lemma lc_body_abody_wrt_atyp :
forall abody1 A1,
  body_abody_wrt_atyp abody1 ->
  lc_atyp A1 ->
  lc_abody (open_abody_wrt_atyp abody1 A1).
Proof.
unfold body_abody_wrt_atyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
abody_aexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_abody_wrt_atyp : lngen.

Lemma lc_body_aexp_wrt_atyp :
forall e1 A1,
  body_aexp_wrt_atyp e1 ->
  lc_atyp A1 ->
  lc_aexp (open_aexp_wrt_atyp e1 A1).
Proof.
unfold body_aexp_wrt_atyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
abody_aexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_aexp_wrt_atyp : lngen.

Lemma lc_body_abody_wrt_aexp :
forall abody1 e1,
  body_abody_wrt_aexp abody1 ->
  lc_aexp e1 ->
  lc_abody (open_abody_wrt_aexp abody1 e1).
Proof.
unfold body_abody_wrt_aexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
abody_aexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_abody_wrt_aexp : lngen.

Lemma lc_body_aexp_wrt_aexp :
forall e1 e2,
  body_aexp_wrt_aexp e1 ->
  lc_aexp e2 ->
  lc_aexp (open_aexp_wrt_aexp e1 e2).
Proof.
unfold body_aexp_wrt_aexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
abody_aexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_aexp_wrt_aexp : lngen.

Lemma lc_body_abind_wrt_atyp :
forall b1 A1,
  body_abind_wrt_atyp b1 ->
  lc_atyp A1 ->
  lc_abind (open_abind_wrt_atyp b1 A1).
Proof.
unfold body_abind_wrt_atyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
abind_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_abind_wrt_atyp : lngen.

Lemma lc_body_atyp_all_1 :
forall A1,
  lc_atyp (atyp_all A1) ->
  body_atyp_wrt_atyp A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_atyp_all_1 : lngen.

Lemma lc_body_a_exp_abs_1 :
forall e1,
  lc_aexp (a_exp_abs e1) ->
  body_aexp_wrt_aexp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_exp_abs_1 : lngen.

Lemma lc_body_a_exp_tabs_1 :
forall abody1,
  lc_aexp (a_exp_tabs abody1) ->
  body_abody_wrt_atyp abody1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_a_exp_tabs_1 : lngen.

(* begin hide *)

Lemma lc_atyp_unique_mutual :
(forall A1 (proof2 proof3 : lc_atyp A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_atyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_atyp_unique :
forall A1 (proof2 proof3 : lc_atyp A1), proof2 = proof3.
Proof.
pose proof lc_atyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_atyp_unique : lngen.

(* begin hide *)

Lemma lc_abody_unique_lc_aexp_unique_mutual :
(forall abody1 (proof2 proof3 : lc_abody abody1), proof2 = proof3) /\
(forall e1 (proof2 proof3 : lc_aexp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_abody_lc_aexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_abody_unique :
forall abody1 (proof2 proof3 : lc_abody abody1), proof2 = proof3.
Proof.
pose proof lc_abody_unique_lc_aexp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_abody_unique : lngen.

Lemma lc_aexp_unique :
forall e1 (proof2 proof3 : lc_aexp e1), proof2 = proof3.
Proof.
pose proof lc_abody_unique_lc_aexp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_aexp_unique : lngen.

(* begin hide *)

Lemma lc_abind_unique_mutual :
(forall b1 (proof2 proof3 : lc_abind b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_abind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_abind_unique :
forall b1 (proof2 proof3 : lc_abind b1), proof2 = proof3.
Proof.
pose proof lc_abind_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_abind_unique : lngen.

(* begin hide *)

Lemma lc_atyp_of_lc_set_atyp_mutual :
(forall A1, lc_set_atyp A1 -> lc_atyp A1).
Proof.
apply_mutual_ind lc_set_atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_atyp_of_lc_set_atyp :
forall A1, lc_set_atyp A1 -> lc_atyp A1.
Proof.
pose proof lc_atyp_of_lc_set_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_atyp_of_lc_set_atyp : lngen.

(* begin hide *)

Lemma lc_abody_of_lc_set_abody_lc_aexp_of_lc_set_aexp_mutual :
(forall abody1, lc_set_abody abody1 -> lc_abody abody1) /\
(forall e1, lc_set_aexp e1 -> lc_aexp e1).
Proof.
apply_mutual_ind lc_set_abody_lc_set_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_abody_of_lc_set_abody :
forall abody1, lc_set_abody abody1 -> lc_abody abody1.
Proof.
pose proof lc_abody_of_lc_set_abody_lc_aexp_of_lc_set_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_abody_of_lc_set_abody : lngen.

Lemma lc_aexp_of_lc_set_aexp :
forall e1, lc_set_aexp e1 -> lc_aexp e1.
Proof.
pose proof lc_abody_of_lc_set_abody_lc_aexp_of_lc_set_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_aexp_of_lc_set_aexp : lngen.

(* begin hide *)

Lemma lc_abind_of_lc_set_abind_mutual :
(forall b1, lc_set_abind b1 -> lc_abind b1).
Proof.
apply_mutual_ind lc_set_abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_abind_of_lc_set_abind :
forall b1, lc_set_abind b1 -> lc_abind b1.
Proof.
pose proof lc_abind_of_lc_set_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_abind_of_lc_set_abind : lngen.

(* begin hide *)

Lemma lc_set_atyp_of_lc_atyp_size_mutual :
forall i1,
(forall A1,
  size_atyp A1 = i1 ->
  lc_atyp A1 ->
  lc_set_atyp A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind atyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_atyp_of_lc_atyp];
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

Lemma lc_set_atyp_of_lc_atyp :
forall A1,
  lc_atyp A1 ->
  lc_set_atyp A1.
Proof.
intros A1; intros;
pose proof (lc_set_atyp_of_lc_atyp_size_mutual (size_atyp A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_atyp_of_lc_atyp : lngen.

(* begin hide *)

Lemma lc_set_abody_of_lc_abody_lc_set_aexp_of_lc_aexp_size_mutual :
forall i1,
(forall abody1,
  size_abody abody1 = i1 ->
  lc_abody abody1 ->
  lc_set_abody abody1) *
(forall e1,
  size_aexp e1 = i1 ->
  lc_aexp e1 ->
  lc_set_aexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind abody_aexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_atyp_of_lc_atyp
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_aexp_of_lc_aexp
 | apply lc_set_atyp_of_lc_atyp
 | apply lc_set_abody_of_lc_abody
 | apply lc_set_aexp_of_lc_aexp];
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

Lemma lc_set_abody_of_lc_abody :
forall abody1,
  lc_abody abody1 ->
  lc_set_abody abody1.
Proof.
intros abody1; intros;
pose proof (lc_set_abody_of_lc_abody_lc_set_aexp_of_lc_aexp_size_mutual (size_abody abody1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_abody_of_lc_abody : lngen.

Lemma lc_set_aexp_of_lc_aexp :
forall e1,
  lc_aexp e1 ->
  lc_set_aexp e1.
Proof.
intros e1; intros;
pose proof (lc_set_abody_of_lc_abody_lc_set_aexp_of_lc_aexp_size_mutual (size_aexp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_aexp_of_lc_aexp : lngen.

(* begin hide *)

Lemma lc_set_abind_of_lc_abind_size_mutual :
forall i1,
(forall b1,
  size_abind b1 = i1 ->
  lc_abind b1 ->
  lc_set_abind b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind abind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_atyp_of_lc_atyp
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
forall b1,
  lc_abind b1 ->
  lc_set_abind b1.
Proof.
intros b1; intros;
pose proof (lc_set_abind_of_lc_abind_size_mutual (size_abind b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_abind_of_lc_abind : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp_mutual :
(forall A1 X1 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 `notin` ftv_in_atyp A1 ->
  close_atyp_wrt_atyp_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp :
forall A1 X1 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 `notin` ftv_in_atyp A1 ->
  close_atyp_wrt_atyp_rec n1 X1 A1 = A1.
Proof.
pose proof close_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp : lngen.
#[export] Hint Rewrite close_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_atyp_rec_degree_abody_wrt_atyp_close_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp_mutual :
(forall abody1 X1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  X1 `notin` ftv_in_abody abody1 ->
  close_abody_wrt_atyp_rec n1 X1 abody1 = abody1) /\
(forall e1 X1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  X1 `notin` ftv_in_aexp e1 ->
  close_aexp_wrt_atyp_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_atyp_rec_degree_abody_wrt_atyp :
forall abody1 X1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  X1 `notin` ftv_in_abody abody1 ->
  close_abody_wrt_atyp_rec n1 X1 abody1 = abody1.
Proof.
pose proof close_abody_wrt_atyp_rec_degree_abody_wrt_atyp_close_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abody_wrt_atyp_rec_degree_abody_wrt_atyp : lngen.
#[export] Hint Rewrite close_abody_wrt_atyp_rec_degree_abody_wrt_atyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp :
forall e1 X1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  X1 `notin` ftv_in_aexp e1 ->
  close_aexp_wrt_atyp_rec n1 X1 e1 = e1.
Proof.
pose proof close_abody_wrt_atyp_rec_degree_abody_wrt_atyp_close_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite close_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexp_rec_degree_abody_wrt_aexp_close_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp_mutual :
(forall abody1 x1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  x1 `notin` fv_in_abody abody1 ->
  close_abody_wrt_aexp_rec n1 x1 abody1 = abody1) /\
(forall e1 x1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  x1 `notin` fv_in_aexp e1 ->
  close_aexp_wrt_aexp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abody_wrt_aexp_rec_degree_abody_wrt_aexp :
forall abody1 x1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  x1 `notin` fv_in_abody abody1 ->
  close_abody_wrt_aexp_rec n1 x1 abody1 = abody1.
Proof.
pose proof close_abody_wrt_aexp_rec_degree_abody_wrt_aexp_close_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abody_wrt_aexp_rec_degree_abody_wrt_aexp : lngen.
#[export] Hint Rewrite close_abody_wrt_aexp_rec_degree_abody_wrt_aexp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp :
forall e1 x1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  x1 `notin` fv_in_aexp e1 ->
  close_aexp_wrt_aexp_rec n1 x1 e1 = e1.
Proof.
pose proof close_abody_wrt_aexp_rec_degree_abody_wrt_aexp_close_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite close_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_atyp_rec_degree_abind_wrt_atyp_mutual :
(forall b1 X1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  X1 `notin` ftv_in_abind b1 ->
  close_abind_wrt_atyp_rec n1 X1 b1 = b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_abind_wrt_atyp_rec_degree_abind_wrt_atyp :
forall b1 X1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  X1 `notin` ftv_in_abind b1 ->
  close_abind_wrt_atyp_rec n1 X1 b1 = b1.
Proof.
pose proof close_abind_wrt_atyp_rec_degree_abind_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_abind_wrt_atyp_rec_degree_abind_wrt_atyp : lngen.
#[export] Hint Rewrite close_abind_wrt_atyp_rec_degree_abind_wrt_atyp using solve [auto] : lngen.

(* end hide *)

Lemma close_atyp_wrt_atyp_lc_atyp :
forall A1 X1,
  lc_atyp A1 ->
  X1 `notin` ftv_in_atyp A1 ->
  close_atyp_wrt_atyp X1 A1 = A1.
Proof.
unfold close_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_atyp_wrt_atyp_lc_atyp : lngen.
#[export] Hint Rewrite close_atyp_wrt_atyp_lc_atyp using solve [auto] : lngen.

Lemma close_abody_wrt_atyp_lc_abody :
forall abody1 X1,
  lc_abody abody1 ->
  X1 `notin` ftv_in_abody abody1 ->
  close_abody_wrt_atyp X1 abody1 = abody1.
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_abody_wrt_atyp_lc_abody : lngen.
#[export] Hint Rewrite close_abody_wrt_atyp_lc_abody using solve [auto] : lngen.

Lemma close_aexp_wrt_atyp_lc_aexp :
forall e1 X1,
  lc_aexp e1 ->
  X1 `notin` ftv_in_aexp e1 ->
  close_aexp_wrt_atyp X1 e1 = e1.
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_aexp_wrt_atyp_lc_aexp : lngen.
#[export] Hint Rewrite close_aexp_wrt_atyp_lc_aexp using solve [auto] : lngen.

Lemma close_abody_wrt_aexp_lc_abody :
forall abody1 x1,
  lc_abody abody1 ->
  x1 `notin` fv_in_abody abody1 ->
  close_abody_wrt_aexp x1 abody1 = abody1.
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve close_abody_wrt_aexp_lc_abody : lngen.
#[export] Hint Rewrite close_abody_wrt_aexp_lc_abody using solve [auto] : lngen.

Lemma close_aexp_wrt_aexp_lc_aexp :
forall e1 x1,
  lc_aexp e1 ->
  x1 `notin` fv_in_aexp e1 ->
  close_aexp_wrt_aexp x1 e1 = e1.
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve close_aexp_wrt_aexp_lc_aexp : lngen.
#[export] Hint Rewrite close_aexp_wrt_aexp_lc_aexp using solve [auto] : lngen.

Lemma close_abind_wrt_atyp_lc_abind :
forall b1 X1,
  lc_abind b1 ->
  X1 `notin` ftv_in_abind b1 ->
  close_abind_wrt_atyp X1 b1 = b1.
Proof.
unfold close_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve close_abind_wrt_atyp_lc_abind : lngen.
#[export] Hint Rewrite close_abind_wrt_atyp_lc_abind using solve [auto] : lngen.

(* begin hide *)

Lemma open_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp_mutual :
(forall A2 A1 n1,
  degree_atyp_wrt_atyp n1 A2 ->
  open_atyp_wrt_atyp_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp :
forall A2 A1 n1,
  degree_atyp_wrt_atyp n1 A2 ->
  open_atyp_wrt_atyp_rec n1 A1 A2 = A2.
Proof.
pose proof open_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp : lngen.
#[export] Hint Rewrite open_atyp_wrt_atyp_rec_degree_atyp_wrt_atyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_atyp_rec_degree_abody_wrt_atyp_open_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp_mutual :
(forall abody1 A1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  open_abody_wrt_atyp_rec n1 A1 abody1 = abody1) /\
(forall e1 A1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  open_aexp_wrt_atyp_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_atyp_rec_degree_abody_wrt_atyp :
forall abody1 A1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  open_abody_wrt_atyp_rec n1 A1 abody1 = abody1.
Proof.
pose proof open_abody_wrt_atyp_rec_degree_abody_wrt_atyp_open_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abody_wrt_atyp_rec_degree_abody_wrt_atyp : lngen.
#[export] Hint Rewrite open_abody_wrt_atyp_rec_degree_abody_wrt_atyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp :
forall e1 A1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  open_aexp_wrt_atyp_rec n1 A1 e1 = e1.
Proof.
pose proof open_abody_wrt_atyp_rec_degree_abody_wrt_atyp_open_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite open_aexp_wrt_atyp_rec_degree_aexp_wrt_atyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexp_rec_degree_abody_wrt_aexp_open_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp_mutual :
(forall abody1 e1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  open_abody_wrt_aexp_rec n1 e1 abody1 = abody1) /\
(forall e2 e1 n1,
  degree_aexp_wrt_aexp n1 e2 ->
  open_aexp_wrt_aexp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abody_wrt_aexp_rec_degree_abody_wrt_aexp :
forall abody1 e1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  open_abody_wrt_aexp_rec n1 e1 abody1 = abody1.
Proof.
pose proof open_abody_wrt_aexp_rec_degree_abody_wrt_aexp_open_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abody_wrt_aexp_rec_degree_abody_wrt_aexp : lngen.
#[export] Hint Rewrite open_abody_wrt_aexp_rec_degree_abody_wrt_aexp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp :
forall e2 e1 n1,
  degree_aexp_wrt_aexp n1 e2 ->
  open_aexp_wrt_aexp_rec n1 e1 e2 = e2.
Proof.
pose proof open_abody_wrt_aexp_rec_degree_abody_wrt_aexp_open_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite open_aexp_wrt_aexp_rec_degree_aexp_wrt_aexp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_atyp_rec_degree_abind_wrt_atyp_mutual :
(forall b1 A1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  open_abind_wrt_atyp_rec n1 A1 b1 = b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_abind_wrt_atyp_rec_degree_abind_wrt_atyp :
forall b1 A1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  open_abind_wrt_atyp_rec n1 A1 b1 = b1.
Proof.
pose proof open_abind_wrt_atyp_rec_degree_abind_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_abind_wrt_atyp_rec_degree_abind_wrt_atyp : lngen.
#[export] Hint Rewrite open_abind_wrt_atyp_rec_degree_abind_wrt_atyp using solve [auto] : lngen.

(* end hide *)

Lemma open_atyp_wrt_atyp_lc_atyp :
forall A2 A1,
  lc_atyp A2 ->
  open_atyp_wrt_atyp A2 A1 = A2.
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_atyp_wrt_atyp_lc_atyp : lngen.
#[export] Hint Rewrite open_atyp_wrt_atyp_lc_atyp using solve [auto] : lngen.

Lemma open_abody_wrt_atyp_lc_abody :
forall abody1 A1,
  lc_abody abody1 ->
  open_abody_wrt_atyp abody1 A1 = abody1.
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_abody_wrt_atyp_lc_abody : lngen.
#[export] Hint Rewrite open_abody_wrt_atyp_lc_abody using solve [auto] : lngen.

Lemma open_aexp_wrt_atyp_lc_aexp :
forall e1 A1,
  lc_aexp e1 ->
  open_aexp_wrt_atyp e1 A1 = e1.
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_aexp_wrt_atyp_lc_aexp : lngen.
#[export] Hint Rewrite open_aexp_wrt_atyp_lc_aexp using solve [auto] : lngen.

Lemma open_abody_wrt_aexp_lc_abody :
forall abody1 e1,
  lc_abody abody1 ->
  open_abody_wrt_aexp abody1 e1 = abody1.
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve open_abody_wrt_aexp_lc_abody : lngen.
#[export] Hint Rewrite open_abody_wrt_aexp_lc_abody using solve [auto] : lngen.

Lemma open_aexp_wrt_aexp_lc_aexp :
forall e2 e1,
  lc_aexp e2 ->
  open_aexp_wrt_aexp e2 e1 = e2.
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve open_aexp_wrt_aexp_lc_aexp : lngen.
#[export] Hint Rewrite open_aexp_wrt_aexp_lc_aexp using solve [auto] : lngen.

Lemma open_abind_wrt_atyp_lc_abind :
forall b1 A1,
  lc_abind b1 ->
  open_abind_wrt_atyp b1 A1 = b1.
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve open_abind_wrt_atyp_lc_abind : lngen.
#[export] Hint Rewrite open_abind_wrt_atyp_lc_abind using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftv_in_atyp_close_atyp_wrt_atyp_rec_mutual :
(forall A1 X1 n1,
  ftv_in_atyp (close_atyp_wrt_atyp_rec n1 X1 A1) [=] remove X1 (ftv_in_atyp A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_atyp_close_atyp_wrt_atyp_rec :
forall A1 X1 n1,
  ftv_in_atyp (close_atyp_wrt_atyp_rec n1 X1 A1) [=] remove X1 (ftv_in_atyp A1).
Proof.
pose proof ftv_in_atyp_close_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_close_atyp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite ftv_in_atyp_close_atyp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_close_abody_wrt_atyp_rec_ftv_in_aexp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1,
  ftv_in_abody (close_abody_wrt_atyp_rec n1 X1 abody1) [=] remove X1 (ftv_in_abody abody1)) /\
(forall e1 X1 n1,
  ftv_in_aexp (close_aexp_wrt_atyp_rec n1 X1 e1) [=] remove X1 (ftv_in_aexp e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_close_abody_wrt_atyp_rec :
forall abody1 X1 n1,
  ftv_in_abody (close_abody_wrt_atyp_rec n1 X1 abody1) [=] remove X1 (ftv_in_abody abody1).
Proof.
pose proof ftv_in_abody_close_abody_wrt_atyp_rec_ftv_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_close_abody_wrt_atyp_rec : lngen.
#[export] Hint Rewrite ftv_in_abody_close_abody_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_aexp_close_aexp_wrt_atyp_rec :
forall e1 X1 n1,
  ftv_in_aexp (close_aexp_wrt_atyp_rec n1 X1 e1) [=] remove X1 (ftv_in_aexp e1).
Proof.
pose proof ftv_in_abody_close_abody_wrt_atyp_rec_ftv_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_close_aexp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite ftv_in_aexp_close_aexp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_close_abody_wrt_aexp_rec_ftv_in_aexp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1,
  ftv_in_abody (close_abody_wrt_aexp_rec n1 x1 abody1) [=] ftv_in_abody abody1) /\
(forall e1 x1 n1,
  ftv_in_aexp (close_aexp_wrt_aexp_rec n1 x1 e1) [=] ftv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_close_abody_wrt_aexp_rec :
forall abody1 x1 n1,
  ftv_in_abody (close_abody_wrt_aexp_rec n1 x1 abody1) [=] ftv_in_abody abody1.
Proof.
pose proof ftv_in_abody_close_abody_wrt_aexp_rec_ftv_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_close_abody_wrt_aexp_rec : lngen.
#[export] Hint Rewrite ftv_in_abody_close_abody_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_aexp_close_aexp_wrt_aexp_rec :
forall e1 x1 n1,
  ftv_in_aexp (close_aexp_wrt_aexp_rec n1 x1 e1) [=] ftv_in_aexp e1.
Proof.
pose proof ftv_in_abody_close_abody_wrt_aexp_rec_ftv_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_close_aexp_wrt_aexp_rec : lngen.
#[export] Hint Rewrite ftv_in_aexp_close_aexp_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_close_abody_wrt_atyp_rec_fv_in_aexp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 X1 n1,
  fv_in_abody (close_abody_wrt_atyp_rec n1 X1 abody1) [=] fv_in_abody abody1) /\
(forall e1 X1 n1,
  fv_in_aexp (close_aexp_wrt_atyp_rec n1 X1 e1) [=] fv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_close_abody_wrt_atyp_rec :
forall abody1 X1 n1,
  fv_in_abody (close_abody_wrt_atyp_rec n1 X1 abody1) [=] fv_in_abody abody1.
Proof.
pose proof fv_in_abody_close_abody_wrt_atyp_rec_fv_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_close_abody_wrt_atyp_rec : lngen.
#[export] Hint Rewrite fv_in_abody_close_abody_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_aexp_close_aexp_wrt_atyp_rec :
forall e1 X1 n1,
  fv_in_aexp (close_aexp_wrt_atyp_rec n1 X1 e1) [=] fv_in_aexp e1.
Proof.
pose proof fv_in_abody_close_abody_wrt_atyp_rec_fv_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_close_aexp_wrt_atyp_rec : lngen.
#[export] Hint Rewrite fv_in_aexp_close_aexp_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_close_abody_wrt_aexp_rec_fv_in_aexp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 x1 n1,
  fv_in_abody (close_abody_wrt_aexp_rec n1 x1 abody1) [=] remove x1 (fv_in_abody abody1)) /\
(forall e1 x1 n1,
  fv_in_aexp (close_aexp_wrt_aexp_rec n1 x1 e1) [=] remove x1 (fv_in_aexp e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_close_abody_wrt_aexp_rec :
forall abody1 x1 n1,
  fv_in_abody (close_abody_wrt_aexp_rec n1 x1 abody1) [=] remove x1 (fv_in_abody abody1).
Proof.
pose proof fv_in_abody_close_abody_wrt_aexp_rec_fv_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_close_abody_wrt_aexp_rec : lngen.
#[export] Hint Rewrite fv_in_abody_close_abody_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_aexp_close_aexp_wrt_aexp_rec :
forall e1 x1 n1,
  fv_in_aexp (close_aexp_wrt_aexp_rec n1 x1 e1) [=] remove x1 (fv_in_aexp e1).
Proof.
pose proof fv_in_abody_close_abody_wrt_aexp_rec_fv_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_close_aexp_wrt_aexp_rec : lngen.
#[export] Hint Rewrite fv_in_aexp_close_aexp_wrt_aexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abind_close_abind_wrt_atyp_rec_mutual :
(forall b1 X1 n1,
  ftv_in_abind (close_abind_wrt_atyp_rec n1 X1 b1) [=] remove X1 (ftv_in_abind b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abind_close_abind_wrt_atyp_rec :
forall b1 X1 n1,
  ftv_in_abind (close_abind_wrt_atyp_rec n1 X1 b1) [=] remove X1 (ftv_in_abind b1).
Proof.
pose proof ftv_in_abind_close_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_close_abind_wrt_atyp_rec : lngen.
#[export] Hint Rewrite ftv_in_abind_close_abind_wrt_atyp_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftv_in_atyp_close_atyp_wrt_atyp :
forall A1 X1,
  ftv_in_atyp (close_atyp_wrt_atyp X1 A1) [=] remove X1 (ftv_in_atyp A1).
Proof.
unfold close_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_atyp_close_atyp_wrt_atyp : lngen.
#[export] Hint Rewrite ftv_in_atyp_close_atyp_wrt_atyp using solve [auto] : lngen.

Lemma ftv_in_abody_close_abody_wrt_atyp :
forall abody1 X1,
  ftv_in_abody (close_abody_wrt_atyp X1 abody1) [=] remove X1 (ftv_in_abody abody1).
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abody_close_abody_wrt_atyp : lngen.
#[export] Hint Rewrite ftv_in_abody_close_abody_wrt_atyp using solve [auto] : lngen.

Lemma ftv_in_aexp_close_aexp_wrt_atyp :
forall e1 X1,
  ftv_in_aexp (close_aexp_wrt_atyp X1 e1) [=] remove X1 (ftv_in_aexp e1).
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_aexp_close_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite ftv_in_aexp_close_aexp_wrt_atyp using solve [auto] : lngen.

Lemma ftv_in_abody_close_abody_wrt_aexp :
forall abody1 x1,
  ftv_in_abody (close_abody_wrt_aexp x1 abody1) [=] ftv_in_abody abody1.
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abody_close_abody_wrt_aexp : lngen.
#[export] Hint Rewrite ftv_in_abody_close_abody_wrt_aexp using solve [auto] : lngen.

Lemma ftv_in_aexp_close_aexp_wrt_aexp :
forall e1 x1,
  ftv_in_aexp (close_aexp_wrt_aexp x1 e1) [=] ftv_in_aexp e1.
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_aexp_close_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite ftv_in_aexp_close_aexp_wrt_aexp using solve [auto] : lngen.

Lemma fv_in_abody_close_abody_wrt_atyp :
forall abody1 X1,
  fv_in_abody (close_abody_wrt_atyp X1 abody1) [=] fv_in_abody abody1.
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_abody_close_abody_wrt_atyp : lngen.
#[export] Hint Rewrite fv_in_abody_close_abody_wrt_atyp using solve [auto] : lngen.

Lemma fv_in_aexp_close_aexp_wrt_atyp :
forall e1 X1,
  fv_in_aexp (close_aexp_wrt_atyp X1 e1) [=] fv_in_aexp e1.
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_aexp_close_aexp_wrt_atyp : lngen.
#[export] Hint Rewrite fv_in_aexp_close_aexp_wrt_atyp using solve [auto] : lngen.

Lemma fv_in_abody_close_abody_wrt_aexp :
forall abody1 x1,
  fv_in_abody (close_abody_wrt_aexp x1 abody1) [=] remove x1 (fv_in_abody abody1).
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_abody_close_abody_wrt_aexp : lngen.
#[export] Hint Rewrite fv_in_abody_close_abody_wrt_aexp using solve [auto] : lngen.

Lemma fv_in_aexp_close_aexp_wrt_aexp :
forall e1 x1,
  fv_in_aexp (close_aexp_wrt_aexp x1 e1) [=] remove x1 (fv_in_aexp e1).
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_aexp_close_aexp_wrt_aexp : lngen.
#[export] Hint Rewrite fv_in_aexp_close_aexp_wrt_aexp using solve [auto] : lngen.

Lemma ftv_in_abind_close_abind_wrt_atyp :
forall b1 X1,
  ftv_in_abind (close_abind_wrt_atyp X1 b1) [=] remove X1 (ftv_in_abind b1).
Proof.
unfold close_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abind_close_abind_wrt_atyp : lngen.
#[export] Hint Rewrite ftv_in_abind_close_abind_wrt_atyp using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_atyp_open_atyp_wrt_atyp_rec_lower_mutual :
(forall A1 A2 n1,
  ftv_in_atyp A1 [<=] ftv_in_atyp (open_atyp_wrt_atyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_atyp_open_atyp_wrt_atyp_rec_lower :
forall A1 A2 n1,
  ftv_in_atyp A1 [<=] ftv_in_atyp (open_atyp_wrt_atyp_rec n1 A2 A1).
Proof.
pose proof ftv_in_atyp_open_atyp_wrt_atyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_open_atyp_wrt_atyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_atyp_rec_lower_ftv_in_aexp_open_aexp_wrt_atyp_rec_lower_mutual :
(forall abody1 A1 n1,
  ftv_in_abody abody1 [<=] ftv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1)) /\
(forall e1 A1 n1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_atyp_rec_lower :
forall abody1 A1 n1,
  ftv_in_abody abody1 [<=] ftv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1).
Proof.
pose proof ftv_in_abody_open_abody_wrt_atyp_rec_lower_ftv_in_aexp_open_aexp_wrt_atyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_atyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_aexp_open_aexp_wrt_atyp_rec_lower :
forall e1 A1 n1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1).
Proof.
pose proof ftv_in_abody_open_abody_wrt_atyp_rec_lower_ftv_in_aexp_open_aexp_wrt_atyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_atyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_aexp_rec_lower_ftv_in_aexp_open_aexp_wrt_aexp_rec_lower_mutual :
(forall abody1 e1 n1,
  ftv_in_abody abody1 [<=] ftv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1)) /\
(forall e1 e2 n1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_aexp_rec_lower :
forall abody1 e1 n1,
  ftv_in_abody abody1 [<=] ftv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1).
Proof.
pose proof ftv_in_abody_open_abody_wrt_aexp_rec_lower_ftv_in_aexp_open_aexp_wrt_aexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_aexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_aexp_open_aexp_wrt_aexp_rec_lower :
forall e1 e2 n1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1).
Proof.
pose proof ftv_in_abody_open_abody_wrt_aexp_rec_lower_ftv_in_aexp_open_aexp_wrt_aexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_aexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_atyp_rec_lower_fv_in_aexp_open_aexp_wrt_atyp_rec_lower_mutual :
(forall abody1 A1 n1,
  fv_in_abody abody1 [<=] fv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1)) /\
(forall e1 A1 n1,
  fv_in_aexp e1 [<=] fv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_atyp_rec_lower :
forall abody1 A1 n1,
  fv_in_abody abody1 [<=] fv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1).
Proof.
pose proof fv_in_abody_open_abody_wrt_atyp_rec_lower_fv_in_aexp_open_aexp_wrt_atyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_atyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_aexp_open_aexp_wrt_atyp_rec_lower :
forall e1 A1 n1,
  fv_in_aexp e1 [<=] fv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1).
Proof.
pose proof fv_in_abody_open_abody_wrt_atyp_rec_lower_fv_in_aexp_open_aexp_wrt_atyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_atyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_aexp_rec_lower_fv_in_aexp_open_aexp_wrt_aexp_rec_lower_mutual :
(forall abody1 e1 n1,
  fv_in_abody abody1 [<=] fv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1)) /\
(forall e1 e2 n1,
  fv_in_aexp e1 [<=] fv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_aexp_rec_lower :
forall abody1 e1 n1,
  fv_in_abody abody1 [<=] fv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1).
Proof.
pose proof fv_in_abody_open_abody_wrt_aexp_rec_lower_fv_in_aexp_open_aexp_wrt_aexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_aexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_aexp_open_aexp_wrt_aexp_rec_lower :
forall e1 e2 n1,
  fv_in_aexp e1 [<=] fv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1).
Proof.
pose proof fv_in_abody_open_abody_wrt_aexp_rec_lower_fv_in_aexp_open_aexp_wrt_aexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_aexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abind_open_abind_wrt_atyp_rec_lower_mutual :
(forall b1 A1 n1,
  ftv_in_abind b1 [<=] ftv_in_abind (open_abind_wrt_atyp_rec n1 A1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abind_open_abind_wrt_atyp_rec_lower :
forall b1 A1 n1,
  ftv_in_abind b1 [<=] ftv_in_abind (open_abind_wrt_atyp_rec n1 A1 b1).
Proof.
pose proof ftv_in_abind_open_abind_wrt_atyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_open_abind_wrt_atyp_rec_lower : lngen.

(* end hide *)

Lemma ftv_in_atyp_open_atyp_wrt_atyp_lower :
forall A1 A2,
  ftv_in_atyp A1 [<=] ftv_in_atyp (open_atyp_wrt_atyp A1 A2).
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_atyp_open_atyp_wrt_atyp_lower : lngen.

Lemma ftv_in_abody_open_abody_wrt_atyp_lower :
forall abody1 A1,
  ftv_in_abody abody1 [<=] ftv_in_abody (open_abody_wrt_atyp abody1 A1).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_atyp_lower : lngen.

Lemma ftv_in_aexp_open_aexp_wrt_atyp_lower :
forall e1 A1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (open_aexp_wrt_atyp e1 A1).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_atyp_lower : lngen.

Lemma ftv_in_abody_open_abody_wrt_aexp_lower :
forall abody1 e1,
  ftv_in_abody abody1 [<=] ftv_in_abody (open_abody_wrt_aexp abody1 e1).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_aexp_lower : lngen.

Lemma ftv_in_aexp_open_aexp_wrt_aexp_lower :
forall e1 e2,
  ftv_in_aexp e1 [<=] ftv_in_aexp (open_aexp_wrt_aexp e1 e2).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_aexp_lower : lngen.

Lemma fv_in_abody_open_abody_wrt_atyp_lower :
forall abody1 A1,
  fv_in_abody abody1 [<=] fv_in_abody (open_abody_wrt_atyp abody1 A1).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_atyp_lower : lngen.

Lemma fv_in_aexp_open_aexp_wrt_atyp_lower :
forall e1 A1,
  fv_in_aexp e1 [<=] fv_in_aexp (open_aexp_wrt_atyp e1 A1).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_atyp_lower : lngen.

Lemma fv_in_abody_open_abody_wrt_aexp_lower :
forall abody1 e1,
  fv_in_abody abody1 [<=] fv_in_abody (open_abody_wrt_aexp abody1 e1).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_aexp_lower : lngen.

Lemma fv_in_aexp_open_aexp_wrt_aexp_lower :
forall e1 e2,
  fv_in_aexp e1 [<=] fv_in_aexp (open_aexp_wrt_aexp e1 e2).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_aexp_lower : lngen.

Lemma ftv_in_abind_open_abind_wrt_atyp_lower :
forall b1 A1,
  ftv_in_abind b1 [<=] ftv_in_abind (open_abind_wrt_atyp b1 A1).
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abind_open_abind_wrt_atyp_lower : lngen.

(* begin hide *)

Lemma ftv_in_atyp_open_atyp_wrt_atyp_rec_upper_mutual :
(forall A1 A2 n1,
  ftv_in_atyp (open_atyp_wrt_atyp_rec n1 A2 A1) [<=] ftv_in_atyp A2 `union` ftv_in_atyp A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_atyp_open_atyp_wrt_atyp_rec_upper :
forall A1 A2 n1,
  ftv_in_atyp (open_atyp_wrt_atyp_rec n1 A2 A1) [<=] ftv_in_atyp A2 `union` ftv_in_atyp A1.
Proof.
pose proof ftv_in_atyp_open_atyp_wrt_atyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_open_atyp_wrt_atyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_atyp_rec_upper_ftv_in_aexp_open_aexp_wrt_atyp_rec_upper_mutual :
(forall abody1 A1 n1,
  ftv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1) [<=] ftv_in_atyp A1 `union` ftv_in_abody abody1) /\
(forall e1 A1 n1,
  ftv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1) [<=] ftv_in_atyp A1 `union` ftv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_atyp_rec_upper :
forall abody1 A1 n1,
  ftv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1) [<=] ftv_in_atyp A1 `union` ftv_in_abody abody1.
Proof.
pose proof ftv_in_abody_open_abody_wrt_atyp_rec_upper_ftv_in_aexp_open_aexp_wrt_atyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_atyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_aexp_open_aexp_wrt_atyp_rec_upper :
forall e1 A1 n1,
  ftv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1) [<=] ftv_in_atyp A1 `union` ftv_in_aexp e1.
Proof.
pose proof ftv_in_abody_open_abody_wrt_atyp_rec_upper_ftv_in_aexp_open_aexp_wrt_atyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_atyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_aexp_rec_upper_ftv_in_aexp_open_aexp_wrt_aexp_rec_upper_mutual :
(forall abody1 e1 n1,
  ftv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1) [<=] ftv_in_aexp e1 `union` ftv_in_abody abody1) /\
(forall e1 e2 n1,
  ftv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1) [<=] ftv_in_aexp e2 `union` ftv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abody_open_abody_wrt_aexp_rec_upper :
forall abody1 e1 n1,
  ftv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1) [<=] ftv_in_aexp e1 `union` ftv_in_abody abody1.
Proof.
pose proof ftv_in_abody_open_abody_wrt_aexp_rec_upper_ftv_in_aexp_open_aexp_wrt_aexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_aexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_aexp_open_aexp_wrt_aexp_rec_upper :
forall e1 e2 n1,
  ftv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1) [<=] ftv_in_aexp e2 `union` ftv_in_aexp e1.
Proof.
pose proof ftv_in_abody_open_abody_wrt_aexp_rec_upper_ftv_in_aexp_open_aexp_wrt_aexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_aexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_atyp_rec_upper_fv_in_aexp_open_aexp_wrt_atyp_rec_upper_mutual :
(forall abody1 A1 n1,
  fv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1) [<=] fv_in_abody abody1) /\
(forall e1 A1 n1,
  fv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1) [<=] fv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_atyp_rec_upper :
forall abody1 A1 n1,
  fv_in_abody (open_abody_wrt_atyp_rec n1 A1 abody1) [<=] fv_in_abody abody1.
Proof.
pose proof fv_in_abody_open_abody_wrt_atyp_rec_upper_fv_in_aexp_open_aexp_wrt_atyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_atyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_aexp_open_aexp_wrt_atyp_rec_upper :
forall e1 A1 n1,
  fv_in_aexp (open_aexp_wrt_atyp_rec n1 A1 e1) [<=] fv_in_aexp e1.
Proof.
pose proof fv_in_abody_open_abody_wrt_atyp_rec_upper_fv_in_aexp_open_aexp_wrt_atyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_atyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_aexp_rec_upper_fv_in_aexp_open_aexp_wrt_aexp_rec_upper_mutual :
(forall abody1 e1 n1,
  fv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1) [<=] fv_in_aexp e1 `union` fv_in_abody abody1) /\
(forall e1 e2 n1,
  fv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1) [<=] fv_in_aexp e2 `union` fv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_abody_open_abody_wrt_aexp_rec_upper :
forall abody1 e1 n1,
  fv_in_abody (open_abody_wrt_aexp_rec n1 e1 abody1) [<=] fv_in_aexp e1 `union` fv_in_abody abody1.
Proof.
pose proof fv_in_abody_open_abody_wrt_aexp_rec_upper_fv_in_aexp_open_aexp_wrt_aexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_aexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_aexp_open_aexp_wrt_aexp_rec_upper :
forall e1 e2 n1,
  fv_in_aexp (open_aexp_wrt_aexp_rec n1 e2 e1) [<=] fv_in_aexp e2 `union` fv_in_aexp e1.
Proof.
pose proof fv_in_abody_open_abody_wrt_aexp_rec_upper_fv_in_aexp_open_aexp_wrt_aexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_aexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abind_open_abind_wrt_atyp_rec_upper_mutual :
(forall b1 A1 n1,
  ftv_in_abind (open_abind_wrt_atyp_rec n1 A1 b1) [<=] ftv_in_atyp A1 `union` ftv_in_abind b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_abind_open_abind_wrt_atyp_rec_upper :
forall b1 A1 n1,
  ftv_in_abind (open_abind_wrt_atyp_rec n1 A1 b1) [<=] ftv_in_atyp A1 `union` ftv_in_abind b1.
Proof.
pose proof ftv_in_abind_open_abind_wrt_atyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_open_abind_wrt_atyp_rec_upper : lngen.

(* end hide *)

Lemma ftv_in_atyp_open_atyp_wrt_atyp_upper :
forall A1 A2,
  ftv_in_atyp (open_atyp_wrt_atyp A1 A2) [<=] ftv_in_atyp A2 `union` ftv_in_atyp A1.
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_atyp_open_atyp_wrt_atyp_upper : lngen.

Lemma ftv_in_abody_open_abody_wrt_atyp_upper :
forall abody1 A1,
  ftv_in_abody (open_abody_wrt_atyp abody1 A1) [<=] ftv_in_atyp A1 `union` ftv_in_abody abody1.
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_atyp_upper : lngen.

Lemma ftv_in_aexp_open_aexp_wrt_atyp_upper :
forall e1 A1,
  ftv_in_aexp (open_aexp_wrt_atyp e1 A1) [<=] ftv_in_atyp A1 `union` ftv_in_aexp e1.
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_atyp_upper : lngen.

Lemma ftv_in_abody_open_abody_wrt_aexp_upper :
forall abody1 e1,
  ftv_in_abody (open_abody_wrt_aexp abody1 e1) [<=] ftv_in_aexp e1 `union` ftv_in_abody abody1.
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abody_open_abody_wrt_aexp_upper : lngen.

Lemma ftv_in_aexp_open_aexp_wrt_aexp_upper :
forall e1 e2,
  ftv_in_aexp (open_aexp_wrt_aexp e1 e2) [<=] ftv_in_aexp e2 `union` ftv_in_aexp e1.
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_aexp_open_aexp_wrt_aexp_upper : lngen.

Lemma fv_in_abody_open_abody_wrt_atyp_upper :
forall abody1 A1,
  fv_in_abody (open_abody_wrt_atyp abody1 A1) [<=] fv_in_abody abody1.
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_atyp_upper : lngen.

Lemma fv_in_aexp_open_aexp_wrt_atyp_upper :
forall e1 A1,
  fv_in_aexp (open_aexp_wrt_atyp e1 A1) [<=] fv_in_aexp e1.
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_atyp_upper : lngen.

Lemma fv_in_abody_open_abody_wrt_aexp_upper :
forall abody1 e1,
  fv_in_abody (open_abody_wrt_aexp abody1 e1) [<=] fv_in_aexp e1 `union` fv_in_abody abody1.
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_abody_open_abody_wrt_aexp_upper : lngen.

Lemma fv_in_aexp_open_aexp_wrt_aexp_upper :
forall e1 e2,
  fv_in_aexp (open_aexp_wrt_aexp e1 e2) [<=] fv_in_aexp e2 `union` fv_in_aexp e1.
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_aexp_open_aexp_wrt_aexp_upper : lngen.

Lemma ftv_in_abind_open_abind_wrt_atyp_upper :
forall b1 A1,
  ftv_in_abind (open_abind_wrt_atyp b1 A1) [<=] ftv_in_atyp A1 `union` ftv_in_abind b1.
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_abind_open_abind_wrt_atyp_upper : lngen.

(* begin hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` ftv_in_atyp A1 ->
  ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1) [=] ftv_in_atyp A1).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_fresh :
forall A1 A2 X1,
  X1 `notin` ftv_in_atyp A1 ->
  ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1) [=] ftv_in_atyp A1.
Proof.
pose proof ftv_in_atyp_a_subst_tv_in_atyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_a_subst_tv_in_atyp_fresh : lngen.
#[export] Hint Rewrite ftv_in_atyp_a_subst_tv_in_atyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_fresh_ftv_in_aexp_a_subst_tv_in_aexp_fresh_mutual :
(forall abody1 A1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [=] ftv_in_abody abody1) /\
(forall e1 A1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [=] ftv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_fresh :
forall abody1 A1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [=] ftv_in_abody abody1.
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_fresh_ftv_in_aexp_a_subst_tv_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_tv_in_abody_fresh : lngen.
#[export] Hint Rewrite ftv_in_abody_a_subst_tv_in_abody_fresh using solve [auto] : lngen.

Lemma ftv_in_aexp_a_subst_tv_in_aexp_fresh :
forall e1 A1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [=] ftv_in_aexp e1.
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_fresh_ftv_in_aexp_a_subst_tv_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_tv_in_aexp_fresh : lngen.
#[export] Hint Rewrite ftv_in_aexp_a_subst_tv_in_aexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_fresh_ftv_in_aexp_a_subst_v_in_aexp_fresh_mutual :
(forall abody1 A1 X1,
  fv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [=] fv_in_abody abody1) /\
(forall e1 A1 X1,
  fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [=] fv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_fresh :
forall abody1 A1 X1,
  fv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [=] fv_in_abody abody1.
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_fresh_ftv_in_aexp_a_subst_v_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_v_in_abody_fresh : lngen.
#[export] Hint Rewrite ftv_in_abody_a_subst_v_in_abody_fresh using solve [auto] : lngen.

Lemma ftv_in_aexp_a_subst_v_in_aexp_fresh :
forall e1 A1 X1,
  fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [=] fv_in_aexp e1.
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_fresh_ftv_in_aexp_a_subst_v_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_v_in_aexp_fresh : lngen.
#[export] Hint Rewrite ftv_in_aexp_a_subst_v_in_aexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_v_in_abody_fresh_fv_in_aexp_a_subst_v_in_aexp_fresh_mutual :
(forall abody1 e1 x1,
  x1 `notin` fv_in_abody abody1 ->
  fv_in_abody (a_subst_v_in_abody e1 x1 abody1) [=] fv_in_abody abody1) /\
(forall e1 e2 x1,
  x1 `notin` fv_in_aexp e1 ->
  fv_in_aexp (a_subst_v_in_aexp e2 x1 e1) [=] fv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_v_in_abody_fresh :
forall abody1 e1 x1,
  x1 `notin` fv_in_abody abody1 ->
  fv_in_abody (a_subst_v_in_abody e1 x1 abody1) [=] fv_in_abody abody1.
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_fresh_fv_in_aexp_a_subst_v_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_v_in_abody_fresh : lngen.
#[export] Hint Rewrite fv_in_abody_a_subst_v_in_abody_fresh using solve [auto] : lngen.

Lemma fv_in_aexp_a_subst_v_in_aexp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_in_aexp e1 ->
  fv_in_aexp (a_subst_v_in_aexp e2 x1 e1) [=] fv_in_aexp e1.
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_fresh_fv_in_aexp_a_subst_v_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_v_in_aexp_fresh : lngen.
#[export] Hint Rewrite fv_in_aexp_a_subst_v_in_aexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_fresh_mutual :
(forall b1 A1 X1,
  X1 `notin` ftv_in_abind b1 ->
  ftv_in_abind (a_subst_tv_in_abind A1 X1 b1) [=] ftv_in_abind b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_fresh :
forall b1 A1 X1,
  X1 `notin` ftv_in_abind b1 ->
  ftv_in_abind (a_subst_tv_in_abind A1 X1 b1) [=] ftv_in_abind b1.
Proof.
pose proof ftv_in_abind_a_subst_tv_in_abind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_a_subst_tv_in_abind_fresh : lngen.
#[export] Hint Rewrite ftv_in_abind_a_subst_tv_in_abind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_lower_mutual :
(forall A1 A2 X1,
  remove X1 (ftv_in_atyp A1) [<=] ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_lower :
forall A1 A2 X1,
  remove X1 (ftv_in_atyp A1) [<=] ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1).
Proof.
pose proof ftv_in_atyp_a_subst_tv_in_atyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_a_subst_tv_in_atyp_lower : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_lower_ftv_in_aexp_a_subst_tv_in_aexp_lower_mutual :
(forall abody1 A1 X1,
  remove X1 (ftv_in_abody abody1) [<=] ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1,
  remove X1 (ftv_in_aexp e1) [<=] ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_lower :
forall abody1 A1 X1,
  remove X1 (ftv_in_abody abody1) [<=] ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_lower_ftv_in_aexp_a_subst_tv_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_tv_in_abody_lower : lngen.

Lemma ftv_in_aexp_a_subst_tv_in_aexp_lower :
forall e1 A1 X1,
  remove X1 (ftv_in_aexp e1) [<=] ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_lower_ftv_in_aexp_a_subst_tv_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_tv_in_aexp_lower : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_lower_ftv_in_aexp_a_subst_v_in_aexp_lower_mutual :
(forall abody1 e1 x1,
  ftv_in_abody abody1 [<=] ftv_in_abody (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 x1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_lower :
forall abody1 e1 x1,
  ftv_in_abody abody1 [<=] ftv_in_abody (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_lower_ftv_in_aexp_a_subst_v_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_v_in_abody_lower : lngen.

Lemma ftv_in_aexp_a_subst_v_in_aexp_lower :
forall e1 e2 x1,
  ftv_in_aexp e1 [<=] ftv_in_aexp (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_lower_ftv_in_aexp_a_subst_v_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_v_in_aexp_lower : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_tv_in_abody_lower_fv_in_aexp_a_subst_tv_in_aexp_lower_mutual :
(forall abody1 A1 X1,
  fv_in_abody abody1 [<=] fv_in_abody (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1,
  fv_in_aexp e1 [<=] fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_tv_in_abody_lower :
forall abody1 A1 X1,
  fv_in_abody abody1 [<=] fv_in_abody (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof fv_in_abody_a_subst_tv_in_abody_lower_fv_in_aexp_a_subst_tv_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_tv_in_abody_lower : lngen.

Lemma fv_in_aexp_a_subst_tv_in_aexp_lower :
forall e1 A1 X1,
  fv_in_aexp e1 [<=] fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof fv_in_abody_a_subst_tv_in_abody_lower_fv_in_aexp_a_subst_tv_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_tv_in_aexp_lower : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_v_in_abody_lower_fv_in_aexp_a_subst_v_in_aexp_lower_mutual :
(forall abody1 e1 x1,
  remove x1 (fv_in_abody abody1) [<=] fv_in_abody (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 x1,
  remove x1 (fv_in_aexp e1) [<=] fv_in_aexp (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_v_in_abody_lower :
forall abody1 e1 x1,
  remove x1 (fv_in_abody abody1) [<=] fv_in_abody (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_lower_fv_in_aexp_a_subst_v_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_v_in_abody_lower : lngen.

Lemma fv_in_aexp_a_subst_v_in_aexp_lower :
forall e1 e2 x1,
  remove x1 (fv_in_aexp e1) [<=] fv_in_aexp (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_lower_fv_in_aexp_a_subst_v_in_aexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_v_in_aexp_lower : lngen.

(* begin hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_lower_mutual :
(forall b1 A1 X1,
  remove X1 (ftv_in_abind b1) [<=] ftv_in_abind (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_lower :
forall b1 A1 X1,
  remove X1 (ftv_in_abind b1) [<=] ftv_in_abind (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof ftv_in_abind_a_subst_tv_in_abind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_a_subst_tv_in_abind_lower : lngen.

(* begin hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_atyp A2 ->
  X2 `notin` ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_notin :
forall A1 A2 X1 X2,
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_atyp A2 ->
  X2 `notin` ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1).
Proof.
pose proof ftv_in_atyp_a_subst_tv_in_atyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_a_subst_tv_in_atyp_notin : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_notin_ftv_in_aexp_a_subst_tv_in_aexp_notin_mutual :
(forall abody1 A1 X1 X2,
  X2 `notin` ftv_in_abody abody1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1 X2,
  X2 `notin` ftv_in_aexp e1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_notin :
forall abody1 A1 X1 X2,
  X2 `notin` ftv_in_abody abody1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_notin_ftv_in_aexp_a_subst_tv_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_tv_in_abody_notin : lngen.

Lemma ftv_in_aexp_a_subst_tv_in_aexp_notin :
forall e1 A1 X1 X2,
  X2 `notin` ftv_in_aexp e1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_notin_ftv_in_aexp_a_subst_tv_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_tv_in_aexp_notin : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_notin_ftv_in_aexp_a_subst_v_in_aexp_notin_mutual :
(forall abody1 e1 x1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_aexp e1 ->
  X1 `notin` ftv_in_abody (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 x1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_notin :
forall abody1 e1 x1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_aexp e1 ->
  X1 `notin` ftv_in_abody (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_notin_ftv_in_aexp_a_subst_v_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_v_in_abody_notin : lngen.

Lemma ftv_in_aexp_a_subst_v_in_aexp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_notin_ftv_in_aexp_a_subst_v_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_v_in_aexp_notin : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_tv_in_abody_notin_fv_in_aexp_a_subst_tv_in_aexp_notin_mutual :
(forall abody1 A1 X1 x1,
  x1 `notin` fv_in_abody abody1 ->
  x1 `notin` fv_in_abody (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1 x1,
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_tv_in_abody_notin :
forall abody1 A1 X1 x1,
  x1 `notin` fv_in_abody abody1 ->
  x1 `notin` fv_in_abody (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof fv_in_abody_a_subst_tv_in_abody_notin_fv_in_aexp_a_subst_tv_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_tv_in_abody_notin : lngen.

Lemma fv_in_aexp_a_subst_tv_in_aexp_notin :
forall e1 A1 X1 x1,
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof fv_in_abody_a_subst_tv_in_abody_notin_fv_in_aexp_a_subst_tv_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_tv_in_aexp_notin : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_v_in_abody_notin_fv_in_aexp_a_subst_v_in_aexp_notin_mutual :
(forall abody1 e1 x1 x2,
  x2 `notin` fv_in_abody abody1 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 `notin` fv_in_abody (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 x1 x2,
  x2 `notin` fv_in_aexp e1 ->
  x2 `notin` fv_in_aexp e2 ->
  x2 `notin` fv_in_aexp (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_v_in_abody_notin :
forall abody1 e1 x1 x2,
  x2 `notin` fv_in_abody abody1 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 `notin` fv_in_abody (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_notin_fv_in_aexp_a_subst_v_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_v_in_abody_notin : lngen.

Lemma fv_in_aexp_a_subst_v_in_aexp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_in_aexp e1 ->
  x2 `notin` fv_in_aexp e2 ->
  x2 `notin` fv_in_aexp (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_notin_fv_in_aexp_a_subst_v_in_aexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_v_in_aexp_notin : lngen.

(* begin hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_notin_mutual :
(forall b1 A1 X1 X2,
  X2 `notin` ftv_in_abind b1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_abind (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_notin :
forall b1 A1 X1 X2,
  X2 `notin` ftv_in_abind b1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 `notin` ftv_in_abind (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof ftv_in_abind_a_subst_tv_in_abind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_a_subst_tv_in_abind_notin : lngen.

(* begin hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_upper_mutual :
(forall A1 A2 X1,
  ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1) [<=] ftv_in_atyp A2 `union` remove X1 (ftv_in_atyp A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_atyp_a_subst_tv_in_atyp_upper :
forall A1 A2 X1,
  ftv_in_atyp (a_subst_tv_in_atyp A2 X1 A1) [<=] ftv_in_atyp A2 `union` remove X1 (ftv_in_atyp A1).
Proof.
pose proof ftv_in_atyp_a_subst_tv_in_atyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_atyp_a_subst_tv_in_atyp_upper : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_upper_ftv_in_aexp_a_subst_tv_in_aexp_upper_mutual :
(forall abody1 A1 X1,
  ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [<=] ftv_in_atyp A1 `union` remove X1 (ftv_in_abody abody1)) /\
(forall e1 A1 X1,
  ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [<=] ftv_in_atyp A1 `union` remove X1 (ftv_in_aexp e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_tv_in_abody_upper :
forall abody1 A1 X1,
  ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [<=] ftv_in_atyp A1 `union` remove X1 (ftv_in_abody abody1).
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_upper_ftv_in_aexp_a_subst_tv_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_tv_in_abody_upper : lngen.

Lemma ftv_in_aexp_a_subst_tv_in_aexp_upper :
forall e1 A1 X1,
  ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [<=] ftv_in_atyp A1 `union` remove X1 (ftv_in_aexp e1).
Proof.
pose proof ftv_in_abody_a_subst_tv_in_abody_upper_ftv_in_aexp_a_subst_tv_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_tv_in_aexp_upper : lngen.

(* begin hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_upper_ftv_in_aexp_a_subst_v_in_aexp_upper_mutual :
(forall abody1 e1 x1,
  ftv_in_abody (a_subst_v_in_abody e1 x1 abody1) [<=] ftv_in_aexp e1 `union` ftv_in_abody abody1) /\
(forall e1 e2 x1,
  ftv_in_aexp (a_subst_v_in_aexp e2 x1 e1) [<=] ftv_in_aexp e2 `union` ftv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abody_a_subst_v_in_abody_upper :
forall abody1 e1 x1,
  ftv_in_abody (a_subst_v_in_abody e1 x1 abody1) [<=] ftv_in_aexp e1 `union` ftv_in_abody abody1.
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_upper_ftv_in_aexp_a_subst_v_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abody_a_subst_v_in_abody_upper : lngen.

Lemma ftv_in_aexp_a_subst_v_in_aexp_upper :
forall e1 e2 x1,
  ftv_in_aexp (a_subst_v_in_aexp e2 x1 e1) [<=] ftv_in_aexp e2 `union` ftv_in_aexp e1.
Proof.
pose proof ftv_in_abody_a_subst_v_in_abody_upper_ftv_in_aexp_a_subst_v_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_aexp_a_subst_v_in_aexp_upper : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_tv_in_abody_upper_fv_in_aexp_a_subst_tv_in_aexp_upper_mutual :
(forall abody1 A1 X1,
  fv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [<=] fv_in_abody abody1) /\
(forall e1 A1 X1,
  fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [<=] fv_in_aexp e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_tv_in_abody_upper :
forall abody1 A1 X1,
  fv_in_abody (a_subst_tv_in_abody A1 X1 abody1) [<=] fv_in_abody abody1.
Proof.
pose proof fv_in_abody_a_subst_tv_in_abody_upper_fv_in_aexp_a_subst_tv_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_tv_in_abody_upper : lngen.

Lemma fv_in_aexp_a_subst_tv_in_aexp_upper :
forall e1 A1 X1,
  fv_in_aexp (a_subst_tv_in_aexp A1 X1 e1) [<=] fv_in_aexp e1.
Proof.
pose proof fv_in_abody_a_subst_tv_in_abody_upper_fv_in_aexp_a_subst_tv_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_tv_in_aexp_upper : lngen.

(* begin hide *)

Lemma fv_in_abody_a_subst_v_in_abody_upper_fv_in_aexp_a_subst_v_in_aexp_upper_mutual :
(forall abody1 e1 x1,
  fv_in_abody (a_subst_v_in_abody e1 x1 abody1) [<=] fv_in_aexp e1 `union` remove x1 (fv_in_abody abody1)) /\
(forall e1 e2 x1,
  fv_in_aexp (a_subst_v_in_aexp e2 x1 e1) [<=] fv_in_aexp e2 `union` remove x1 (fv_in_aexp e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_abody_a_subst_v_in_abody_upper :
forall abody1 e1 x1,
  fv_in_abody (a_subst_v_in_abody e1 x1 abody1) [<=] fv_in_aexp e1 `union` remove x1 (fv_in_abody abody1).
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_upper_fv_in_aexp_a_subst_v_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_abody_a_subst_v_in_abody_upper : lngen.

Lemma fv_in_aexp_a_subst_v_in_aexp_upper :
forall e1 e2 x1,
  fv_in_aexp (a_subst_v_in_aexp e2 x1 e1) [<=] fv_in_aexp e2 `union` remove x1 (fv_in_aexp e1).
Proof.
pose proof fv_in_abody_a_subst_v_in_abody_upper_fv_in_aexp_a_subst_v_in_aexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_aexp_a_subst_v_in_aexp_upper : lngen.

(* begin hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_upper_mutual :
(forall b1 A1 X1,
  ftv_in_abind (a_subst_tv_in_abind A1 X1 b1) [<=] ftv_in_atyp A1 `union` remove X1 (ftv_in_abind b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_abind_a_subst_tv_in_abind_upper :
forall b1 A1 X1,
  ftv_in_abind (a_subst_tv_in_abind A1 X1 b1) [<=] ftv_in_atyp A1 `union` remove X1 (ftv_in_abind b1).
Proof.
pose proof ftv_in_abind_a_subst_tv_in_abind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_abind_a_subst_tv_in_abind_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 (close_atyp_wrt_atyp_rec n1 X2 A2) = close_atyp_wrt_atyp_rec n1 X2 (a_subst_tv_in_atyp A1 X1 A2)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec :
forall A2 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 (close_atyp_wrt_atyp_rec n1 X2 A2) = close_atyp_wrt_atyp_rec n1 X2 (a_subst_tv_in_atyp A1 X1 A2).
Proof.
pose proof a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_atyp_rec_a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_abody A1 X1 (close_abody_wrt_atyp_rec n1 X2 abody1) = close_abody_wrt_atyp_rec n1 X2 (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 (close_aexp_wrt_atyp_rec n1 X2 e1) = close_aexp_wrt_atyp_rec n1 X2 (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_atyp_rec :
forall abody1 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_abody A1 X1 (close_abody_wrt_atyp_rec n1 X2 abody1) = close_abody_wrt_atyp_rec n1 X2 (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_atyp_rec_a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_atyp_rec : lngen.

Lemma a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec :
forall e1 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 (close_aexp_wrt_atyp_rec n1 X2 e1) = close_aexp_wrt_atyp_rec n1 X2 (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_atyp_rec_a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_aexp_rec_a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 A1 x1 X1 n1,
  a_subst_tv_in_abody A1 x1 (close_abody_wrt_aexp_rec n1 X1 abody1) = close_abody_wrt_aexp_rec n1 X1 (a_subst_tv_in_abody A1 x1 abody1)) /\
(forall e1 A1 x1 X1 n1,
  a_subst_tv_in_aexp A1 x1 (close_aexp_wrt_aexp_rec n1 X1 e1) = close_aexp_wrt_aexp_rec n1 X1 (a_subst_tv_in_aexp A1 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_aexp_rec :
forall abody1 A1 x1 X1 n1,
  a_subst_tv_in_abody A1 x1 (close_abody_wrt_aexp_rec n1 X1 abody1) = close_abody_wrt_aexp_rec n1 X1 (a_subst_tv_in_abody A1 x1 abody1).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_aexp_rec_a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_aexp_rec : lngen.

Lemma a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec :
forall e1 A1 x1 X1 n1,
  a_subst_tv_in_aexp A1 x1 (close_aexp_wrt_aexp_rec n1 X1 e1) = close_aexp_wrt_aexp_rec n1 X1 (a_subst_tv_in_aexp A1 x1 e1).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_aexp_rec_a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_atyp_rec_a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_mutual :
(forall abody1 e1 X1 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  x1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_abody e1 X1 (close_abody_wrt_atyp_rec n1 x1 abody1) = close_abody_wrt_atyp_rec n1 x1 (a_subst_v_in_abody e1 X1 abody1)) /\
(forall e2 e1 X1 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  x1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_aexp e1 X1 (close_aexp_wrt_atyp_rec n1 x1 e2) = close_aexp_wrt_atyp_rec n1 x1 (a_subst_v_in_aexp e1 X1 e2)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_atyp_rec :
forall abody1 e1 X1 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  x1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_abody e1 X1 (close_abody_wrt_atyp_rec n1 x1 abody1) = close_abody_wrt_atyp_rec n1 x1 (a_subst_v_in_abody e1 X1 abody1).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_atyp_rec_a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_atyp_rec : lngen.

Lemma a_subst_v_in_aexp_close_aexp_wrt_atyp_rec :
forall e2 e1 X1 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  x1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_aexp e1 X1 (close_aexp_wrt_atyp_rec n1 x1 e2) = close_aexp_wrt_atyp_rec n1 x1 (a_subst_v_in_aexp e1 X1 e2).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_atyp_rec_a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_atyp_rec : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_aexp_rec_a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_mutual :
(forall abody1 e1 x1 x2 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_aexp e1 ->
  a_subst_v_in_abody e1 x1 (close_abody_wrt_aexp_rec n1 x2 abody1) = close_abody_wrt_aexp_rec n1 x2 (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e2 e1 x1 x2 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (close_aexp_wrt_aexp_rec n1 x2 e2) = close_aexp_wrt_aexp_rec n1 x2 (a_subst_v_in_aexp e1 x1 e2)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_aexp_rec :
forall abody1 e1 x1 x2 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_aexp e1 ->
  a_subst_v_in_abody e1 x1 (close_abody_wrt_aexp_rec n1 x2 abody1) = close_abody_wrt_aexp_rec n1 x2 (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_aexp_rec_a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_aexp_rec : lngen.

Lemma a_subst_v_in_aexp_close_aexp_wrt_aexp_rec :
forall e2 e1 x1 x2 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (close_aexp_wrt_aexp_rec n1 x2 e2) = close_aexp_wrt_aexp_rec n1 x2 (a_subst_v_in_aexp e1 x1 e2).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_aexp_rec_a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_aexp_rec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_close_abind_wrt_atyp_rec_mutual :
(forall b1 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_abind A1 X1 (close_abind_wrt_atyp_rec n1 X2 b1) = close_abind_wrt_atyp_rec n1 X2 (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_close_abind_wrt_atyp_rec :
forall b1 A1 X1 X2 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_abind A1 X1 (close_abind_wrt_atyp_rec n1 X2 b1) = close_abind_wrt_atyp_rec n1 X2 (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof a_subst_tv_in_abind_close_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_close_abind_wrt_atyp_rec : lngen.

Lemma a_subst_tv_in_atyp_close_atyp_wrt_atyp :
forall A2 A1 X1 X2,
  lc_atyp A1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 (close_atyp_wrt_atyp X2 A2) = close_atyp_wrt_atyp X2 (a_subst_tv_in_atyp A1 X1 A2).
Proof.
unfold close_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_close_atyp_wrt_atyp : lngen.

Lemma a_subst_tv_in_abody_close_abody_wrt_atyp :
forall abody1 A1 X1 X2,
  lc_atyp A1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_abody A1 X1 (close_abody_wrt_atyp X2 abody1) = close_abody_wrt_atyp X2 (a_subst_tv_in_abody A1 X1 abody1).
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_atyp : lngen.

Lemma a_subst_tv_in_aexp_close_aexp_wrt_atyp :
forall e1 A1 X1 X2,
  lc_atyp A1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 (close_aexp_wrt_atyp X2 e1) = close_aexp_wrt_atyp X2 (a_subst_tv_in_aexp A1 X1 e1).
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_atyp : lngen.

Lemma a_subst_tv_in_abody_close_abody_wrt_aexp :
forall abody1 A1 x1 X1,
  lc_atyp A1 ->  a_subst_tv_in_abody A1 x1 (close_abody_wrt_aexp X1 abody1) = close_abody_wrt_aexp X1 (a_subst_tv_in_abody A1 x1 abody1).
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_aexp : lngen.

Lemma a_subst_tv_in_aexp_close_aexp_wrt_aexp :
forall e1 A1 x1 X1,
  lc_atyp A1 ->  a_subst_tv_in_aexp A1 x1 (close_aexp_wrt_aexp X1 e1) = close_aexp_wrt_aexp X1 (a_subst_tv_in_aexp A1 x1 e1).
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_aexp : lngen.

Lemma a_subst_v_in_abody_close_abody_wrt_atyp :
forall abody1 e1 X1 x1,
  lc_aexp e1 ->  x1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_abody e1 X1 (close_abody_wrt_atyp x1 abody1) = close_abody_wrt_atyp x1 (a_subst_v_in_abody e1 X1 abody1).
Proof.
unfold close_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_atyp : lngen.

Lemma a_subst_v_in_aexp_close_aexp_wrt_atyp :
forall e2 e1 X1 x1,
  lc_aexp e1 ->  x1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_aexp e1 X1 (close_aexp_wrt_atyp x1 e2) = close_aexp_wrt_atyp x1 (a_subst_v_in_aexp e1 X1 e2).
Proof.
unfold close_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_atyp : lngen.

Lemma a_subst_v_in_abody_close_abody_wrt_aexp :
forall abody1 e1 x1 x2,
  lc_aexp e1 ->  x1 <> x2 ->
  x2 `notin` fv_in_aexp e1 ->
  a_subst_v_in_abody e1 x1 (close_abody_wrt_aexp x2 abody1) = close_abody_wrt_aexp x2 (a_subst_v_in_abody e1 x1 abody1).
Proof.
unfold close_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_aexp : lngen.

Lemma a_subst_v_in_aexp_close_aexp_wrt_aexp :
forall e2 e1 x1 x2,
  lc_aexp e1 ->  x1 <> x2 ->
  x2 `notin` fv_in_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (close_aexp_wrt_aexp x2 e2) = close_aexp_wrt_aexp x2 (a_subst_v_in_aexp e1 x1 e2).
Proof.
unfold close_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_aexp : lngen.

Lemma a_subst_tv_in_abind_close_abind_wrt_atyp :
forall b1 A1 X1 X2,
  lc_atyp A1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_atyp A1 ->
  a_subst_tv_in_abind A1 X1 (close_abind_wrt_atyp X2 b1) = close_abind_wrt_atyp X2 (a_subst_tv_in_abind A1 X1 b1).
Proof.
unfold close_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_close_abind_wrt_atyp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_degree_atyp_wrt_atyp_mutual :
(forall A1 A2 X1 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  degree_atyp_wrt_atyp n1 A2 ->
  degree_atyp_wrt_atyp n1 (a_subst_tv_in_atyp A2 X1 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_degree_atyp_wrt_atyp :
forall A1 A2 X1 n1,
  degree_atyp_wrt_atyp n1 A1 ->
  degree_atyp_wrt_atyp n1 A2 ->
  degree_atyp_wrt_atyp n1 (a_subst_tv_in_atyp A2 X1 A1).
Proof.
pose proof a_subst_tv_in_atyp_degree_atyp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_degree_atyp_wrt_atyp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_degree_abody_wrt_atyp_a_subst_tv_in_aexp_degree_aexp_wrt_atyp_mutual :
(forall abody1 A1 X1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abody_wrt_atyp n1 (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_aexp_wrt_atyp n1 (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_degree_abody_wrt_atyp :
forall abody1 A1 X1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abody_wrt_atyp n1 (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_degree_abody_wrt_atyp_a_subst_tv_in_aexp_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_degree_abody_wrt_atyp : lngen.

Lemma a_subst_tv_in_aexp_degree_aexp_wrt_atyp :
forall e1 A1 X1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_aexp_wrt_atyp n1 (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_degree_abody_wrt_atyp_a_subst_tv_in_aexp_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_degree_aexp_wrt_atyp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_degree_abody_wrt_aexp_a_subst_tv_in_aexp_degree_aexp_wrt_aexp_mutual :
(forall abody1 A1 X1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp n1 (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_degree_abody_wrt_aexp :
forall abody1 A1 X1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_abody_wrt_aexp n1 (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_degree_abody_wrt_aexp_a_subst_tv_in_aexp_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_degree_abody_wrt_aexp : lngen.

Lemma a_subst_tv_in_aexp_degree_aexp_wrt_aexp :
forall e1 A1 X1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_degree_abody_wrt_aexp_a_subst_tv_in_aexp_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_degree_aexp_wrt_aexp : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_degree_abody_wrt_atyp_a_subst_v_in_aexp_degree_aexp_wrt_atyp_mutual :
(forall abody1 e1 x1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  degree_abody_wrt_atyp n1 (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp n1 e2 ->
  degree_aexp_wrt_atyp n1 (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_degree_abody_wrt_atyp :
forall abody1 e1 x1 n1,
  degree_abody_wrt_atyp n1 abody1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  degree_abody_wrt_atyp n1 (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_degree_abody_wrt_atyp_a_subst_v_in_aexp_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_degree_abody_wrt_atyp : lngen.

Lemma a_subst_v_in_aexp_degree_aexp_wrt_atyp :
forall e1 e2 x1 n1,
  degree_aexp_wrt_atyp n1 e1 ->
  degree_aexp_wrt_atyp n1 e2 ->
  degree_aexp_wrt_atyp n1 (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof a_subst_v_in_abody_degree_abody_wrt_atyp_a_subst_v_in_aexp_degree_aexp_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_degree_aexp_wrt_atyp : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_degree_abody_wrt_aexp_a_subst_v_in_aexp_degree_aexp_wrt_aexp_mutual :
(forall abody1 e1 x1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  degree_abody_wrt_aexp n1 (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 x1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 e2 ->
  degree_aexp_wrt_aexp n1 (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_degree_abody_wrt_aexp :
forall abody1 e1 x1 n1,
  degree_abody_wrt_aexp n1 abody1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  degree_abody_wrt_aexp n1 (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_degree_abody_wrt_aexp_a_subst_v_in_aexp_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_degree_abody_wrt_aexp : lngen.

Lemma a_subst_v_in_aexp_degree_aexp_wrt_aexp :
forall e1 e2 x1 n1,
  degree_aexp_wrt_aexp n1 e1 ->
  degree_aexp_wrt_aexp n1 e2 ->
  degree_aexp_wrt_aexp n1 (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof a_subst_v_in_abody_degree_abody_wrt_aexp_a_subst_v_in_aexp_degree_aexp_wrt_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_degree_aexp_wrt_aexp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_degree_abind_wrt_atyp_mutual :
(forall b1 A1 X1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abind_wrt_atyp n1 (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_degree_abind_wrt_atyp :
forall b1 A1 X1 n1,
  degree_abind_wrt_atyp n1 b1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  degree_abind_wrt_atyp n1 (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof a_subst_tv_in_abind_degree_abind_wrt_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_degree_abind_wrt_atyp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` ftv_in_atyp A2 ->
  a_subst_tv_in_atyp A1 X1 A2 = A2).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_fresh_eq :
forall A2 A1 X1,
  X1 `notin` ftv_in_atyp A2 ->
  a_subst_tv_in_atyp A1 X1 A2 = A2.
Proof.
pose proof a_subst_tv_in_atyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_atyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_fresh_eq_a_subst_tv_in_aexp_fresh_eq_mutual :
(forall abody1 A1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  a_subst_tv_in_abody A1 X1 abody1 = abody1) /\
(forall e1 A1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  a_subst_tv_in_aexp A1 X1 e1 = e1).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_fresh_eq :
forall abody1 A1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  a_subst_tv_in_abody A1 X1 abody1 = abody1.
Proof.
pose proof a_subst_tv_in_abody_fresh_eq_a_subst_tv_in_aexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_abody_fresh_eq using solve [auto] : lngen.

Lemma a_subst_tv_in_aexp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` ftv_in_aexp e1 ->
  a_subst_tv_in_aexp A1 X1 e1 = e1.
Proof.
pose proof a_subst_tv_in_abody_fresh_eq_a_subst_tv_in_aexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_aexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_fresh_eq_a_subst_v_in_aexp_fresh_eq_mutual :
(forall abody1 e1 x1,
  x1 `notin` fv_in_abody abody1 ->
  a_subst_v_in_abody e1 x1 abody1 = abody1) /\
(forall e2 e1 x1,
  x1 `notin` fv_in_aexp e2 ->
  a_subst_v_in_aexp e1 x1 e2 = e2).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_fresh_eq :
forall abody1 e1 x1,
  x1 `notin` fv_in_abody abody1 ->
  a_subst_v_in_abody e1 x1 abody1 = abody1.
Proof.
pose proof a_subst_v_in_abody_fresh_eq_a_subst_v_in_aexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_v_in_abody_fresh_eq using solve [auto] : lngen.

Lemma a_subst_v_in_aexp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_in_aexp e2 ->
  a_subst_v_in_aexp e1 x1 e2 = e2.
Proof.
pose proof a_subst_v_in_abody_fresh_eq_a_subst_v_in_aexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_v_in_aexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_fresh_eq_mutual :
(forall b1 A1 X1,
  X1 `notin` ftv_in_abind b1 ->
  a_subst_tv_in_abind A1 X1 b1 = b1).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_fresh_eq :
forall b1 A1 X1,
  X1 `notin` ftv_in_abind b1 ->
  a_subst_tv_in_abind A1 X1 b1 = b1.
Proof.
pose proof a_subst_tv_in_abind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_fresh_eq : lngen.
#[export] Hint Rewrite a_subst_tv_in_abind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_atyp (a_subst_tv_in_atyp A1 X1 A2)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_fresh_same :
forall A2 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_atyp (a_subst_tv_in_atyp A1 X1 A2).
Proof.
pose proof a_subst_tv_in_atyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_fresh_same_a_subst_tv_in_aexp_fresh_same_mutual :
(forall abody1 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_fresh_same :
forall abody1 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abody (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_fresh_same_a_subst_tv_in_aexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_fresh_same : lngen.

Lemma a_subst_tv_in_aexp_fresh_same :
forall e1 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_aexp (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_fresh_same_a_subst_tv_in_aexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_fresh_same_a_subst_v_in_aexp_fresh_same_mutual :
(forall abody1 e1 x1,
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_abody (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e2 e1 x1,
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_aexp (a_subst_v_in_aexp e1 x1 e2)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_fresh_same :
forall abody1 e1 x1,
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_abody (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_fresh_same_a_subst_v_in_aexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_fresh_same : lngen.

Lemma a_subst_v_in_aexp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_aexp (a_subst_v_in_aexp e1 x1 e2).
Proof.
pose proof a_subst_v_in_abody_fresh_same_a_subst_v_in_aexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_fresh_same_mutual :
(forall b1 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abind (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_fresh_same :
forall b1 A1 X1,
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abind (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof a_subst_tv_in_abind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_fresh_same : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` ftv_in_atyp A2 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_atyp (a_subst_tv_in_atyp A1 X2 A2)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_fresh :
forall A2 A1 X1 X2,
  X1 `notin` ftv_in_atyp A2 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_atyp (a_subst_tv_in_atyp A1 X2 A2).
Proof.
pose proof a_subst_tv_in_atyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_fresh : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_fresh_a_subst_tv_in_aexp_fresh_mutual :
(forall abody1 A1 X1 X2,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abody (a_subst_tv_in_abody A1 X2 abody1)) /\
(forall e1 A1 X1 X2,
  X1 `notin` ftv_in_aexp e1 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_aexp (a_subst_tv_in_aexp A1 X2 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_fresh :
forall abody1 A1 X1 X2,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abody (a_subst_tv_in_abody A1 X2 abody1).
Proof.
pose proof a_subst_tv_in_abody_fresh_a_subst_tv_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_fresh : lngen.

Lemma a_subst_tv_in_aexp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` ftv_in_aexp e1 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_aexp (a_subst_tv_in_aexp A1 X2 e1).
Proof.
pose proof a_subst_tv_in_abody_fresh_a_subst_tv_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_fresh : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_fresh_a_subst_v_in_aexp_fresh_mutual :
(forall abody1 e1 x1 x2,
  x1 `notin` fv_in_abody abody1 ->
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_abody (a_subst_v_in_abody e1 x2 abody1)) /\
(forall e2 e1 x1 x2,
  x1 `notin` fv_in_aexp e2 ->
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_aexp (a_subst_v_in_aexp e1 x2 e2)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_fresh :
forall abody1 e1 x1 x2,
  x1 `notin` fv_in_abody abody1 ->
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_abody (a_subst_v_in_abody e1 x2 abody1).
Proof.
pose proof a_subst_v_in_abody_fresh_a_subst_v_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_fresh : lngen.

Lemma a_subst_v_in_aexp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_in_aexp e2 ->
  x1 `notin` fv_in_aexp e1 ->
  x1 `notin` fv_in_aexp (a_subst_v_in_aexp e1 x2 e2).
Proof.
pose proof a_subst_v_in_abody_fresh_a_subst_v_in_aexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_fresh : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_fresh_mutual :
(forall b1 A1 X1 X2,
  X1 `notin` ftv_in_abind b1 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abind (a_subst_tv_in_abind A1 X2 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_fresh :
forall b1 A1 X1 X2,
  X1 `notin` ftv_in_abind b1 ->
  X1 `notin` ftv_in_atyp A1 ->
  X1 `notin` ftv_in_abind (a_subst_tv_in_abind A1 X2 b1).
Proof.
pose proof a_subst_tv_in_abind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_fresh : lngen.

Lemma a_subst_tv_in_atyp_lc_atyp :
forall A1 A2 X1,
  lc_atyp A1 ->
  lc_atyp A2 ->
  lc_atyp (a_subst_tv_in_atyp A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_lc_atyp : lngen.

Lemma a_subst_tv_in_abody_lc_abody :
forall abody1 A1 X1,
  lc_abody abody1 ->
  lc_atyp A1 ->
  lc_abody (a_subst_tv_in_abody A1 X1 abody1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_lc_abody : lngen.

Lemma a_subst_tv_in_aexp_lc_aexp :
forall e1 A1 X1,
  lc_aexp e1 ->
  lc_atyp A1 ->
  lc_aexp (a_subst_tv_in_aexp A1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_lc_aexp : lngen.

Lemma a_subst_v_in_abody_lc_abody :
forall abody1 e1 x1,
  lc_abody abody1 ->
  lc_aexp e1 ->
  lc_abody (a_subst_v_in_abody e1 x1 abody1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_lc_abody : lngen.

Lemma a_subst_v_in_aexp_lc_aexp :
forall e1 e2 x1,
  lc_aexp e1 ->
  lc_aexp e2 ->
  lc_aexp (a_subst_v_in_aexp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_lc_aexp : lngen.

Lemma a_subst_tv_in_abind_lc_abind :
forall b1 A1 X1,
  lc_abind b1 ->
  lc_atyp A1 ->
  lc_abind (a_subst_tv_in_abind A1 X1 b1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_lc_abind : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_open_atyp_wrt_atyp_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp_rec n1 A2 A3) = open_atyp_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_atyp A1 X1 A3)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_atyp_open_atyp_wrt_atyp_rec :
forall A3 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp_rec n1 A2 A3) = open_atyp_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_atyp A1 X1 A3).
Proof.
pose proof a_subst_tv_in_atyp_open_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_open_atyp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_open_abody_wrt_atyp_rec_a_subst_tv_in_aexp_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp_rec n1 A2 abody1) = open_abody_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp_rec n1 A2 e1) = open_aexp_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_open_abody_wrt_atyp_rec :
forall abody1 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp_rec n1 A2 abody1) = open_abody_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_open_abody_wrt_atyp_rec_a_subst_tv_in_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_aexp_open_aexp_wrt_atyp_rec :
forall e1 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp_rec n1 A2 e1) = open_aexp_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_open_abody_wrt_atyp_rec_a_subst_tv_in_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_open_abody_wrt_aexp_rec_a_subst_tv_in_aexp_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 A1 e1 X1 n1,
  a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp_rec n1 e1 abody1) = open_abody_wrt_aexp_rec n1 (a_subst_tv_in_aexp A1 X1 e1) (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e2 A1 e1 X1 n1,
  a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp_rec n1 e1 e2) = open_aexp_wrt_aexp_rec n1 (a_subst_tv_in_aexp A1 X1 e1) (a_subst_tv_in_aexp A1 X1 e2)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_open_abody_wrt_aexp_rec :
forall abody1 A1 e1 X1 n1,
  a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp_rec n1 e1 abody1) = open_abody_wrt_aexp_rec n1 (a_subst_tv_in_aexp A1 X1 e1) (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_open_abody_wrt_aexp_rec_a_subst_tv_in_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_aexp_open_aexp_wrt_aexp_rec :
forall e2 A1 e1 X1 n1,
  a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp_rec n1 e1 e2) = open_aexp_wrt_aexp_rec n1 (a_subst_tv_in_aexp A1 X1 e1) (a_subst_tv_in_aexp A1 X1 e2).
Proof.
pose proof a_subst_tv_in_abody_open_abody_wrt_aexp_rec_a_subst_tv_in_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_open_abody_wrt_atyp_rec_a_subst_v_in_aexp_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 e1 A1 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp_rec n1 A1 abody1) = open_abody_wrt_atyp_rec n1 A1 (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e2 e1 A1 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp_rec n1 A1 e2) = open_aexp_wrt_atyp_rec n1 A1 (a_subst_v_in_aexp e1 x1 e2)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_open_abody_wrt_atyp_rec :
forall abody1 e1 A1 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp_rec n1 A1 abody1) = open_abody_wrt_atyp_rec n1 A1 (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_open_abody_wrt_atyp_rec_a_subst_v_in_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_aexp_open_aexp_wrt_atyp_rec :
forall e2 e1 A1 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp_rec n1 A1 e2) = open_aexp_wrt_atyp_rec n1 A1 (a_subst_v_in_aexp e1 x1 e2).
Proof.
pose proof a_subst_v_in_abody_open_abody_wrt_atyp_rec_a_subst_v_in_aexp_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_open_abody_wrt_aexp_rec_a_subst_v_in_aexp_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 e1 e2 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp_rec n1 e2 abody1) = open_abody_wrt_aexp_rec n1 (a_subst_v_in_aexp e1 x1 e2) (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e3 e1 e2 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp_rec n1 e2 e3) = open_aexp_wrt_aexp_rec n1 (a_subst_v_in_aexp e1 x1 e2) (a_subst_v_in_aexp e1 x1 e3)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_open_abody_wrt_aexp_rec :
forall abody1 e1 e2 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp_rec n1 e2 abody1) = open_abody_wrt_aexp_rec n1 (a_subst_v_in_aexp e1 x1 e2) (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_open_abody_wrt_aexp_rec_a_subst_v_in_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_aexp_open_aexp_wrt_aexp_rec :
forall e3 e1 e2 x1 n1,
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp_rec n1 e2 e3) = open_aexp_wrt_aexp_rec n1 (a_subst_v_in_aexp e1 x1 e2) (a_subst_v_in_aexp e1 x1 e3).
Proof.
pose proof a_subst_v_in_abody_open_abody_wrt_aexp_rec_a_subst_v_in_aexp_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abind_open_abind_wrt_atyp_rec_mutual :
(forall b1 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp_rec n1 A2 b1) = open_abind_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abind_open_abind_wrt_atyp_rec :
forall b1 A1 A2 X1 n1,
  lc_atyp A1 ->
  a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp_rec n1 A2 b1) = open_abind_wrt_atyp_rec n1 (a_subst_tv_in_atyp A1 X1 A2) (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof a_subst_tv_in_abind_open_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_open_abind_wrt_atyp_rec : lngen.

(* end hide *)

Lemma a_subst_tv_in_atyp_open_atyp_wrt_atyp :
forall A3 A1 A2 X1,
  lc_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp A3 A2) = open_atyp_wrt_atyp (a_subst_tv_in_atyp A1 X1 A3) (a_subst_tv_in_atyp A1 X1 A2).
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_open_atyp_wrt_atyp : lngen.

Lemma a_subst_tv_in_abody_open_abody_wrt_atyp :
forall abody1 A1 A2 X1,
  lc_atyp A1 ->
  a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp abody1 A2) = open_abody_wrt_atyp (a_subst_tv_in_abody A1 X1 abody1) (a_subst_tv_in_atyp A1 X1 A2).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_open_abody_wrt_atyp : lngen.

Lemma a_subst_tv_in_aexp_open_aexp_wrt_atyp :
forall e1 A1 A2 X1,
  lc_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp e1 A2) = open_aexp_wrt_atyp (a_subst_tv_in_aexp A1 X1 e1) (a_subst_tv_in_atyp A1 X1 A2).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_open_aexp_wrt_atyp : lngen.

Lemma a_subst_tv_in_abody_open_abody_wrt_aexp :
forall abody1 A1 e1 X1,
  a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp abody1 e1) = open_abody_wrt_aexp (a_subst_tv_in_abody A1 X1 abody1) (a_subst_tv_in_aexp A1 X1 e1).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_open_abody_wrt_aexp : lngen.

Lemma a_subst_tv_in_aexp_open_aexp_wrt_aexp :
forall e2 A1 e1 X1,
  a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp e2 e1) = open_aexp_wrt_aexp (a_subst_tv_in_aexp A1 X1 e2) (a_subst_tv_in_aexp A1 X1 e1).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_open_aexp_wrt_aexp : lngen.

Lemma a_subst_v_in_abody_open_abody_wrt_atyp :
forall abody1 e1 A1 x1,
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp abody1 A1) = open_abody_wrt_atyp (a_subst_v_in_abody e1 x1 abody1) A1.
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_open_abody_wrt_atyp : lngen.

Lemma a_subst_v_in_aexp_open_aexp_wrt_atyp :
forall e2 e1 A1 x1,
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp e2 A1) = open_aexp_wrt_atyp (a_subst_v_in_aexp e1 x1 e2) A1.
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_open_aexp_wrt_atyp : lngen.

Lemma a_subst_v_in_abody_open_abody_wrt_aexp :
forall abody1 e1 e2 x1,
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp abody1 e2) = open_abody_wrt_aexp (a_subst_v_in_abody e1 x1 abody1) (a_subst_v_in_aexp e1 x1 e2).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_open_abody_wrt_aexp : lngen.

Lemma a_subst_v_in_aexp_open_aexp_wrt_aexp :
forall e3 e1 e2 x1,
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp e3 e2) = open_aexp_wrt_aexp (a_subst_v_in_aexp e1 x1 e3) (a_subst_v_in_aexp e1 x1 e2).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_open_aexp_wrt_aexp : lngen.

Lemma a_subst_tv_in_abind_open_abind_wrt_atyp :
forall b1 A1 A2 X1,
  lc_atyp A1 ->
  a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp b1 A2) = open_abind_wrt_atyp (a_subst_tv_in_abind A1 X1 b1) (a_subst_tv_in_atyp A1 X1 A2).
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_open_abind_wrt_atyp : lngen.

Lemma a_subst_tv_in_atyp_open_atyp_wrt_atyp_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_atyp A1 ->
  open_atyp_wrt_atyp (a_subst_tv_in_atyp A1 X1 A2) (atyp_tvar_f X2) = a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp A2 (atyp_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_atyp_open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_open_atyp_wrt_atyp_var : lngen.

Lemma a_subst_tv_in_abody_open_abody_wrt_atyp_var :
forall abody1 A1 X1 X2,
  X1 <> X2 ->
  lc_atyp A1 ->
  open_abody_wrt_atyp (a_subst_tv_in_abody A1 X1 abody1) (atyp_tvar_f X2) = a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_abody_open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_open_abody_wrt_atyp_var : lngen.

Lemma a_subst_tv_in_aexp_open_aexp_wrt_atyp_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_atyp A1 ->
  open_aexp_wrt_atyp (a_subst_tv_in_aexp A1 X1 e1) (atyp_tvar_f X2) = a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp e1 (atyp_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_aexp_open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_open_aexp_wrt_atyp_var : lngen.

Lemma a_subst_tv_in_abody_open_abody_wrt_aexp_var :
forall abody1 A1 X1 x1,
  open_abody_wrt_aexp (a_subst_tv_in_abody A1 X1 abody1) (a_exp_var_f x1) = a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp abody1 (a_exp_var_f x1)).
Proof.
intros; rewrite a_subst_tv_in_abody_open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_open_abody_wrt_aexp_var : lngen.

Lemma a_subst_tv_in_aexp_open_aexp_wrt_aexp_var :
forall e1 A1 X1 x1,
  open_aexp_wrt_aexp (a_subst_tv_in_aexp A1 X1 e1) (a_exp_var_f x1) = a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp e1 (a_exp_var_f x1)).
Proof.
intros; rewrite a_subst_tv_in_aexp_open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_open_aexp_wrt_aexp_var : lngen.

Lemma a_subst_v_in_abody_open_abody_wrt_atyp_var :
forall abody1 e1 x1 X1,
  lc_aexp e1 ->
  open_abody_wrt_atyp (a_subst_v_in_abody e1 x1 abody1) (atyp_tvar_f X1) = a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)).
Proof.
intros; rewrite a_subst_v_in_abody_open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_open_abody_wrt_atyp_var : lngen.

Lemma a_subst_v_in_aexp_open_aexp_wrt_atyp_var :
forall e2 e1 x1 X1,
  lc_aexp e1 ->
  open_aexp_wrt_atyp (a_subst_v_in_aexp e1 x1 e2) (atyp_tvar_f X1) = a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp e2 (atyp_tvar_f X1)).
Proof.
intros; rewrite a_subst_v_in_aexp_open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_open_aexp_wrt_atyp_var : lngen.

Lemma a_subst_v_in_abody_open_abody_wrt_aexp_var :
forall abody1 e1 x1 x2,
  x1 <> x2 ->
  lc_aexp e1 ->
  open_abody_wrt_aexp (a_subst_v_in_abody e1 x1 abody1) (a_exp_var_f x2) = a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp abody1 (a_exp_var_f x2)).
Proof.
intros; rewrite a_subst_v_in_abody_open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_open_abody_wrt_aexp_var : lngen.

Lemma a_subst_v_in_aexp_open_aexp_wrt_aexp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_aexp e1 ->
  open_aexp_wrt_aexp (a_subst_v_in_aexp e1 x1 e2) (a_exp_var_f x2) = a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp e2 (a_exp_var_f x2)).
Proof.
intros; rewrite a_subst_v_in_aexp_open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_open_aexp_wrt_aexp_var : lngen.

Lemma a_subst_tv_in_abind_open_abind_wrt_atyp_var :
forall b1 A1 X1 X2,
  X1 <> X2 ->
  lc_atyp A1 ->
  open_abind_wrt_atyp (a_subst_tv_in_abind A1 X1 b1) (atyp_tvar_f X2) = a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp b1 (atyp_tvar_f X2)).
Proof.
intros; rewrite a_subst_tv_in_abind_open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_open_abind_wrt_atyp_var : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_spec_rec_mutual :
(forall A1 A2 X1 n1,
  a_subst_tv_in_atyp A2 X1 A1 = open_atyp_wrt_atyp_rec n1 A2 (close_atyp_wrt_atyp_rec n1 X1 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_atyp_spec_rec :
forall A1 A2 X1 n1,
  a_subst_tv_in_atyp A2 X1 A1 = open_atyp_wrt_atyp_rec n1 A2 (close_atyp_wrt_atyp_rec n1 X1 A1).
Proof.
pose proof a_subst_tv_in_atyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_spec_rec_a_subst_tv_in_aexp_spec_rec_mutual :
(forall abody1 A1 X1 n1,
  a_subst_tv_in_abody A1 X1 abody1 = open_abody_wrt_atyp_rec n1 A1 (close_abody_wrt_atyp_rec n1 X1 abody1)) /\
(forall e1 A1 X1 n1,
  a_subst_tv_in_aexp A1 X1 e1 = open_aexp_wrt_atyp_rec n1 A1 (close_aexp_wrt_atyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_spec_rec :
forall abody1 A1 X1 n1,
  a_subst_tv_in_abody A1 X1 abody1 = open_abody_wrt_atyp_rec n1 A1 (close_abody_wrt_atyp_rec n1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_spec_rec_a_subst_tv_in_aexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_aexp_spec_rec :
forall e1 A1 X1 n1,
  a_subst_tv_in_aexp A1 X1 e1 = open_aexp_wrt_atyp_rec n1 A1 (close_aexp_wrt_atyp_rec n1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_spec_rec_a_subst_tv_in_aexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_spec_rec_a_subst_v_in_aexp_spec_rec_mutual :
(forall abody1 e1 x1 n1,
  a_subst_v_in_abody e1 x1 abody1 = open_abody_wrt_aexp_rec n1 e1 (close_abody_wrt_aexp_rec n1 x1 abody1)) /\
(forall e1 e2 x1 n1,
  a_subst_v_in_aexp e2 x1 e1 = open_aexp_wrt_aexp_rec n1 e2 (close_aexp_wrt_aexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_spec_rec :
forall abody1 e1 x1 n1,
  a_subst_v_in_abody e1 x1 abody1 = open_abody_wrt_aexp_rec n1 e1 (close_abody_wrt_aexp_rec n1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_spec_rec_a_subst_v_in_aexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_aexp_spec_rec :
forall e1 e2 x1 n1,
  a_subst_v_in_aexp e2 x1 e1 = open_aexp_wrt_aexp_rec n1 e2 (close_aexp_wrt_aexp_rec n1 x1 e1).
Proof.
pose proof a_subst_v_in_abody_spec_rec_a_subst_v_in_aexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abind_spec_rec_mutual :
(forall b1 A1 X1 n1,
  a_subst_tv_in_abind A1 X1 b1 = open_abind_wrt_atyp_rec n1 A1 (close_abind_wrt_atyp_rec n1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abind_spec_rec :
forall b1 A1 X1 n1,
  a_subst_tv_in_abind A1 X1 b1 = open_abind_wrt_atyp_rec n1 A1 (close_abind_wrt_atyp_rec n1 X1 b1).
Proof.
pose proof a_subst_tv_in_abind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_spec_rec : lngen.

(* end hide *)

Lemma a_subst_tv_in_atyp_spec :
forall A1 A2 X1,
  a_subst_tv_in_atyp A2 X1 A1 = open_atyp_wrt_atyp (close_atyp_wrt_atyp X1 A1) A2.
Proof.
unfold close_atyp_wrt_atyp; unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_spec : lngen.

Lemma a_subst_tv_in_abody_spec :
forall abody1 A1 X1,
  a_subst_tv_in_abody A1 X1 abody1 = open_abody_wrt_atyp (close_abody_wrt_atyp X1 abody1) A1.
Proof.
unfold close_abody_wrt_atyp; unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_spec : lngen.

Lemma a_subst_tv_in_aexp_spec :
forall e1 A1 X1,
  a_subst_tv_in_aexp A1 X1 e1 = open_aexp_wrt_atyp (close_aexp_wrt_atyp X1 e1) A1.
Proof.
unfold close_aexp_wrt_atyp; unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_spec : lngen.

Lemma a_subst_v_in_abody_spec :
forall abody1 e1 x1,
  a_subst_v_in_abody e1 x1 abody1 = open_abody_wrt_aexp (close_abody_wrt_aexp x1 abody1) e1.
Proof.
unfold close_abody_wrt_aexp; unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_spec : lngen.

Lemma a_subst_v_in_aexp_spec :
forall e1 e2 x1,
  a_subst_v_in_aexp e2 x1 e1 = open_aexp_wrt_aexp (close_aexp_wrt_aexp x1 e1) e2.
Proof.
unfold close_aexp_wrt_aexp; unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_spec : lngen.

Lemma a_subst_tv_in_abind_spec :
forall b1 A1 X1,
  a_subst_tv_in_abind A1 X1 b1 = open_abind_wrt_atyp (close_abind_wrt_atyp X1 b1) A1.
Proof.
unfold close_abind_wrt_atyp; unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_spec : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_a_subst_tv_in_atyp_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` ftv_in_atyp A2 ->
  X2 <> X1 ->
  a_subst_tv_in_atyp A2 X1 (a_subst_tv_in_atyp A3 X2 A1) = a_subst_tv_in_atyp (a_subst_tv_in_atyp A2 X1 A3) X2 (a_subst_tv_in_atyp A2 X1 A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_a_subst_tv_in_atyp :
forall A1 A2 A3 X2 X1,
  X2 `notin` ftv_in_atyp A2 ->
  X2 <> X1 ->
  a_subst_tv_in_atyp A2 X1 (a_subst_tv_in_atyp A3 X2 A1) = a_subst_tv_in_atyp (a_subst_tv_in_atyp A2 X1 A3) X2 (a_subst_tv_in_atyp A2 X1 A1).
Proof.
pose proof a_subst_tv_in_atyp_a_subst_tv_in_atyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_a_subst_tv_in_atyp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_a_subst_tv_in_abody_a_subst_tv_in_aexp_a_subst_tv_in_aexp_mutual :
(forall abody1 A1 A2 X2 X1,
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  a_subst_tv_in_abody A1 X1 (a_subst_tv_in_abody A2 X2 abody1) = a_subst_tv_in_abody (a_subst_tv_in_atyp A1 X1 A2) X2 (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 A2 X2 X1,
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  a_subst_tv_in_aexp A1 X1 (a_subst_tv_in_aexp A2 X2 e1) = a_subst_tv_in_aexp (a_subst_tv_in_atyp A1 X1 A2) X2 (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_a_subst_tv_in_abody :
forall abody1 A1 A2 X2 X1,
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  a_subst_tv_in_abody A1 X1 (a_subst_tv_in_abody A2 X2 abody1) = a_subst_tv_in_abody (a_subst_tv_in_atyp A1 X1 A2) X2 (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_a_subst_tv_in_abody_a_subst_tv_in_aexp_a_subst_tv_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_a_subst_tv_in_abody : lngen.

Lemma a_subst_tv_in_aexp_a_subst_tv_in_aexp :
forall e1 A1 A2 X2 X1,
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  a_subst_tv_in_aexp A1 X1 (a_subst_tv_in_aexp A2 X2 e1) = a_subst_tv_in_aexp (a_subst_tv_in_atyp A1 X1 A2) X2 (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_a_subst_tv_in_abody_a_subst_tv_in_aexp_a_subst_tv_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_a_subst_tv_in_aexp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_a_subst_v_in_abody_a_subst_tv_in_aexp_a_subst_v_in_aexp_mutual :
(forall abody1 A1 e1 x1 X1,
  a_subst_tv_in_abody A1 X1 (a_subst_v_in_abody e1 x1 abody1) = a_subst_v_in_abody (a_subst_tv_in_aexp A1 X1 e1) x1 (a_subst_tv_in_abody A1 X1 abody1)) /\
(forall e1 A1 e2 x1 X1,
  a_subst_tv_in_aexp A1 X1 (a_subst_v_in_aexp e2 x1 e1) = a_subst_v_in_aexp (a_subst_tv_in_aexp A1 X1 e2) x1 (a_subst_tv_in_aexp A1 X1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_a_subst_v_in_abody :
forall abody1 A1 e1 x1 X1,
  a_subst_tv_in_abody A1 X1 (a_subst_v_in_abody e1 x1 abody1) = a_subst_v_in_abody (a_subst_tv_in_aexp A1 X1 e1) x1 (a_subst_tv_in_abody A1 X1 abody1).
Proof.
pose proof a_subst_tv_in_abody_a_subst_v_in_abody_a_subst_tv_in_aexp_a_subst_v_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_a_subst_v_in_abody : lngen.

Lemma a_subst_tv_in_aexp_a_subst_v_in_aexp :
forall e1 A1 e2 x1 X1,
  a_subst_tv_in_aexp A1 X1 (a_subst_v_in_aexp e2 x1 e1) = a_subst_v_in_aexp (a_subst_tv_in_aexp A1 X1 e2) x1 (a_subst_tv_in_aexp A1 X1 e1).
Proof.
pose proof a_subst_tv_in_abody_a_subst_v_in_abody_a_subst_tv_in_aexp_a_subst_v_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_a_subst_v_in_aexp : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_a_subst_tv_in_abody_a_subst_v_in_aexp_a_subst_tv_in_aexp_mutual :
(forall abody1 e1 A1 X1 x1,
  X1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_abody e1 x1 (a_subst_tv_in_abody A1 X1 abody1) = a_subst_tv_in_abody A1 X1 (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 A1 X1 x1,
  X1 `notin` ftv_in_aexp e2 ->
  a_subst_v_in_aexp e2 x1 (a_subst_tv_in_aexp A1 X1 e1) = a_subst_tv_in_aexp A1 X1 (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_a_subst_tv_in_abody :
forall abody1 e1 A1 X1 x1,
  X1 `notin` ftv_in_aexp e1 ->
  a_subst_v_in_abody e1 x1 (a_subst_tv_in_abody A1 X1 abody1) = a_subst_tv_in_abody A1 X1 (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_a_subst_tv_in_abody_a_subst_v_in_aexp_a_subst_tv_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_a_subst_tv_in_abody : lngen.

Lemma a_subst_v_in_aexp_a_subst_tv_in_aexp :
forall e1 e2 A1 X1 x1,
  X1 `notin` ftv_in_aexp e2 ->
  a_subst_v_in_aexp e2 x1 (a_subst_tv_in_aexp A1 X1 e1) = a_subst_tv_in_aexp A1 X1 (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof a_subst_v_in_abody_a_subst_tv_in_abody_a_subst_v_in_aexp_a_subst_tv_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_a_subst_tv_in_aexp : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_a_subst_v_in_abody_a_subst_v_in_aexp_a_subst_v_in_aexp_mutual :
(forall abody1 e1 e2 x2 x1,
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  a_subst_v_in_abody e1 x1 (a_subst_v_in_abody e2 x2 abody1) = a_subst_v_in_abody (a_subst_v_in_aexp e1 x1 e2) x2 (a_subst_v_in_abody e1 x1 abody1)) /\
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_in_aexp e2 ->
  x2 <> x1 ->
  a_subst_v_in_aexp e2 x1 (a_subst_v_in_aexp e3 x2 e1) = a_subst_v_in_aexp (a_subst_v_in_aexp e2 x1 e3) x2 (a_subst_v_in_aexp e2 x1 e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_a_subst_v_in_abody :
forall abody1 e1 e2 x2 x1,
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  a_subst_v_in_abody e1 x1 (a_subst_v_in_abody e2 x2 abody1) = a_subst_v_in_abody (a_subst_v_in_aexp e1 x1 e2) x2 (a_subst_v_in_abody e1 x1 abody1).
Proof.
pose proof a_subst_v_in_abody_a_subst_v_in_abody_a_subst_v_in_aexp_a_subst_v_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_a_subst_v_in_abody : lngen.

Lemma a_subst_v_in_aexp_a_subst_v_in_aexp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_in_aexp e2 ->
  x2 <> x1 ->
  a_subst_v_in_aexp e2 x1 (a_subst_v_in_aexp e3 x2 e1) = a_subst_v_in_aexp (a_subst_v_in_aexp e2 x1 e3) x2 (a_subst_v_in_aexp e2 x1 e1).
Proof.
pose proof a_subst_v_in_abody_a_subst_v_in_abody_a_subst_v_in_aexp_a_subst_v_in_aexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_a_subst_v_in_aexp : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_a_subst_tv_in_abind_mutual :
(forall b1 A1 A2 X2 X1,
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  a_subst_tv_in_abind A1 X1 (a_subst_tv_in_abind A2 X2 b1) = a_subst_tv_in_abind (a_subst_tv_in_atyp A1 X1 A2) X2 (a_subst_tv_in_abind A1 X1 b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_a_subst_tv_in_abind :
forall b1 A1 A2 X2 X1,
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  a_subst_tv_in_abind A1 X1 (a_subst_tv_in_abind A2 X2 b1) = a_subst_tv_in_abind (a_subst_tv_in_atyp A1 X1 A2) X2 (a_subst_tv_in_abind A1 X1 b1).
Proof.
pose proof a_subst_tv_in_abind_a_subst_tv_in_abind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_a_subst_tv_in_abind : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` ftv_in_atyp A2 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_atyp A1 X1 A2 = close_atyp_wrt_atyp_rec n1 X2 (a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X2) A2))).
Proof.
apply_mutual_ind atyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` ftv_in_atyp A2 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_atyp A1 X1 A2 = close_atyp_wrt_atyp_rec n1 X2 (a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X2) A2)).
Proof.
pose proof a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_close_atyp_wrt_atyp_rec_open_atyp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 A1 X1 X2 n1,
  X2 `notin` ftv_in_abody abody1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_abody A1 X1 abody1 = close_abody_wrt_atyp_rec n1 X2 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X2) abody1))) *
(forall e1 A1 X1 X2 n1,
  X2 `notin` ftv_in_aexp e1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_aexp A1 X1 e1 = close_aexp_wrt_atyp_rec n1 X2 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X2) e1))).
Proof.
apply_mutual_ind abody_aexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec :
forall abody1 A1 X1 X2 n1,
  X2 `notin` ftv_in_abody abody1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_abody A1 X1 abody1 = close_abody_wrt_atyp_rec n1 X2 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X2) abody1)).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` ftv_in_aexp e1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_aexp A1 X1 e1 = close_aexp_wrt_atyp_rec n1 X2 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X2) e1)).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 A1 X1 x1 n1,
  x1 `notin` fv_in_abody abody1 ->
  a_subst_tv_in_abody A1 X1 abody1 = close_abody_wrt_aexp_rec n1 x1 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1))) *
(forall e1 A1 X1 x1 n1,
  x1 `notin` fv_in_aexp e1 ->
  a_subst_tv_in_aexp A1 X1 e1 = close_aexp_wrt_aexp_rec n1 x1 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1))).
Proof.
apply_mutual_ind abody_aexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec :
forall abody1 A1 X1 x1 n1,
  x1 `notin` fv_in_abody abody1 ->
  a_subst_tv_in_abody A1 X1 abody1 = close_abody_wrt_aexp_rec n1 x1 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1)).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` fv_in_aexp e1 ->
  a_subst_tv_in_aexp A1 X1 e1 = close_aexp_wrt_aexp_rec n1 x1 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1)).
Proof.
pose proof a_subst_tv_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual :
(forall abody1 e1 x1 X1 n1,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_aexp e1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  a_subst_v_in_abody e1 x1 abody1 = close_abody_wrt_atyp_rec n1 X1 (a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1))) *
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp e1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  a_subst_v_in_aexp e1 x1 e2 = close_aexp_wrt_atyp_rec n1 X1 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e2))).
Proof.
apply_mutual_ind abody_aexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec :
forall abody1 e1 x1 X1 n1,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_aexp e1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  a_subst_v_in_abody e1 x1 abody1 = close_abody_wrt_atyp_rec n1 X1 (a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1)).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp e1 ->
  degree_aexp_wrt_atyp n1 e1 ->
  a_subst_v_in_aexp e1 x1 e2 = close_aexp_wrt_atyp_rec n1 X1 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e2)).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_atyp_rec_open_abody_wrt_atyp_rec_a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_atyp_rec_open_aexp_wrt_atyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual :
(forall abody1 e1 x1 x2 n1,
  x2 `notin` fv_in_abody abody1 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  a_subst_v_in_abody e1 x1 abody1 = close_abody_wrt_aexp_rec n1 x2 (a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x2) abody1))) *
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_in_aexp e2 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  a_subst_v_in_aexp e1 x1 e2 = close_aexp_wrt_aexp_rec n1 x2 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x2) e2))).
Proof.
apply_mutual_ind abody_aexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec :
forall abody1 e1 x1 x2 n1,
  x2 `notin` fv_in_abody abody1 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  a_subst_v_in_abody e1 x1 abody1 = close_abody_wrt_aexp_rec n1 x2 (a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x2) abody1)).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_in_aexp e2 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  degree_aexp_wrt_aexp n1 e1 ->
  a_subst_v_in_aexp e1 x1 e2 = close_aexp_wrt_aexp_rec n1 x2 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x2) e2)).
Proof.
pose proof a_subst_v_in_abody_close_abody_wrt_aexp_rec_open_abody_wrt_aexp_rec_a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_aexp_rec_open_aexp_wrt_aexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abind_close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec_mutual :
(forall b1 A1 X1 X2 n1,
  X2 `notin` ftv_in_abind b1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_abind A1 X1 b1 = close_abind_wrt_atyp_rec n1 X2 (a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X2) b1))).
Proof.
apply_mutual_ind abind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma a_subst_tv_in_abind_close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec :
forall b1 A1 X1 X2 n1,
  X2 `notin` ftv_in_abind b1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  degree_atyp_wrt_atyp n1 A1 ->
  a_subst_tv_in_abind A1 X1 b1 = close_abind_wrt_atyp_rec n1 X2 (a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X2) b1)).
Proof.
pose proof a_subst_tv_in_abind_close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_close_abind_wrt_atyp_rec_open_abind_wrt_atyp_rec : lngen.

(* end hide *)

Lemma a_subst_tv_in_atyp_close_atyp_wrt_atyp_open_atyp_wrt_atyp :
forall A2 A1 X1 X2,
  X2 `notin` ftv_in_atyp A2 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  lc_atyp A1 ->
  a_subst_tv_in_atyp A1 X1 A2 = close_atyp_wrt_atyp X2 (a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp A2 (atyp_tvar_f X2))).
Proof.
unfold close_atyp_wrt_atyp; unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_close_atyp_wrt_atyp_open_atyp_wrt_atyp : lngen.

Lemma a_subst_tv_in_abody_close_abody_wrt_atyp_open_abody_wrt_atyp :
forall abody1 A1 X1 X2,
  X2 `notin` ftv_in_abody abody1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  lc_atyp A1 ->
  a_subst_tv_in_abody A1 X1 abody1 = close_abody_wrt_atyp X2 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X2))).
Proof.
unfold close_abody_wrt_atyp; unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_atyp_open_abody_wrt_atyp : lngen.

Lemma a_subst_tv_in_aexp_close_aexp_wrt_atyp_open_aexp_wrt_atyp :
forall e1 A1 X1 X2,
  X2 `notin` ftv_in_aexp e1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  lc_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 e1 = close_aexp_wrt_atyp X2 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp e1 (atyp_tvar_f X2))).
Proof.
unfold close_aexp_wrt_atyp; unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_atyp_open_aexp_wrt_atyp : lngen.

Lemma a_subst_tv_in_abody_close_abody_wrt_aexp_open_abody_wrt_aexp :
forall abody1 A1 X1 x1,
  x1 `notin` fv_in_abody abody1 ->
  lc_atyp A1 ->
  a_subst_tv_in_abody A1 X1 abody1 = close_abody_wrt_aexp x1 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_aexp abody1 (a_exp_var_f x1))).
Proof.
unfold close_abody_wrt_aexp; unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_close_abody_wrt_aexp_open_abody_wrt_aexp : lngen.

Lemma a_subst_tv_in_aexp_close_aexp_wrt_aexp_open_aexp_wrt_aexp :
forall e1 A1 X1 x1,
  x1 `notin` fv_in_aexp e1 ->
  lc_atyp A1 ->
  a_subst_tv_in_aexp A1 X1 e1 = close_aexp_wrt_aexp x1 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp e1 (a_exp_var_f x1))).
Proof.
unfold close_aexp_wrt_aexp; unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_close_aexp_wrt_aexp_open_aexp_wrt_aexp : lngen.

Lemma a_subst_v_in_abody_close_abody_wrt_atyp_open_abody_wrt_atyp :
forall abody1 e1 x1 X1,
  X1 `notin` ftv_in_abody abody1 ->
  X1 `notin` ftv_in_aexp e1 ->
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 abody1 = close_abody_wrt_atyp X1 (a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X1))).
Proof.
unfold close_abody_wrt_atyp; unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_atyp_open_abody_wrt_atyp : lngen.

Lemma a_subst_v_in_aexp_close_aexp_wrt_atyp_open_aexp_wrt_atyp :
forall e2 e1 x1 X1,
  X1 `notin` ftv_in_aexp e2 ->
  X1 `notin` ftv_in_aexp e1 ->
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 e2 = close_aexp_wrt_atyp X1 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_atyp e2 (atyp_tvar_f X1))).
Proof.
unfold close_aexp_wrt_atyp; unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_atyp_open_aexp_wrt_atyp : lngen.

Lemma a_subst_v_in_abody_close_abody_wrt_aexp_open_abody_wrt_aexp :
forall abody1 e1 x1 x2,
  x2 `notin` fv_in_abody abody1 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  lc_aexp e1 ->
  a_subst_v_in_abody e1 x1 abody1 = close_abody_wrt_aexp x2 (a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp abody1 (a_exp_var_f x2))).
Proof.
unfold close_abody_wrt_aexp; unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_close_abody_wrt_aexp_open_abody_wrt_aexp : lngen.

Lemma a_subst_v_in_aexp_close_aexp_wrt_aexp_open_aexp_wrt_aexp :
forall e2 e1 x1 x2,
  x2 `notin` fv_in_aexp e2 ->
  x2 `notin` fv_in_aexp e1 ->
  x2 <> x1 ->
  lc_aexp e1 ->
  a_subst_v_in_aexp e1 x1 e2 = close_aexp_wrt_aexp x2 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp e2 (a_exp_var_f x2))).
Proof.
unfold close_aexp_wrt_aexp; unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_close_aexp_wrt_aexp_open_aexp_wrt_aexp : lngen.

Lemma a_subst_tv_in_abind_close_abind_wrt_atyp_open_abind_wrt_atyp :
forall b1 A1 X1 X2,
  X2 `notin` ftv_in_abind b1 ->
  X2 `notin` ftv_in_atyp A1 ->
  X2 <> X1 ->
  lc_atyp A1 ->
  a_subst_tv_in_abind A1 X1 b1 = close_abind_wrt_atyp X2 (a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp b1 (atyp_tvar_f X2))).
Proof.
unfold close_abind_wrt_atyp; unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_close_abind_wrt_atyp_open_abind_wrt_atyp : lngen.

Lemma a_subst_tv_in_atyp_atyp_all :
forall X2 A2 A1 X1,
  lc_atyp A1 ->
  X2 `notin` ftv_in_atyp A1 `union` ftv_in_atyp A2 `union` singleton X1 ->
  a_subst_tv_in_atyp A1 X1 (atyp_all A2) = atyp_all (close_atyp_wrt_atyp X2 (a_subst_tv_in_atyp A1 X1 (open_atyp_wrt_atyp A2 (atyp_tvar_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_atyp_all : lngen.

Lemma a_subst_tv_in_aexp_a_exp_abs :
forall x1 e1 A1 X1,
  lc_atyp A1 ->
  x1 `notin` fv_in_aexp e1 ->
  a_subst_tv_in_aexp A1 X1 (a_exp_abs e1) = a_exp_abs (close_aexp_wrt_aexp x1 (a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_aexp e1 (a_exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_a_exp_abs : lngen.

Lemma a_subst_tv_in_aexp_a_exp_tabs :
forall X2 abody1 A1 X1,
  lc_atyp A1 ->
  X2 `notin` ftv_in_atyp A1 `union` ftv_in_abody abody1 `union` singleton X1 ->
  a_subst_tv_in_aexp A1 X1 (a_exp_tabs abody1) = a_exp_tabs (close_abody_wrt_atyp X2 (a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_a_exp_tabs : lngen.

Lemma a_subst_v_in_aexp_a_exp_abs :
forall x2 e2 e1 x1,
  lc_aexp e1 ->
  x2 `notin` fv_in_aexp e1 `union` fv_in_aexp e2 `union` singleton x1 ->
  a_subst_v_in_aexp e1 x1 (a_exp_abs e2) = a_exp_abs (close_aexp_wrt_aexp x2 (a_subst_v_in_aexp e1 x1 (open_aexp_wrt_aexp e2 (a_exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_a_exp_abs : lngen.

Lemma a_subst_v_in_aexp_a_exp_tabs :
forall X1 abody1 e1 x1,
  lc_aexp e1 ->
  X1 `notin` ftv_in_aexp e1 `union` ftv_in_abody abody1 ->
  a_subst_v_in_aexp e1 x1 (a_exp_tabs abody1) = a_exp_tabs (close_abody_wrt_atyp X1 (a_subst_v_in_abody e1 x1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_a_exp_tabs : lngen.

(* begin hide *)

Lemma a_subst_tv_in_atyp_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` ftv_in_atyp A1 ->
  open_atyp_wrt_atyp_rec n1 A2 A1 = a_subst_tv_in_atyp A2 X1 (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1)).
Proof.
apply_mutual_ind atyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_atyp_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` ftv_in_atyp A1 ->
  open_atyp_wrt_atyp_rec n1 A2 A1 = a_subst_tv_in_atyp A2 X1 (open_atyp_wrt_atyp_rec n1 (atyp_tvar_f X1) A1).
Proof.
pose proof a_subst_tv_in_atyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_atyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abody_intro_rec_a_subst_tv_in_aexp_intro_rec_mutual :
(forall abody1 X1 A1 n1,
  X1 `notin` ftv_in_abody abody1 ->
  open_abody_wrt_atyp_rec n1 A1 abody1 = a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1)) /\
(forall e1 X1 A1 n1,
  X1 `notin` ftv_in_aexp e1 ->
  open_aexp_wrt_atyp_rec n1 A1 e1 = a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abody_intro_rec :
forall abody1 X1 A1 n1,
  X1 `notin` ftv_in_abody abody1 ->
  open_abody_wrt_atyp_rec n1 A1 abody1 = a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp_rec n1 (atyp_tvar_f X1) abody1).
Proof.
pose proof a_subst_tv_in_abody_intro_rec_a_subst_tv_in_aexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_abody_intro_rec using solve [auto] : lngen.

Lemma a_subst_tv_in_aexp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` ftv_in_aexp e1 ->
  open_aexp_wrt_atyp_rec n1 A1 e1 = a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp_rec n1 (atyp_tvar_f X1) e1).
Proof.
pose proof a_subst_tv_in_abody_intro_rec_a_subst_tv_in_aexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_aexp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_v_in_abody_intro_rec_a_subst_v_in_aexp_intro_rec_mutual :
(forall abody1 x1 e1 n1,
  x1 `notin` fv_in_abody abody1 ->
  open_abody_wrt_aexp_rec n1 e1 abody1 = a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1)) /\
(forall e1 x1 e2 n1,
  x1 `notin` fv_in_aexp e1 ->
  open_aexp_wrt_aexp_rec n1 e2 e1 = a_subst_v_in_aexp e2 x1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1)).
Proof.
apply_mutual_ind abody_aexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_v_in_abody_intro_rec :
forall abody1 x1 e1 n1,
  x1 `notin` fv_in_abody abody1 ->
  open_abody_wrt_aexp_rec n1 e1 abody1 = a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp_rec n1 (a_exp_var_f x1) abody1).
Proof.
pose proof a_subst_v_in_abody_intro_rec_a_subst_v_in_aexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_intro_rec : lngen.
#[export] Hint Rewrite a_subst_v_in_abody_intro_rec using solve [auto] : lngen.

Lemma a_subst_v_in_aexp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_in_aexp e1 ->
  open_aexp_wrt_aexp_rec n1 e2 e1 = a_subst_v_in_aexp e2 x1 (open_aexp_wrt_aexp_rec n1 (a_exp_var_f x1) e1).
Proof.
pose proof a_subst_v_in_abody_intro_rec_a_subst_v_in_aexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_intro_rec : lngen.
#[export] Hint Rewrite a_subst_v_in_aexp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma a_subst_tv_in_abind_intro_rec_mutual :
(forall b1 X1 A1 n1,
  X1 `notin` ftv_in_abind b1 ->
  open_abind_wrt_atyp_rec n1 A1 b1 = a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1)).
Proof.
apply_mutual_ind abind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma a_subst_tv_in_abind_intro_rec :
forall b1 X1 A1 n1,
  X1 `notin` ftv_in_abind b1 ->
  open_abind_wrt_atyp_rec n1 A1 b1 = a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp_rec n1 (atyp_tvar_f X1) b1).
Proof.
pose proof a_subst_tv_in_abind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_intro_rec : lngen.
#[export] Hint Rewrite a_subst_tv_in_abind_intro_rec using solve [auto] : lngen.

Lemma a_subst_tv_in_atyp_intro :
forall X1 A1 A2,
  X1 `notin` ftv_in_atyp A1 ->
  open_atyp_wrt_atyp A1 A2 = a_subst_tv_in_atyp A2 X1 (open_atyp_wrt_atyp A1 (atyp_tvar_f X1)).
Proof.
unfold open_atyp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_atyp_intro : lngen.

Lemma a_subst_tv_in_abody_intro :
forall X1 abody1 A1,
  X1 `notin` ftv_in_abody abody1 ->
  open_abody_wrt_atyp abody1 A1 = a_subst_tv_in_abody A1 X1 (open_abody_wrt_atyp abody1 (atyp_tvar_f X1)).
Proof.
unfold open_abody_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abody_intro : lngen.

Lemma a_subst_tv_in_aexp_intro :
forall X1 e1 A1,
  X1 `notin` ftv_in_aexp e1 ->
  open_aexp_wrt_atyp e1 A1 = a_subst_tv_in_aexp A1 X1 (open_aexp_wrt_atyp e1 (atyp_tvar_f X1)).
Proof.
unfold open_aexp_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_aexp_intro : lngen.

Lemma a_subst_v_in_abody_intro :
forall x1 abody1 e1,
  x1 `notin` fv_in_abody abody1 ->
  open_abody_wrt_aexp abody1 e1 = a_subst_v_in_abody e1 x1 (open_abody_wrt_aexp abody1 (a_exp_var_f x1)).
Proof.
unfold open_abody_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_abody_intro : lngen.

Lemma a_subst_v_in_aexp_intro :
forall x1 e1 e2,
  x1 `notin` fv_in_aexp e1 ->
  open_aexp_wrt_aexp e1 e2 = a_subst_v_in_aexp e2 x1 (open_aexp_wrt_aexp e1 (a_exp_var_f x1)).
Proof.
unfold open_aexp_wrt_aexp; default_simp.
Qed.

#[export] Hint Resolve a_subst_v_in_aexp_intro : lngen.

Lemma a_subst_tv_in_abind_intro :
forall X1 b1 A1,
  X1 `notin` ftv_in_abind b1 ->
  open_abind_wrt_atyp b1 A1 = a_subst_tv_in_abind A1 X1 (open_abind_wrt_atyp b1 (atyp_tvar_f X1)).
Proof.
unfold open_abind_wrt_atyp; default_simp.
Qed.

#[export] Hint Resolve a_subst_tv_in_abind_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
