Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export decl.def_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme dtyp_ind' := Induction for dtyp Sort Prop.

Combined Scheme dtyp_mutind from dtyp_ind'.

Scheme dtyp_rec' := Induction for dtyp Sort Set.

Combined Scheme dtyp_mutrec from dtyp_rec'.

Scheme binding_ind' := Induction for binding Sort Prop.

Combined Scheme binding_mutind from binding_ind'.

Scheme binding_rec' := Induction for binding Sort Set.

Combined Scheme binding_mutrec from binding_rec'.

Scheme dbody_ind' := Induction for dbody Sort Prop
  with dexp_ind' := Induction for dexp Sort Prop.

Combined Scheme dbody_dexp_mutind from dbody_ind',dexp_ind'.

Scheme dbody_rec' := Induction for dbody Sort Set
  with dexp_rec' := Induction for dexp Sort Set.

Combined Scheme dbody_dexp_mutrec from dbody_rec',dexp_rec'.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_dtyp (T1 : dtyp) {struct T1} : nat :=
  match T1 with
    | dtyp_unit => 1
    | dtyp_top => 1
    | dtyp_bot => 1
    | dtyp_var_f X1 => 1
    | dtyp_var_b n1 => 1
    | dtyp_svar SX1 => 1
    | dtyp_arrow T2 T3 => 1 + (size_dtyp T2) + (size_dtyp T3)
    | dtyp_all T2 => 1 + (size_dtyp T2)
    | dtyp_union T2 T3 => 1 + (size_dtyp T2) + (size_dtyp T3)
    | dtyp_intersection T2 T3 => 1 + (size_dtyp T2) + (size_dtyp T3)
  end.

Fixpoint size_binding (b1 : binding) {struct b1} : nat :=
  match b1 with
    | dbind_tvar_empty => 1
    | dbind_stvar_empty => 1
    | dbind_typ T1 => 1 + (size_dtyp T1)
  end.

Fixpoint size_dbody (dbody1 : dbody) {struct dbody1} : nat :=
  match dbody1 with
    | dbody_anno e1 T1 => 1 + (size_dexp e1) + (size_dtyp T1)
  end

with size_dexp (e1 : dexp) {struct e1} : nat :=
  match e1 with
    | dexp_unit => 1
    | dexp_top => 1
    | dexp_var_f x1 => 1
    | dexp_var_b n1 => 1
    | dexp_abs e2 => 1 + (size_dexp e2)
    | dexp_app e2 e3 => 1 + (size_dexp e2) + (size_dexp e3)
    | dexp_tabs dbody1 => 1 + (size_dbody dbody1)
    | dexp_tapp e2 T1 => 1 + (size_dexp e2) + (size_dtyp T1)
    | dexp_anno e2 T1 => 1 + (size_dexp e2) + (size_dtyp T1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_dtyp_wrt_dtyp : nat -> dtyp -> Prop :=
  | degree_wrt_dtyp_dtyp_unit : forall n1,
    degree_dtyp_wrt_dtyp n1 (dtyp_unit)
  | degree_wrt_dtyp_dtyp_top : forall n1,
    degree_dtyp_wrt_dtyp n1 (dtyp_top)
  | degree_wrt_dtyp_dtyp_bot : forall n1,
    degree_dtyp_wrt_dtyp n1 (dtyp_bot)
  | degree_wrt_dtyp_dtyp_var_f : forall n1 X1,
    degree_dtyp_wrt_dtyp n1 (dtyp_var_f X1)
  | degree_wrt_dtyp_dtyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_dtyp_wrt_dtyp n1 (dtyp_var_b n2)
  | degree_wrt_dtyp_dtyp_svar : forall n1 SX1,
    degree_dtyp_wrt_dtyp n1 (dtyp_svar SX1)
  | degree_wrt_dtyp_dtyp_arrow : forall n1 T1 T2,
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_dtyp_wrt_dtyp n1 T2 ->
    degree_dtyp_wrt_dtyp n1 (dtyp_arrow T1 T2)
  | degree_wrt_dtyp_dtyp_all : forall n1 T1,
    degree_dtyp_wrt_dtyp (S n1) T1 ->
    degree_dtyp_wrt_dtyp n1 (dtyp_all T1)
  | degree_wrt_dtyp_dtyp_union : forall n1 T1 T2,
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_dtyp_wrt_dtyp n1 T2 ->
    degree_dtyp_wrt_dtyp n1 (dtyp_union T1 T2)
  | degree_wrt_dtyp_dtyp_intersection : forall n1 T1 T2,
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_dtyp_wrt_dtyp n1 T2 ->
    degree_dtyp_wrt_dtyp n1 (dtyp_intersection T1 T2).

Scheme degree_dtyp_wrt_dtyp_ind' := Induction for degree_dtyp_wrt_dtyp Sort Prop.

Combined Scheme degree_dtyp_wrt_dtyp_mutind from degree_dtyp_wrt_dtyp_ind'.

#[export] Hint Constructors degree_dtyp_wrt_dtyp : core lngen.

Inductive degree_binding_wrt_dtyp : nat -> binding -> Prop :=
  | degree_wrt_dtyp_dbind_tvar_empty : forall n1,
    degree_binding_wrt_dtyp n1 (dbind_tvar_empty)
  | degree_wrt_dtyp_dbind_stvar_empty : forall n1,
    degree_binding_wrt_dtyp n1 (dbind_stvar_empty)
  | degree_wrt_dtyp_dbind_typ : forall n1 T1,
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_binding_wrt_dtyp n1 (dbind_typ T1).

Scheme degree_binding_wrt_dtyp_ind' := Induction for degree_binding_wrt_dtyp Sort Prop.

Combined Scheme degree_binding_wrt_dtyp_mutind from degree_binding_wrt_dtyp_ind'.

#[export] Hint Constructors degree_binding_wrt_dtyp : core lngen.

Inductive degree_dbody_wrt_dtyp : nat -> dbody -> Prop :=
  | degree_wrt_dtyp_dbody_anno : forall n1 e1 T1,
    degree_dexp_wrt_dtyp n1 e1 ->
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_dbody_wrt_dtyp n1 (dbody_anno e1 T1)

with degree_dexp_wrt_dtyp : nat -> dexp -> Prop :=
  | degree_wrt_dtyp_dexp_unit : forall n1,
    degree_dexp_wrt_dtyp n1 (dexp_unit)
  | degree_wrt_dtyp_dexp_top : forall n1,
    degree_dexp_wrt_dtyp n1 (dexp_top)
  | degree_wrt_dtyp_dexp_var_f : forall n1 x1,
    degree_dexp_wrt_dtyp n1 (dexp_var_f x1)
  | degree_wrt_dtyp_dexp_var_b : forall n1 n2,
    degree_dexp_wrt_dtyp n1 (dexp_var_b n2)
  | degree_wrt_dtyp_dexp_abs : forall n1 e1,
    degree_dexp_wrt_dtyp n1 e1 ->
    degree_dexp_wrt_dtyp n1 (dexp_abs e1)
  | degree_wrt_dtyp_dexp_app : forall n1 e1 e2,
    degree_dexp_wrt_dtyp n1 e1 ->
    degree_dexp_wrt_dtyp n1 e2 ->
    degree_dexp_wrt_dtyp n1 (dexp_app e1 e2)
  | degree_wrt_dtyp_dexp_tabs : forall n1 dbody1,
    degree_dbody_wrt_dtyp (S n1) dbody1 ->
    degree_dexp_wrt_dtyp n1 (dexp_tabs dbody1)
  | degree_wrt_dtyp_dexp_tapp : forall n1 e1 T1,
    degree_dexp_wrt_dtyp n1 e1 ->
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_dexp_wrt_dtyp n1 (dexp_tapp e1 T1)
  | degree_wrt_dtyp_dexp_anno : forall n1 e1 T1,
    degree_dexp_wrt_dtyp n1 e1 ->
    degree_dtyp_wrt_dtyp n1 T1 ->
    degree_dexp_wrt_dtyp n1 (dexp_anno e1 T1).

Inductive degree_dbody_wrt_dexp : nat -> dbody -> Prop :=
  | degree_wrt_dexp_dbody_anno : forall n1 e1 T1,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dbody_wrt_dexp n1 (dbody_anno e1 T1)

with degree_dexp_wrt_dexp : nat -> dexp -> Prop :=
  | degree_wrt_dexp_dexp_unit : forall n1,
    degree_dexp_wrt_dexp n1 (dexp_unit)
  | degree_wrt_dexp_dexp_top : forall n1,
    degree_dexp_wrt_dexp n1 (dexp_top)
  | degree_wrt_dexp_dexp_var_f : forall n1 x1,
    degree_dexp_wrt_dexp n1 (dexp_var_f x1)
  | degree_wrt_dexp_dexp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_dexp_wrt_dexp n1 (dexp_var_b n2)
  | degree_wrt_dexp_dexp_abs : forall n1 e1,
    degree_dexp_wrt_dexp (S n1) e1 ->
    degree_dexp_wrt_dexp n1 (dexp_abs e1)
  | degree_wrt_dexp_dexp_app : forall n1 e1 e2,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 e2 ->
    degree_dexp_wrt_dexp n1 (dexp_app e1 e2)
  | degree_wrt_dexp_dexp_tabs : forall n1 dbody1,
    degree_dbody_wrt_dexp n1 dbody1 ->
    degree_dexp_wrt_dexp n1 (dexp_tabs dbody1)
  | degree_wrt_dexp_dexp_tapp : forall n1 e1 T1,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 (dexp_tapp e1 T1)
  | degree_wrt_dexp_dexp_anno : forall n1 e1 T1,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 (dexp_anno e1 T1).

Scheme degree_dbody_wrt_dtyp_ind' := Induction for degree_dbody_wrt_dtyp Sort Prop
  with degree_dexp_wrt_dtyp_ind' := Induction for degree_dexp_wrt_dtyp Sort Prop.

Combined Scheme degree_dbody_wrt_dtyp_degree_dexp_wrt_dtyp_mutind from degree_dbody_wrt_dtyp_ind',degree_dexp_wrt_dtyp_ind'.

Scheme degree_dbody_wrt_dexp_ind' := Induction for degree_dbody_wrt_dexp Sort Prop
  with degree_dexp_wrt_dexp_ind' := Induction for degree_dexp_wrt_dexp Sort Prop.

Combined Scheme degree_dbody_wrt_dexp_degree_dexp_wrt_dexp_mutind from degree_dbody_wrt_dexp_ind',degree_dexp_wrt_dexp_ind'.

#[export] Hint Constructors degree_dbody_wrt_dtyp : core lngen.

#[export] Hint Constructors degree_dexp_wrt_dtyp : core lngen.

#[export] Hint Constructors degree_dbody_wrt_dexp : core lngen.

#[export] Hint Constructors degree_dexp_wrt_dexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_dtyp : dtyp -> Set :=
  | lc_set_dtyp_unit :
    lc_set_dtyp (dtyp_unit)
  | lc_set_dtyp_top :
    lc_set_dtyp (dtyp_top)
  | lc_set_dtyp_bot :
    lc_set_dtyp (dtyp_bot)
  | lc_set_dtyp_var_f : forall X1,
    lc_set_dtyp (dtyp_var_f X1)
  | lc_set_dtyp_svar : forall SX1,
    lc_set_dtyp (dtyp_svar SX1)
  | lc_set_dtyp_arrow : forall T1 T2,
    lc_set_dtyp T1 ->
    lc_set_dtyp T2 ->
    lc_set_dtyp (dtyp_arrow T1 T2)
  | lc_set_dtyp_all : forall T1,
    (forall X1 : typvar, lc_set_dtyp (open_dtyp_wrt_dtyp T1 (dtyp_var_f X1))) ->
    lc_set_dtyp (dtyp_all T1)
  | lc_set_dtyp_union : forall T1 T2,
    lc_set_dtyp T1 ->
    lc_set_dtyp T2 ->
    lc_set_dtyp (dtyp_union T1 T2)
  | lc_set_dtyp_intersection : forall T1 T2,
    lc_set_dtyp T1 ->
    lc_set_dtyp T2 ->
    lc_set_dtyp (dtyp_intersection T1 T2).

Scheme lc_dtyp_ind' := Induction for lc_dtyp Sort Prop.

Combined Scheme lc_dtyp_mutind from lc_dtyp_ind'.

Scheme lc_set_dtyp_ind' := Induction for lc_set_dtyp Sort Prop.

Combined Scheme lc_set_dtyp_mutind from lc_set_dtyp_ind'.

Scheme lc_set_dtyp_rec' := Induction for lc_set_dtyp Sort Set.

Combined Scheme lc_set_dtyp_mutrec from lc_set_dtyp_rec'.

#[export] Hint Constructors lc_dtyp : core lngen.

#[export] Hint Constructors lc_set_dtyp : core lngen.

Inductive lc_set_binding : binding -> Set :=
  | lc_set_dbind_tvar_empty :
    lc_set_binding (dbind_tvar_empty)
  | lc_set_dbind_stvar_empty :
    lc_set_binding (dbind_stvar_empty)
  | lc_set_dbind_typ : forall T1,
    lc_set_dtyp T1 ->
    lc_set_binding (dbind_typ T1).

Scheme lc_binding_ind' := Induction for lc_binding Sort Prop.

Combined Scheme lc_binding_mutind from lc_binding_ind'.

Scheme lc_set_binding_ind' := Induction for lc_set_binding Sort Prop.

Combined Scheme lc_set_binding_mutind from lc_set_binding_ind'.

Scheme lc_set_binding_rec' := Induction for lc_set_binding Sort Set.

Combined Scheme lc_set_binding_mutrec from lc_set_binding_rec'.

#[export] Hint Constructors lc_binding : core lngen.

#[export] Hint Constructors lc_set_binding : core lngen.

Inductive lc_set_dbody : dbody -> Set :=
  | lc_set_dbody_anno : forall e1 T1,
    lc_set_dexp e1 ->
    lc_set_dtyp T1 ->
    lc_set_dbody (dbody_anno e1 T1)

with lc_set_dexp : dexp -> Set :=
  | lc_set_dexp_unit :
    lc_set_dexp (dexp_unit)
  | lc_set_dexp_top :
    lc_set_dexp (dexp_top)
  | lc_set_dexp_var_f : forall x1,
    lc_set_dexp (dexp_var_f x1)
  | lc_set_dexp_abs : forall e1,
    (forall x1 : expvar, lc_set_dexp (open_dexp_wrt_dexp e1 (dexp_var_f x1))) ->
    lc_set_dexp (dexp_abs e1)
  | lc_set_dexp_app : forall e1 e2,
    lc_set_dexp e1 ->
    lc_set_dexp e2 ->
    lc_set_dexp (dexp_app e1 e2)
  | lc_set_dexp_tabs : forall dbody1,
    (forall X1 : typvar, lc_set_dbody (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1))) ->
    lc_set_dexp (dexp_tabs dbody1)
  | lc_set_dexp_tapp : forall e1 T1,
    lc_set_dexp e1 ->
    lc_set_dtyp T1 ->
    lc_set_dexp (dexp_tapp e1 T1)
  | lc_set_dexp_anno : forall e1 T1,
    lc_set_dexp e1 ->
    lc_set_dtyp T1 ->
    lc_set_dexp (dexp_anno e1 T1).

Scheme lc_dbody_ind' := Induction for lc_dbody Sort Prop
  with lc_dexp_ind' := Induction for lc_dexp Sort Prop.

Combined Scheme lc_dbody_lc_dexp_mutind from lc_dbody_ind',lc_dexp_ind'.

Scheme lc_set_dbody_ind' := Induction for lc_set_dbody Sort Prop
  with lc_set_dexp_ind' := Induction for lc_set_dexp Sort Prop.

Combined Scheme lc_set_dbody_lc_set_dexp_mutind from lc_set_dbody_ind',lc_set_dexp_ind'.

Scheme lc_set_dbody_rec' := Induction for lc_set_dbody Sort Set
  with lc_set_dexp_rec' := Induction for lc_set_dexp Sort Set.

Combined Scheme lc_set_dbody_lc_set_dexp_mutrec from lc_set_dbody_rec',lc_set_dexp_rec'.

#[export] Hint Constructors lc_dbody : core lngen.

#[export] Hint Constructors lc_dexp : core lngen.

#[export] Hint Constructors lc_set_dbody : core lngen.

#[export] Hint Constructors lc_set_dexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_dtyp_wrt_dtyp T1 := forall X1, lc_dtyp (open_dtyp_wrt_dtyp T1 (dtyp_var_f X1)).

#[export] Hint Unfold body_dtyp_wrt_dtyp : core.

Definition body_binding_wrt_dtyp b1 := forall X1, lc_binding (open_binding_wrt_dtyp b1 (dtyp_var_f X1)).

#[export] Hint Unfold body_binding_wrt_dtyp : core.

Definition body_dbody_wrt_dtyp dbody1 := forall X1, lc_dbody (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)).

Definition body_dexp_wrt_dtyp e1 := forall X1, lc_dexp (open_dexp_wrt_dtyp e1 (dtyp_var_f X1)).

Definition body_dbody_wrt_dexp dbody1 := forall x1, lc_dbody (open_dbody_wrt_dexp dbody1 (dexp_var_f x1)).

Definition body_dexp_wrt_dexp e1 := forall x1, lc_dexp (open_dexp_wrt_dexp e1 (dexp_var_f x1)).

#[export] Hint Unfold body_dbody_wrt_dtyp : core.

#[export] Hint Unfold body_dexp_wrt_dtyp : core.

#[export] Hint Unfold body_dbody_wrt_dexp : core.

#[export] Hint Unfold body_dexp_wrt_dexp : core.


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

Lemma size_dtyp_min_mutual :
(forall T1, 1 <= size_dtyp T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dtyp_min :
forall T1, 1 <= size_dtyp T1.
Proof.
pose proof size_dtyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dtyp_min : lngen.

(* begin hide *)

Lemma size_binding_min_mutual :
(forall b1, 1 <= size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_binding_min :
forall b1, 1 <= size_binding b1.
Proof.
pose proof size_binding_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_binding_min : lngen.

(* begin hide *)

Lemma size_dbody_min_size_dexp_min_mutual :
(forall dbody1, 1 <= size_dbody dbody1) /\
(forall e1, 1 <= size_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dbody_min :
forall dbody1, 1 <= size_dbody dbody1.
Proof.
pose proof size_dbody_min_size_dexp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_min : lngen.

Lemma size_dexp_min :
forall e1, 1 <= size_dexp e1.
Proof.
pose proof size_dbody_min_size_dexp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_min : lngen.

(* begin hide *)

Lemma size_dtyp_close_dtyp_wrt_dtyp_rec_mutual :
(forall T1 X1 n1,
  size_dtyp (close_dtyp_wrt_dtyp_rec n1 X1 T1) = size_dtyp T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dtyp_close_dtyp_wrt_dtyp_rec :
forall T1 X1 n1,
  size_dtyp (close_dtyp_wrt_dtyp_rec n1 X1 T1) = size_dtyp T1.
Proof.
pose proof size_dtyp_close_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dtyp_close_dtyp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite size_dtyp_close_dtyp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_close_binding_wrt_dtyp_rec_mutual :
(forall b1 X1 n1,
  size_binding (close_binding_wrt_dtyp_rec n1 X1 b1) = size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_close_binding_wrt_dtyp_rec :
forall b1 X1 n1,
  size_binding (close_binding_wrt_dtyp_rec n1 X1 b1) = size_binding b1.
Proof.
pose proof size_binding_close_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_binding_close_binding_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite size_binding_close_binding_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbody_close_dbody_wrt_dtyp_rec_size_dexp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1,
  size_dbody (close_dbody_wrt_dtyp_rec n1 X1 dbody1) = size_dbody dbody1) /\
(forall e1 X1 n1,
  size_dexp (close_dexp_wrt_dtyp_rec n1 X1 e1) = size_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbody_close_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1,
  size_dbody (close_dbody_wrt_dtyp_rec n1 X1 dbody1) = size_dbody dbody1.
Proof.
pose proof size_dbody_close_dbody_wrt_dtyp_rec_size_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_close_dbody_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite size_dbody_close_dbody_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dexp_close_dexp_wrt_dtyp_rec :
forall e1 X1 n1,
  size_dexp (close_dexp_wrt_dtyp_rec n1 X1 e1) = size_dexp e1.
Proof.
pose proof size_dbody_close_dbody_wrt_dtyp_rec_size_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_close_dexp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite size_dexp_close_dexp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbody_close_dbody_wrt_dexp_rec_size_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1,
  size_dbody (close_dbody_wrt_dexp_rec n1 x1 dbody1) = size_dbody dbody1) /\
(forall e1 x1 n1,
  size_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) = size_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbody_close_dbody_wrt_dexp_rec :
forall dbody1 x1 n1,
  size_dbody (close_dbody_wrt_dexp_rec n1 x1 dbody1) = size_dbody dbody1.
Proof.
pose proof size_dbody_close_dbody_wrt_dexp_rec_size_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_close_dbody_wrt_dexp_rec : lngen.
#[export] Hint Rewrite size_dbody_close_dbody_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  size_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) = size_dexp e1.
Proof.
pose proof size_dbody_close_dbody_wrt_dexp_rec_size_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_close_dexp_wrt_dexp_rec : lngen.
#[export] Hint Rewrite size_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_dtyp_close_dtyp_wrt_dtyp :
forall T1 X1,
  size_dtyp (close_dtyp_wrt_dtyp X1 T1) = size_dtyp T1.
Proof.
unfold close_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dtyp_close_dtyp_wrt_dtyp : lngen.
#[export] Hint Rewrite size_dtyp_close_dtyp_wrt_dtyp using solve [auto] : lngen.

Lemma size_binding_close_binding_wrt_dtyp :
forall b1 X1,
  size_binding (close_binding_wrt_dtyp X1 b1) = size_binding b1.
Proof.
unfold close_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_binding_close_binding_wrt_dtyp : lngen.
#[export] Hint Rewrite size_binding_close_binding_wrt_dtyp using solve [auto] : lngen.

Lemma size_dbody_close_dbody_wrt_dtyp :
forall dbody1 X1,
  size_dbody (close_dbody_wrt_dtyp X1 dbody1) = size_dbody dbody1.
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dbody_close_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite size_dbody_close_dbody_wrt_dtyp using solve [auto] : lngen.

Lemma size_dexp_close_dexp_wrt_dtyp :
forall e1 X1,
  size_dexp (close_dexp_wrt_dtyp X1 e1) = size_dexp e1.
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dexp_close_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite size_dexp_close_dexp_wrt_dtyp using solve [auto] : lngen.

Lemma size_dbody_close_dbody_wrt_dexp :
forall dbody1 x1,
  size_dbody (close_dbody_wrt_dexp x1 dbody1) = size_dbody dbody1.
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve size_dbody_close_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite size_dbody_close_dbody_wrt_dexp using solve [auto] : lngen.

Lemma size_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  size_dexp (close_dexp_wrt_dexp x1 e1) = size_dexp e1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve size_dexp_close_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite size_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_dtyp_open_dtyp_wrt_dtyp_rec_mutual :
(forall T1 T2 n1,
  size_dtyp T1 <= size_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dtyp_open_dtyp_wrt_dtyp_rec :
forall T1 T2 n1,
  size_dtyp T1 <= size_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1).
Proof.
pose proof size_dtyp_open_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dtyp_open_dtyp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_dtyp_rec_mutual :
(forall b1 T1 n1,
  size_binding b1 <= size_binding (open_binding_wrt_dtyp_rec n1 T1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_dtyp_rec :
forall b1 T1 n1,
  size_binding b1 <= size_binding (open_binding_wrt_dtyp_rec n1 T1 b1).
Proof.
pose proof size_binding_open_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_binding_open_binding_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dtyp_rec_size_dexp_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 T1 n1,
  size_dbody dbody1 <= size_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1)) /\
(forall e1 T1 n1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dtyp_rec :
forall dbody1 T1 n1,
  size_dbody dbody1 <= size_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1).
Proof.
pose proof size_dbody_open_dbody_wrt_dtyp_rec_size_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dtyp_rec :
forall e1 T1 n1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1).
Proof.
pose proof size_dbody_open_dbody_wrt_dtyp_rec_size_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dexp_rec_size_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 e1 n1,
  size_dbody dbody1 <= size_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1)) /\
(forall e1 e2 n1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dexp_rec :
forall dbody1 e1 n1,
  size_dbody dbody1 <= size_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1).
Proof.
pose proof size_dbody_open_dbody_wrt_dexp_rec_size_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec :
forall e1 e2 n1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof size_dbody_open_dbody_wrt_dexp_rec_size_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma size_dtyp_open_dtyp_wrt_dtyp :
forall T1 T2,
  size_dtyp T1 <= size_dtyp (open_dtyp_wrt_dtyp T1 T2).
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dtyp_open_dtyp_wrt_dtyp : lngen.

Lemma size_binding_open_binding_wrt_dtyp :
forall b1 T1,
  size_binding b1 <= size_binding (open_binding_wrt_dtyp b1 T1).
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_binding_open_binding_wrt_dtyp : lngen.

Lemma size_dbody_open_dbody_wrt_dtyp :
forall dbody1 T1,
  size_dbody dbody1 <= size_dbody (open_dbody_wrt_dtyp dbody1 T1).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dtyp : lngen.

Lemma size_dexp_open_dexp_wrt_dtyp :
forall e1 T1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dtyp e1 T1).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dtyp : lngen.

Lemma size_dbody_open_dbody_wrt_dexp :
forall dbody1 e1,
  size_dbody dbody1 <= size_dbody (open_dbody_wrt_dexp dbody1 e1).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dexp : lngen.

Lemma size_dexp_open_dexp_wrt_dexp :
forall e1 e2,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma size_dtyp_open_dtyp_wrt_dtyp_rec_var_mutual :
(forall T1 X1 n1,
  size_dtyp (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1) = size_dtyp T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dtyp_open_dtyp_wrt_dtyp_rec_var :
forall T1 X1 n1,
  size_dtyp (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1) = size_dtyp T1.
Proof.
pose proof size_dtyp_open_dtyp_wrt_dtyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dtyp_open_dtyp_wrt_dtyp_rec_var : lngen.
#[export] Hint Rewrite size_dtyp_open_dtyp_wrt_dtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_dtyp_rec_var_mutual :
(forall b1 X1 n1,
  size_binding (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1) = size_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_binding_open_binding_wrt_dtyp_rec_var :
forall b1 X1 n1,
  size_binding (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1) = size_binding b1.
Proof.
pose proof size_binding_open_binding_wrt_dtyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_binding_open_binding_wrt_dtyp_rec_var : lngen.
#[export] Hint Rewrite size_binding_open_binding_wrt_dtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dtyp_rec_var_size_dexp_open_dexp_wrt_dtyp_rec_var_mutual :
(forall dbody1 X1 n1,
  size_dbody (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1) = size_dbody dbody1) /\
(forall e1 X1 n1,
  size_dexp (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1) = size_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dtyp_rec_var :
forall dbody1 X1 n1,
  size_dbody (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1) = size_dbody dbody1.
Proof.
pose proof size_dbody_open_dbody_wrt_dtyp_rec_var_size_dexp_open_dexp_wrt_dtyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dtyp_rec_var : lngen.
#[export] Hint Rewrite size_dbody_open_dbody_wrt_dtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dtyp_rec_var :
forall e1 X1 n1,
  size_dexp (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1) = size_dexp e1.
Proof.
pose proof size_dbody_open_dbody_wrt_dtyp_rec_var_size_dexp_open_dexp_wrt_dtyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dtyp_rec_var : lngen.
#[export] Hint Rewrite size_dexp_open_dexp_wrt_dtyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dexp_rec_var_size_dexp_open_dexp_wrt_dexp_rec_var_mutual :
(forall dbody1 x1 n1,
  size_dbody (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1) = size_dbody dbody1) /\
(forall e1 x1 n1,
  size_dexp (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1) = size_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbody_open_dbody_wrt_dexp_rec_var :
forall dbody1 x1 n1,
  size_dbody (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1) = size_dbody dbody1.
Proof.
pose proof size_dbody_open_dbody_wrt_dexp_rec_var_size_dexp_open_dexp_wrt_dexp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dexp_rec_var : lngen.
#[export] Hint Rewrite size_dbody_open_dbody_wrt_dexp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_var :
forall e1 x1 n1,
  size_dexp (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1) = size_dexp e1.
Proof.
pose proof size_dbody_open_dbody_wrt_dexp_rec_var_size_dexp_open_dexp_wrt_dexp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dexp_rec_var : lngen.
#[export] Hint Rewrite size_dexp_open_dexp_wrt_dexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_dtyp_open_dtyp_wrt_dtyp_var :
forall T1 X1,
  size_dtyp (open_dtyp_wrt_dtyp T1 (dtyp_var_f X1)) = size_dtyp T1.
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dtyp_open_dtyp_wrt_dtyp_var : lngen.
#[export] Hint Rewrite size_dtyp_open_dtyp_wrt_dtyp_var using solve [auto] : lngen.

Lemma size_binding_open_binding_wrt_dtyp_var :
forall b1 X1,
  size_binding (open_binding_wrt_dtyp b1 (dtyp_var_f X1)) = size_binding b1.
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_binding_open_binding_wrt_dtyp_var : lngen.
#[export] Hint Rewrite size_binding_open_binding_wrt_dtyp_var using solve [auto] : lngen.

Lemma size_dbody_open_dbody_wrt_dtyp_var :
forall dbody1 X1,
  size_dbody (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)) = size_dbody dbody1.
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dtyp_var : lngen.
#[export] Hint Rewrite size_dbody_open_dbody_wrt_dtyp_var using solve [auto] : lngen.

Lemma size_dexp_open_dexp_wrt_dtyp_var :
forall e1 X1,
  size_dexp (open_dexp_wrt_dtyp e1 (dtyp_var_f X1)) = size_dexp e1.
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dtyp_var : lngen.
#[export] Hint Rewrite size_dexp_open_dexp_wrt_dtyp_var using solve [auto] : lngen.

Lemma size_dbody_open_dbody_wrt_dexp_var :
forall dbody1 x1,
  size_dbody (open_dbody_wrt_dexp dbody1 (dexp_var_f x1)) = size_dbody dbody1.
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve size_dbody_open_dbody_wrt_dexp_var : lngen.
#[export] Hint Rewrite size_dbody_open_dbody_wrt_dexp_var using solve [auto] : lngen.

Lemma size_dexp_open_dexp_wrt_dexp_var :
forall e1 x1,
  size_dexp (open_dexp_wrt_dexp e1 (dexp_var_f x1)) = size_dexp e1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve size_dexp_open_dexp_wrt_dexp_var : lngen.
#[export] Hint Rewrite size_dexp_open_dexp_wrt_dexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_S_mutual :
(forall n1 T1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dtyp_wrt_dtyp (S n1) T1).
Proof.
apply_mutual_ind degree_dtyp_wrt_dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dtyp_wrt_dtyp_S :
forall n1 T1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dtyp_wrt_dtyp (S n1) T1.
Proof.
pose proof degree_dtyp_wrt_dtyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_S : lngen.

(* begin hide *)

Lemma degree_binding_wrt_dtyp_S_mutual :
(forall n1 b1,
  degree_binding_wrt_dtyp n1 b1 ->
  degree_binding_wrt_dtyp (S n1) b1).
Proof.
apply_mutual_ind degree_binding_wrt_dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_binding_wrt_dtyp_S :
forall n1 b1,
  degree_binding_wrt_dtyp n1 b1 ->
  degree_binding_wrt_dtyp (S n1) b1.
Proof.
pose proof degree_binding_wrt_dtyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_S : lngen.

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_S_degree_dexp_wrt_dtyp_S_mutual :
(forall n1 dbody1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dbody_wrt_dtyp (S n1) dbody1) /\
(forall n1 e1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp (S n1) e1).
Proof.
apply_mutual_ind degree_dbody_wrt_dtyp_degree_dexp_wrt_dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dbody_wrt_dtyp_S :
forall n1 dbody1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dbody_wrt_dtyp (S n1) dbody1.
Proof.
pose proof degree_dbody_wrt_dtyp_S_degree_dexp_wrt_dtyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_S : lngen.

Lemma degree_dexp_wrt_dtyp_S :
forall n1 e1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp (S n1) e1.
Proof.
pose proof degree_dbody_wrt_dtyp_S_degree_dexp_wrt_dtyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_S : lngen.

(* begin hide *)

Lemma degree_dbody_wrt_dexp_S_degree_dexp_wrt_dexp_S_mutual :
(forall n1 dbody1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp (S n1) dbody1) /\
(forall n1 e1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) e1).
Proof.
apply_mutual_ind degree_dbody_wrt_dexp_degree_dexp_wrt_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dbody_wrt_dexp_S :
forall n1 dbody1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp (S n1) dbody1.
Proof.
pose proof degree_dbody_wrt_dexp_S_degree_dexp_wrt_dexp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_S : lngen.

Lemma degree_dexp_wrt_dexp_S :
forall n1 e1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) e1.
Proof.
pose proof degree_dbody_wrt_dexp_S_degree_dexp_wrt_dexp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_S : lngen.

Lemma degree_dtyp_wrt_dtyp_O :
forall n1 T1,
  degree_dtyp_wrt_dtyp O T1 ->
  degree_dtyp_wrt_dtyp n1 T1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_O : lngen.

Lemma degree_binding_wrt_dtyp_O :
forall n1 b1,
  degree_binding_wrt_dtyp O b1 ->
  degree_binding_wrt_dtyp n1 b1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_O : lngen.

Lemma degree_dbody_wrt_dtyp_O :
forall n1 dbody1,
  degree_dbody_wrt_dtyp O dbody1 ->
  degree_dbody_wrt_dtyp n1 dbody1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_O : lngen.

Lemma degree_dexp_wrt_dtyp_O :
forall n1 e1,
  degree_dexp_wrt_dtyp O e1 ->
  degree_dexp_wrt_dtyp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_O : lngen.

Lemma degree_dbody_wrt_dexp_O :
forall n1 dbody1,
  degree_dbody_wrt_dexp O dbody1 ->
  degree_dbody_wrt_dexp n1 dbody1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_O : lngen.

Lemma degree_dexp_wrt_dexp_O :
forall n1 e1,
  degree_dexp_wrt_dexp O e1 ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_O : lngen.

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec_mutual :
(forall T1 X1 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dtyp_wrt_dtyp (S n1) (close_dtyp_wrt_dtyp_rec n1 X1 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec :
forall T1 X1 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dtyp_wrt_dtyp (S n1) (close_dtyp_wrt_dtyp_rec n1 X1 T1).
Proof.
pose proof degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec_mutual :
(forall b1 X1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  degree_binding_wrt_dtyp (S n1) (close_binding_wrt_dtyp_rec n1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec :
forall b1 X1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  degree_binding_wrt_dtyp (S n1) (close_binding_wrt_dtyp_rec n1 X1 b1).
Proof.
pose proof degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dbody_wrt_dtyp (S n1) (close_dbody_wrt_dtyp_rec n1 X1 dbody1)) /\
(forall e1 X1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp (S n1) (close_dexp_wrt_dtyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dbody_wrt_dtyp (S n1) (close_dbody_wrt_dtyp_rec n1 X1 dbody1).
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec :
forall e1 X1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp (S n1) (close_dexp_wrt_dtyp_rec n1 X1 e1).
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1 n2,
  degree_dbody_wrt_dtyp n2 dbody1 ->
  degree_dbody_wrt_dtyp n2 (close_dbody_wrt_dexp_rec n1 x1 dbody1)) /\
(forall e1 x1 n1 n2,
  degree_dexp_wrt_dtyp n2 e1 ->
  degree_dexp_wrt_dtyp n2 (close_dexp_wrt_dexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec :
forall dbody1 x1 n1 n2,
  degree_dbody_wrt_dtyp n2 dbody1 ->
  degree_dbody_wrt_dtyp n2 (close_dbody_wrt_dexp_rec n1 x1 dbody1).
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1 n2,
  degree_dexp_wrt_dtyp n2 e1 ->
  degree_dexp_wrt_dtyp n2 (close_dexp_wrt_dexp_rec n1 x1 e1).
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1 n2,
  degree_dbody_wrt_dexp n2 dbody1 ->
  degree_dbody_wrt_dexp n2 (close_dbody_wrt_dtyp_rec n1 X1 dbody1)) /\
(forall e1 X1 n1 n2,
  degree_dexp_wrt_dexp n2 e1 ->
  degree_dexp_wrt_dexp n2 (close_dexp_wrt_dtyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1 n2,
  degree_dbody_wrt_dexp n2 dbody1 ->
  degree_dbody_wrt_dexp n2 (close_dbody_wrt_dtyp_rec n1 X1 dbody1).
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec :
forall e1 X1 n1 n2,
  degree_dexp_wrt_dexp n2 e1 ->
  degree_dexp_wrt_dexp n2 (close_dexp_wrt_dtyp_rec n1 X1 e1).
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp (S n1) (close_dbody_wrt_dexp_rec n1 x1 dbody1)) /\
(forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec :
forall dbody1 x1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp (S n1) (close_dbody_wrt_dexp_rec n1 x1 dbody1).
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1).
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp :
forall T1 X1,
  degree_dtyp_wrt_dtyp 0 T1 ->
  degree_dtyp_wrt_dtyp 1 (close_dtyp_wrt_dtyp X1 T1).
Proof.
unfold close_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp : lngen.

Lemma degree_binding_wrt_dtyp_close_binding_wrt_dtyp :
forall b1 X1,
  degree_binding_wrt_dtyp 0 b1 ->
  degree_binding_wrt_dtyp 1 (close_binding_wrt_dtyp X1 b1).
Proof.
unfold close_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_close_binding_wrt_dtyp : lngen.

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp :
forall dbody1 X1,
  degree_dbody_wrt_dtyp 0 dbody1 ->
  degree_dbody_wrt_dtyp 1 (close_dbody_wrt_dtyp X1 dbody1).
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp : lngen.

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp :
forall e1 X1,
  degree_dexp_wrt_dtyp 0 e1 ->
  degree_dexp_wrt_dtyp 1 (close_dexp_wrt_dtyp X1 e1).
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp : lngen.

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dexp :
forall dbody1 x1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dbody_wrt_dtyp n1 (close_dbody_wrt_dexp x1 dbody1).
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_close_dbody_wrt_dexp : lngen.

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dexp :
forall e1 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp n1 (close_dexp_wrt_dexp x1 e1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_close_dexp_wrt_dexp : lngen.

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dtyp :
forall dbody1 X1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp n1 (close_dbody_wrt_dtyp X1 dbody1).
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_close_dbody_wrt_dtyp : lngen.

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dtyp :
forall e1 X1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 (close_dexp_wrt_dtyp X1 e1).
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dtyp : lngen.

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dexp :
forall dbody1 x1,
  degree_dbody_wrt_dexp 0 dbody1 ->
  degree_dbody_wrt_dexp 1 (close_dbody_wrt_dexp x1 dbody1).
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_close_dbody_wrt_dexp : lngen.

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  degree_dexp_wrt_dexp 0 e1 ->
  degree_dexp_wrt_dexp 1 (close_dexp_wrt_dexp x1 e1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec_inv_mutual :
(forall T1 X1 n1,
  degree_dtyp_wrt_dtyp (S n1) (close_dtyp_wrt_dtyp_rec n1 X1 T1) ->
  degree_dtyp_wrt_dtyp n1 T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec_inv :
forall T1 X1 n1,
  degree_dtyp_wrt_dtyp (S n1) (close_dtyp_wrt_dtyp_rec n1 X1 T1) ->
  degree_dtyp_wrt_dtyp n1 T1.
Proof.
pose proof degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec_inv_mutual :
(forall b1 X1 n1,
  degree_binding_wrt_dtyp (S n1) (close_binding_wrt_dtyp_rec n1 X1 b1) ->
  degree_binding_wrt_dtyp n1 b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec_inv :
forall b1 X1 n1,
  degree_binding_wrt_dtyp (S n1) (close_binding_wrt_dtyp_rec n1 X1 b1) ->
  degree_binding_wrt_dtyp n1 b1.
Proof.
pose proof degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_binding_wrt_dtyp_close_binding_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_inv_mutual :
(forall dbody1 X1 n1,
  degree_dbody_wrt_dtyp (S n1) (close_dbody_wrt_dtyp_rec n1 X1 dbody1) ->
  degree_dbody_wrt_dtyp n1 dbody1) /\
(forall e1 X1 n1,
  degree_dexp_wrt_dtyp (S n1) (close_dexp_wrt_dtyp_rec n1 X1 e1) ->
  degree_dexp_wrt_dtyp n1 e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_inv :
forall dbody1 X1 n1,
  degree_dbody_wrt_dtyp (S n1) (close_dbody_wrt_dtyp_rec n1 X1 dbody1) ->
  degree_dbody_wrt_dtyp n1 dbody1.
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_inv :
forall e1 X1 n1,
  degree_dexp_wrt_dtyp (S n1) (close_dexp_wrt_dtyp_rec n1 X1 e1) ->
  degree_dexp_wrt_dtyp n1 e1.
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_inv_mutual :
(forall dbody1 x1 n1 n2,
  degree_dbody_wrt_dtyp n2 (close_dbody_wrt_dexp_rec n1 x1 dbody1) ->
  degree_dbody_wrt_dtyp n2 dbody1) /\
(forall e1 x1 n1 n2,
  degree_dexp_wrt_dtyp n2 (close_dexp_wrt_dexp_rec n1 x1 e1) ->
  degree_dexp_wrt_dtyp n2 e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_inv :
forall dbody1 x1 n1 n2,
  degree_dbody_wrt_dtyp n2 (close_dbody_wrt_dexp_rec n1 x1 dbody1) ->
  degree_dbody_wrt_dtyp n2 dbody1.
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_inv :
forall e1 x1 n1 n2,
  degree_dexp_wrt_dtyp n2 (close_dexp_wrt_dexp_rec n1 x1 e1) ->
  degree_dexp_wrt_dtyp n2 e1.
Proof.
pose proof degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_inv_mutual :
(forall dbody1 X1 n1 n2,
  degree_dbody_wrt_dexp n2 (close_dbody_wrt_dtyp_rec n1 X1 dbody1) ->
  degree_dbody_wrt_dexp n2 dbody1) /\
(forall e1 X1 n1 n2,
  degree_dexp_wrt_dexp n2 (close_dexp_wrt_dtyp_rec n1 X1 e1) ->
  degree_dexp_wrt_dexp n2 e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_inv :
forall dbody1 X1 n1 n2,
  degree_dbody_wrt_dexp n2 (close_dbody_wrt_dtyp_rec n1 X1 dbody1) ->
  degree_dbody_wrt_dexp n2 dbody1.
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_inv :
forall e1 X1 n1 n2,
  degree_dexp_wrt_dexp n2 (close_dexp_wrt_dtyp_rec n1 X1 e1) ->
  degree_dexp_wrt_dexp n2 e1.
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual :
(forall dbody1 x1 n1,
  degree_dbody_wrt_dexp (S n1) (close_dbody_wrt_dexp_rec n1 x1 dbody1) ->
  degree_dbody_wrt_dexp n1 dbody1) /\
(forall e1 x1 n1,
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1) ->
  degree_dexp_wrt_dexp n1 e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_inv :
forall dbody1 x1 n1,
  degree_dbody_wrt_dexp (S n1) (close_dbody_wrt_dexp_rec n1 x1 dbody1) ->
  degree_dbody_wrt_dexp n1 dbody1.
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv :
forall e1 x1 n1,
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1) ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
pose proof degree_dbody_wrt_dexp_close_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

Lemma degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_inv :
forall T1 X1,
  degree_dtyp_wrt_dtyp 1 (close_dtyp_wrt_dtyp X1 T1) ->
  degree_dtyp_wrt_dtyp 0 T1.
Proof.
unfold close_dtyp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp_inv : lngen.

Lemma degree_binding_wrt_dtyp_close_binding_wrt_dtyp_inv :
forall b1 X1,
  degree_binding_wrt_dtyp 1 (close_binding_wrt_dtyp X1 b1) ->
  degree_binding_wrt_dtyp 0 b1.
Proof.
unfold close_binding_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_binding_wrt_dtyp_close_binding_wrt_dtyp_inv : lngen.

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_inv :
forall dbody1 X1,
  degree_dbody_wrt_dtyp 1 (close_dbody_wrt_dtyp X1 dbody1) ->
  degree_dbody_wrt_dtyp 0 dbody1.
Proof.
unfold close_dbody_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_close_dbody_wrt_dtyp_inv : lngen.

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_inv :
forall e1 X1,
  degree_dexp_wrt_dtyp 1 (close_dexp_wrt_dtyp X1 e1) ->
  degree_dexp_wrt_dtyp 0 e1.
Proof.
unfold close_dexp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_close_dexp_wrt_dtyp_inv : lngen.

Lemma degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_inv :
forall dbody1 x1 n1,
  degree_dbody_wrt_dtyp n1 (close_dbody_wrt_dexp x1 dbody1) ->
  degree_dbody_wrt_dtyp n1 dbody1.
Proof.
unfold close_dbody_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_close_dbody_wrt_dexp_inv : lngen.

Lemma degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_inv :
forall e1 x1 n1,
  degree_dexp_wrt_dtyp n1 (close_dexp_wrt_dexp x1 e1) ->
  degree_dexp_wrt_dtyp n1 e1.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_close_dexp_wrt_dexp_inv : lngen.

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_inv :
forall dbody1 X1 n1,
  degree_dbody_wrt_dexp n1 (close_dbody_wrt_dtyp X1 dbody1) ->
  degree_dbody_wrt_dexp n1 dbody1.
Proof.
unfold close_dbody_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_close_dbody_wrt_dtyp_inv : lngen.

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_inv :
forall e1 X1 n1,
  degree_dexp_wrt_dexp n1 (close_dexp_wrt_dtyp X1 e1) ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
unfold close_dexp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dtyp_inv : lngen.

Lemma degree_dbody_wrt_dexp_close_dbody_wrt_dexp_inv :
forall dbody1 x1,
  degree_dbody_wrt_dexp 1 (close_dbody_wrt_dexp x1 dbody1) ->
  degree_dbody_wrt_dexp 0 dbody1.
Proof.
unfold close_dbody_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_close_dbody_wrt_dexp_inv : lngen.

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_inv :
forall e1 x1,
  degree_dexp_wrt_dexp 1 (close_dexp_wrt_dexp x1 e1) ->
  degree_dexp_wrt_dexp 0 e1.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dexp_inv : lngen.

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec_mutual :
(forall T1 T2 n1,
  degree_dtyp_wrt_dtyp (S n1) T1 ->
  degree_dtyp_wrt_dtyp n1 T2 ->
  degree_dtyp_wrt_dtyp n1 (open_dtyp_wrt_dtyp_rec n1 T2 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec :
forall T1 T2 n1,
  degree_dtyp_wrt_dtyp (S n1) T1 ->
  degree_dtyp_wrt_dtyp n1 T2 ->
  degree_dtyp_wrt_dtyp n1 (open_dtyp_wrt_dtyp_rec n1 T2 T1).
Proof.
pose proof degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec_mutual :
(forall b1 T1 n1,
  degree_binding_wrt_dtyp (S n1) b1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_binding_wrt_dtyp n1 (open_binding_wrt_dtyp_rec n1 T1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec :
forall b1 T1 n1,
  degree_binding_wrt_dtyp (S n1) b1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_binding_wrt_dtyp n1 (open_binding_wrt_dtyp_rec n1 T1 b1).
Proof.
pose proof degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 T1 n1,
  degree_dbody_wrt_dtyp (S n1) dbody1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dtyp_rec n1 T1 dbody1)) /\
(forall e1 T1 n1,
  degree_dexp_wrt_dtyp (S n1) e1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dtyp_rec n1 T1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec :
forall dbody1 T1 n1,
  degree_dbody_wrt_dtyp (S n1) dbody1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dtyp_rec n1 T1 dbody1).
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec :
forall e1 T1 n1,
  degree_dexp_wrt_dtyp (S n1) e1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dtyp_rec n1 T1 e1).
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 e1 n1 n2,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dexp_rec n2 e1 dbody1)) /\
(forall e1 e2 n1 n2,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp n1 e2 ->
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dexp_rec n2 e2 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec :
forall dbody1 e1 n1 n2,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dexp_rec n2 e1 dbody1).
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec :
forall e1 e2 n1 n2,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp n1 e2 ->
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dexp_rec n2 e2 e1).
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 T1 n1 n2,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dtyp_rec n2 T1 dbody1)) /\
(forall e1 T1 n1 n2,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dtyp_rec n2 T1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec :
forall dbody1 T1 n1 n2,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dtyp_rec n2 T1 dbody1).
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec :
forall e1 T1 n1 n2,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dtyp_rec n2 T1 e1).
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 e1 n1,
  degree_dbody_wrt_dexp (S n1) dbody1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dexp_rec n1 e1 dbody1)) /\
(forall e1 e2 n1,
  degree_dexp_wrt_dexp (S n1) e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec :
forall dbody1 e1 n1,
  degree_dbody_wrt_dexp (S n1) dbody1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dexp_rec n1 e1 dbody1).
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec :
forall e1 e2 n1,
  degree_dexp_wrt_dexp (S n1) e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp :
forall T1 T2,
  degree_dtyp_wrt_dtyp 1 T1 ->
  degree_dtyp_wrt_dtyp 0 T2 ->
  degree_dtyp_wrt_dtyp 0 (open_dtyp_wrt_dtyp T1 T2).
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp : lngen.

Lemma degree_binding_wrt_dtyp_open_binding_wrt_dtyp :
forall b1 T1,
  degree_binding_wrt_dtyp 1 b1 ->
  degree_dtyp_wrt_dtyp 0 T1 ->
  degree_binding_wrt_dtyp 0 (open_binding_wrt_dtyp b1 T1).
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_open_binding_wrt_dtyp : lngen.

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp :
forall dbody1 T1,
  degree_dbody_wrt_dtyp 1 dbody1 ->
  degree_dtyp_wrt_dtyp 0 T1 ->
  degree_dbody_wrt_dtyp 0 (open_dbody_wrt_dtyp dbody1 T1).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp : lngen.

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp :
forall e1 T1,
  degree_dexp_wrt_dtyp 1 e1 ->
  degree_dtyp_wrt_dtyp 0 T1 ->
  degree_dexp_wrt_dtyp 0 (open_dexp_wrt_dtyp e1 T1).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp : lngen.

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dexp :
forall dbody1 e1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dexp dbody1 e1).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_open_dbody_wrt_dexp : lngen.

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dexp :
forall e1 e2 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp n1 e2 ->
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_open_dexp_wrt_dexp : lngen.

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dtyp :
forall dbody1 T1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dtyp dbody1 T1).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_open_dbody_wrt_dtyp : lngen.

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dtyp :
forall e1 T1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dtyp e1 T1).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dtyp : lngen.

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dexp :
forall dbody1 e1,
  degree_dbody_wrt_dexp 1 dbody1 ->
  degree_dexp_wrt_dexp 0 e1 ->
  degree_dbody_wrt_dexp 0 (open_dbody_wrt_dexp dbody1 e1).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_open_dbody_wrt_dexp : lngen.

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e1 e2,
  degree_dexp_wrt_dexp 1 e1 ->
  degree_dexp_wrt_dexp 0 e2 ->
  degree_dexp_wrt_dexp 0 (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec_inv_mutual :
(forall T1 T2 n1,
  degree_dtyp_wrt_dtyp n1 (open_dtyp_wrt_dtyp_rec n1 T2 T1) ->
  degree_dtyp_wrt_dtyp (S n1) T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec_inv :
forall T1 T2 n1,
  degree_dtyp_wrt_dtyp n1 (open_dtyp_wrt_dtyp_rec n1 T2 T1) ->
  degree_dtyp_wrt_dtyp (S n1) T1.
Proof.
pose proof degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec_inv_mutual :
(forall b1 T1 n1,
  degree_binding_wrt_dtyp n1 (open_binding_wrt_dtyp_rec n1 T1 b1) ->
  degree_binding_wrt_dtyp (S n1) b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec_inv :
forall b1 T1 n1,
  degree_binding_wrt_dtyp n1 (open_binding_wrt_dtyp_rec n1 T1 b1) ->
  degree_binding_wrt_dtyp (S n1) b1.
Proof.
pose proof degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_binding_wrt_dtyp_open_binding_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_inv_mutual :
(forall dbody1 T1 n1,
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dtyp_rec n1 T1 dbody1) ->
  degree_dbody_wrt_dtyp (S n1) dbody1) /\
(forall e1 T1 n1,
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dtyp_rec n1 T1 e1) ->
  degree_dexp_wrt_dtyp (S n1) e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_inv :
forall dbody1 T1 n1,
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dtyp_rec n1 T1 dbody1) ->
  degree_dbody_wrt_dtyp (S n1) dbody1.
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_inv :
forall e1 T1 n1,
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dtyp_rec n1 T1 e1) ->
  degree_dexp_wrt_dtyp (S n1) e1.
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_inv_mutual :
(forall dbody1 e1 n1 n2,
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dexp_rec n2 e1 dbody1) ->
  degree_dbody_wrt_dtyp n1 dbody1) /\
(forall e1 e2 n1 n2,
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dexp_rec n2 e2 e1) ->
  degree_dexp_wrt_dtyp n1 e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_inv :
forall dbody1 e1 n1 n2,
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dexp_rec n2 e1 dbody1) ->
  degree_dbody_wrt_dtyp n1 dbody1.
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_inv :
forall e1 e2 n1 n2,
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dexp_rec n2 e2 e1) ->
  degree_dexp_wrt_dtyp n1 e1.
Proof.
pose proof degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_inv_mutual :
(forall dbody1 T1 n1 n2,
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dtyp_rec n2 T1 dbody1) ->
  degree_dbody_wrt_dexp n1 dbody1) /\
(forall e1 T1 n1 n2,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dtyp_rec n2 T1 e1) ->
  degree_dexp_wrt_dexp n1 e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_inv :
forall dbody1 T1 n1 n2,
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dtyp_rec n2 T1 dbody1) ->
  degree_dbody_wrt_dexp n1 dbody1.
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_inv :
forall e1 T1 n1 n2,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dtyp_rec n2 T1 e1) ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_rec_inv_degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual :
(forall dbody1 e1 n1,
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dexp_rec n1 e1 dbody1) ->
  degree_dbody_wrt_dexp (S n1) dbody1) /\
(forall e1 e2 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1) ->
  degree_dexp_wrt_dexp (S n1) e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_inv :
forall dbody1 e1 n1,
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dexp_rec n1 e1 dbody1) ->
  degree_dbody_wrt_dexp (S n1) dbody1.
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv :
forall e1 e2 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1) ->
  degree_dexp_wrt_dexp (S n1) e1.
Proof.
pose proof degree_dbody_wrt_dexp_open_dbody_wrt_dexp_rec_inv_degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

Lemma degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_inv :
forall T1 T2,
  degree_dtyp_wrt_dtyp 0 (open_dtyp_wrt_dtyp T1 T2) ->
  degree_dtyp_wrt_dtyp 1 T1.
Proof.
unfold open_dtyp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp_inv : lngen.

Lemma degree_binding_wrt_dtyp_open_binding_wrt_dtyp_inv :
forall b1 T1,
  degree_binding_wrt_dtyp 0 (open_binding_wrt_dtyp b1 T1) ->
  degree_binding_wrt_dtyp 1 b1.
Proof.
unfold open_binding_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_binding_wrt_dtyp_open_binding_wrt_dtyp_inv : lngen.

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_inv :
forall dbody1 T1,
  degree_dbody_wrt_dtyp 0 (open_dbody_wrt_dtyp dbody1 T1) ->
  degree_dbody_wrt_dtyp 1 dbody1.
Proof.
unfold open_dbody_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_open_dbody_wrt_dtyp_inv : lngen.

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_inv :
forall e1 T1,
  degree_dexp_wrt_dtyp 0 (open_dexp_wrt_dtyp e1 T1) ->
  degree_dexp_wrt_dtyp 1 e1.
Proof.
unfold open_dexp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_open_dexp_wrt_dtyp_inv : lngen.

Lemma degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_inv :
forall dbody1 e1 n1,
  degree_dbody_wrt_dtyp n1 (open_dbody_wrt_dexp dbody1 e1) ->
  degree_dbody_wrt_dtyp n1 dbody1.
Proof.
unfold open_dbody_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dtyp_open_dbody_wrt_dexp_inv : lngen.

Lemma degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_inv :
forall e1 e2 n1,
  degree_dexp_wrt_dtyp n1 (open_dexp_wrt_dexp e1 e2) ->
  degree_dexp_wrt_dtyp n1 e1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dtyp_open_dexp_wrt_dexp_inv : lngen.

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_inv :
forall dbody1 T1 n1,
  degree_dbody_wrt_dexp n1 (open_dbody_wrt_dtyp dbody1 T1) ->
  degree_dbody_wrt_dexp n1 dbody1.
Proof.
unfold open_dbody_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_open_dbody_wrt_dtyp_inv : lngen.

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_inv :
forall e1 T1 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dtyp e1 T1) ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
unfold open_dexp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dtyp_inv : lngen.

Lemma degree_dbody_wrt_dexp_open_dbody_wrt_dexp_inv :
forall dbody1 e1,
  degree_dbody_wrt_dexp 0 (open_dbody_wrt_dexp dbody1 e1) ->
  degree_dbody_wrt_dexp 1 dbody1.
Proof.
unfold open_dbody_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbody_wrt_dexp_open_dbody_wrt_dexp_inv : lngen.

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_inv :
forall e1 e2,
  degree_dexp_wrt_dexp 0 (open_dexp_wrt_dexp e1 e2) ->
  degree_dexp_wrt_dexp 1 e1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_dtyp_wrt_dtyp_rec_inj_mutual :
(forall T1 T2 X1 n1,
  close_dtyp_wrt_dtyp_rec n1 X1 T1 = close_dtyp_wrt_dtyp_rec n1 X1 T2 ->
  T1 = T2).
Proof.
apply_mutual_ind dtyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dtyp_wrt_dtyp_rec_inj :
forall T1 T2 X1 n1,
  close_dtyp_wrt_dtyp_rec n1 X1 T1 = close_dtyp_wrt_dtyp_rec n1 X1 T2 ->
  T1 = T2.
Proof.
pose proof close_dtyp_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dtyp_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_dtyp_rec_inj_mutual :
(forall b1 b2 X1 n1,
  close_binding_wrt_dtyp_rec n1 X1 b1 = close_binding_wrt_dtyp_rec n1 X1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_dtyp_rec_inj :
forall b1 b2 X1 n1,
  close_binding_wrt_dtyp_rec n1 X1 b1 = close_binding_wrt_dtyp_rec n1 X1 b2 ->
  b1 = b2.
Proof.
pose proof close_binding_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_binding_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dtyp_rec_inj_close_dexp_wrt_dtyp_rec_inj_mutual :
(forall dbody1 dbody2 X1 n1,
  close_dbody_wrt_dtyp_rec n1 X1 dbody1 = close_dbody_wrt_dtyp_rec n1 X1 dbody2 ->
  dbody1 = dbody2) /\
(forall e1 e2 X1 n1,
  close_dexp_wrt_dtyp_rec n1 X1 e1 = close_dexp_wrt_dtyp_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind dbody_dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dtyp_rec_inj :
forall dbody1 dbody2 X1 n1,
  close_dbody_wrt_dtyp_rec n1 X1 dbody1 = close_dbody_wrt_dtyp_rec n1 X1 dbody2 ->
  dbody1 = dbody2.
Proof.
pose proof close_dbody_wrt_dtyp_rec_inj_close_dexp_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dbody_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dtyp_rec_inj :
forall e1 e2 X1 n1,
  close_dexp_wrt_dtyp_rec n1 X1 e1 = close_dexp_wrt_dtyp_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_dbody_wrt_dtyp_rec_inj_close_dexp_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dexp_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dexp_rec_inj_close_dexp_wrt_dexp_rec_inj_mutual :
(forall dbody1 dbody2 x1 n1,
  close_dbody_wrt_dexp_rec n1 x1 dbody1 = close_dbody_wrt_dexp_rec n1 x1 dbody2 ->
  dbody1 = dbody2) /\
(forall e1 e2 x1 n1,
  close_dexp_wrt_dexp_rec n1 x1 e1 = close_dexp_wrt_dexp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind dbody_dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dexp_rec_inj :
forall dbody1 dbody2 x1 n1,
  close_dbody_wrt_dexp_rec n1 x1 dbody1 = close_dbody_wrt_dexp_rec n1 x1 dbody2 ->
  dbody1 = dbody2.
Proof.
pose proof close_dbody_wrt_dexp_rec_inj_close_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dbody_wrt_dexp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_inj :
forall e1 e2 x1 n1,
  close_dexp_wrt_dexp_rec n1 x1 e1 = close_dexp_wrt_dexp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_dbody_wrt_dexp_rec_inj_close_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dexp_wrt_dexp_rec_inj : lngen.

(* end hide *)

Lemma close_dtyp_wrt_dtyp_inj :
forall T1 T2 X1,
  close_dtyp_wrt_dtyp X1 T1 = close_dtyp_wrt_dtyp X1 T2 ->
  T1 = T2.
Proof.
unfold close_dtyp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_dtyp_wrt_dtyp_inj : lngen.

Lemma close_binding_wrt_dtyp_inj :
forall b1 b2 X1,
  close_binding_wrt_dtyp X1 b1 = close_binding_wrt_dtyp X1 b2 ->
  b1 = b2.
Proof.
unfold close_binding_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_binding_wrt_dtyp_inj : lngen.

Lemma close_dbody_wrt_dtyp_inj :
forall dbody1 dbody2 X1,
  close_dbody_wrt_dtyp X1 dbody1 = close_dbody_wrt_dtyp X1 dbody2 ->
  dbody1 = dbody2.
Proof.
unfold close_dbody_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_dbody_wrt_dtyp_inj : lngen.

Lemma close_dexp_wrt_dtyp_inj :
forall e1 e2 X1,
  close_dexp_wrt_dtyp X1 e1 = close_dexp_wrt_dtyp X1 e2 ->
  e1 = e2.
Proof.
unfold close_dexp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_dexp_wrt_dtyp_inj : lngen.

Lemma close_dbody_wrt_dexp_inj :
forall dbody1 dbody2 x1,
  close_dbody_wrt_dexp x1 dbody1 = close_dbody_wrt_dexp x1 dbody2 ->
  dbody1 = dbody2.
Proof.
unfold close_dbody_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate close_dbody_wrt_dexp_inj : lngen.

Lemma close_dexp_wrt_dexp_inj :
forall e1 e2 x1,
  close_dexp_wrt_dexp x1 e1 = close_dexp_wrt_dexp x1 e2 ->
  e1 = e2.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate close_dexp_wrt_dexp_inj : lngen.

(* begin hide *)

Lemma close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec_mutual :
(forall T1 X1 n1,
  X1 `notin` ftv_in_dtyp T1 ->
  close_dtyp_wrt_dtyp_rec n1 X1 (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1) = T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec :
forall T1 X1 n1,
  X1 `notin` ftv_in_dtyp T1 ->
  close_dtyp_wrt_dtyp_rec n1 X1 (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1) = T1.
Proof.
pose proof close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec_mutual :
(forall b1 X1 n1,
  X1 `notin` ftv_in_binding b1 ->
  close_binding_wrt_dtyp_rec n1 X1 (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1) = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec :
forall b1 X1 n1,
  X1 `notin` ftv_in_binding b1 ->
  close_binding_wrt_dtyp_rec n1 X1 (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1) = b1.
Proof.
pose proof close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1,
  X1 `notin` ftv_in_dbody dbody1 ->
  close_dbody_wrt_dtyp_rec n1 X1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1) = dbody1) /\
(forall e1 X1 n1,
  X1 `notin` ftv_in_dexp e1 ->
  close_dexp_wrt_dtyp_rec n1 X1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1) = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1,
  X1 `notin` ftv_in_dbody dbody1 ->
  close_dbody_wrt_dtyp_rec n1 X1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1) = dbody1.
Proof.
pose proof close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec :
forall e1 X1 n1,
  X1 `notin` ftv_in_dexp e1 ->
  close_dexp_wrt_dtyp_rec n1 X1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1) = e1.
Proof.
pose proof close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1,
  x1 `notin` fv_in_dbody dbody1 ->
  close_dbody_wrt_dexp_rec n1 x1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1) = dbody1) /\
(forall e1 x1 n1,
  x1 `notin` fv_in_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec :
forall dbody1 x1 n1,
  x1 `notin` fv_in_dbody dbody1 ->
  close_dbody_wrt_dexp_rec n1 x1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1) = dbody1.
Proof.
pose proof close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec : lngen.
#[export] Hint Rewrite close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  x1 `notin` fv_in_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1) = e1.
Proof.
pose proof close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.
#[export] Hint Rewrite close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp :
forall T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  close_dtyp_wrt_dtyp X1 (open_dtyp_wrt_dtyp T1 (dtyp_var_f X1)) = T1.
Proof.
unfold close_dtyp_wrt_dtyp; unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp : lngen.
#[export] Hint Rewrite close_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp using solve [auto] : lngen.

Lemma close_binding_wrt_dtyp_open_binding_wrt_dtyp :
forall b1 X1,
  X1 `notin` ftv_in_binding b1 ->
  close_binding_wrt_dtyp X1 (open_binding_wrt_dtyp b1 (dtyp_var_f X1)) = b1.
Proof.
unfold close_binding_wrt_dtyp; unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_binding_wrt_dtyp_open_binding_wrt_dtyp : lngen.
#[export] Hint Rewrite close_binding_wrt_dtyp_open_binding_wrt_dtyp using solve [auto] : lngen.

Lemma close_dbody_wrt_dtyp_open_dbody_wrt_dtyp :
forall dbody1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  close_dbody_wrt_dtyp X1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)) = dbody1.
Proof.
unfold close_dbody_wrt_dtyp; unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_dbody_wrt_dtyp_open_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite close_dbody_wrt_dtyp_open_dbody_wrt_dtyp using solve [auto] : lngen.

Lemma close_dexp_wrt_dtyp_open_dexp_wrt_dtyp :
forall e1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  close_dexp_wrt_dtyp X1 (open_dexp_wrt_dtyp e1 (dtyp_var_f X1)) = e1.
Proof.
unfold close_dexp_wrt_dtyp; unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_dexp_wrt_dtyp_open_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite close_dexp_wrt_dtyp_open_dexp_wrt_dtyp using solve [auto] : lngen.

Lemma close_dbody_wrt_dexp_open_dbody_wrt_dexp :
forall dbody1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  close_dbody_wrt_dexp x1 (open_dbody_wrt_dexp dbody1 (dexp_var_f x1)) = dbody1.
Proof.
unfold close_dbody_wrt_dexp; unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve close_dbody_wrt_dexp_open_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite close_dbody_wrt_dexp_open_dbody_wrt_dexp using solve [auto] : lngen.

Lemma close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e1 x1,
  x1 `notin` fv_in_dexp e1 ->
  close_dexp_wrt_dexp x1 (open_dexp_wrt_dexp e1 (dexp_var_f x1)) = e1.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite close_dexp_wrt_dexp_open_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dtyp_wrt_dtyp_rec_close_dtyp_wrt_dtyp_rec_mutual :
(forall T1 X1 n1,
  open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_dtyp_wrt_dtyp_rec n1 X1 T1) = T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dtyp_wrt_dtyp_rec_close_dtyp_wrt_dtyp_rec :
forall T1 X1 n1,
  open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_dtyp_wrt_dtyp_rec n1 X1 T1) = T1.
Proof.
pose proof open_dtyp_wrt_dtyp_rec_close_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dtyp_wrt_dtyp_rec_close_dtyp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite open_dtyp_wrt_dtyp_rec_close_dtyp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_dtyp_rec_close_binding_wrt_dtyp_rec_mutual :
(forall b1 X1 n1,
  open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_binding_wrt_dtyp_rec n1 X1 b1) = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_dtyp_rec_close_binding_wrt_dtyp_rec :
forall b1 X1 n1,
  open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_binding_wrt_dtyp_rec n1 X1 b1) = b1.
Proof.
pose proof open_binding_wrt_dtyp_rec_close_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_binding_wrt_dtyp_rec_close_binding_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite open_binding_wrt_dtyp_rec_close_binding_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dtyp_rec_close_dbody_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1,
  open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_dbody_wrt_dtyp_rec n1 X1 dbody1) = dbody1) /\
(forall e1 X1 n1,
  open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_dexp_wrt_dtyp_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dtyp_rec_close_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1,
  open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_dbody_wrt_dtyp_rec n1 X1 dbody1) = dbody1.
Proof.
pose proof open_dbody_wrt_dtyp_rec_close_dbody_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbody_wrt_dtyp_rec_close_dbody_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite open_dbody_wrt_dtyp_rec_close_dbody_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec :
forall e1 X1 n1,
  open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) (close_dexp_wrt_dtyp_rec n1 X1 e1) = e1.
Proof.
pose proof open_dbody_wrt_dtyp_rec_close_dbody_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dexp_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite open_dexp_wrt_dtyp_rec_close_dexp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dexp_rec_close_dbody_wrt_dexp_rec_open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1,
  open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) (close_dbody_wrt_dexp_rec n1 x1 dbody1) = dbody1) /\
(forall e1 x1 n1,
  open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) (close_dexp_wrt_dexp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dexp_rec_close_dbody_wrt_dexp_rec :
forall dbody1 x1 n1,
  open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) (close_dbody_wrt_dexp_rec n1 x1 dbody1) = dbody1.
Proof.
pose proof open_dbody_wrt_dexp_rec_close_dbody_wrt_dexp_rec_open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbody_wrt_dexp_rec_close_dbody_wrt_dexp_rec : lngen.
#[export] Hint Rewrite open_dbody_wrt_dexp_rec_close_dbody_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) (close_dexp_wrt_dexp_rec n1 x1 e1) = e1.
Proof.
pose proof open_dbody_wrt_dexp_rec_close_dbody_wrt_dexp_rec_open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec : lngen.
#[export] Hint Rewrite open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp :
forall T1 X1,
  open_dtyp_wrt_dtyp (close_dtyp_wrt_dtyp X1 T1) (dtyp_var_f X1) = T1.
Proof.
unfold close_dtyp_wrt_dtyp; unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp : lngen.
#[export] Hint Rewrite open_dtyp_wrt_dtyp_close_dtyp_wrt_dtyp using solve [auto] : lngen.

Lemma open_binding_wrt_dtyp_close_binding_wrt_dtyp :
forall b1 X1,
  open_binding_wrt_dtyp (close_binding_wrt_dtyp X1 b1) (dtyp_var_f X1) = b1.
Proof.
unfold close_binding_wrt_dtyp; unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_binding_wrt_dtyp_close_binding_wrt_dtyp : lngen.
#[export] Hint Rewrite open_binding_wrt_dtyp_close_binding_wrt_dtyp using solve [auto] : lngen.

Lemma open_dbody_wrt_dtyp_close_dbody_wrt_dtyp :
forall dbody1 X1,
  open_dbody_wrt_dtyp (close_dbody_wrt_dtyp X1 dbody1) (dtyp_var_f X1) = dbody1.
Proof.
unfold close_dbody_wrt_dtyp; unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_dbody_wrt_dtyp_close_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite open_dbody_wrt_dtyp_close_dbody_wrt_dtyp using solve [auto] : lngen.

Lemma open_dexp_wrt_dtyp_close_dexp_wrt_dtyp :
forall e1 X1,
  open_dexp_wrt_dtyp (close_dexp_wrt_dtyp X1 e1) (dtyp_var_f X1) = e1.
Proof.
unfold close_dexp_wrt_dtyp; unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_dexp_wrt_dtyp_close_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite open_dexp_wrt_dtyp_close_dexp_wrt_dtyp using solve [auto] : lngen.

Lemma open_dbody_wrt_dexp_close_dbody_wrt_dexp :
forall dbody1 x1,
  open_dbody_wrt_dexp (close_dbody_wrt_dexp x1 dbody1) (dexp_var_f x1) = dbody1.
Proof.
unfold close_dbody_wrt_dexp; unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve open_dbody_wrt_dexp_close_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite open_dbody_wrt_dexp_close_dbody_wrt_dexp using solve [auto] : lngen.

Lemma open_dexp_wrt_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  open_dexp_wrt_dexp (close_dexp_wrt_dexp x1 e1) (dexp_var_f x1) = e1.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve open_dexp_wrt_dexp_close_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite open_dexp_wrt_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dtyp_wrt_dtyp_rec_inj_mutual :
(forall T2 T1 X1 n1,
  X1 `notin` ftv_in_dtyp T2 ->
  X1 `notin` ftv_in_dtyp T1 ->
  open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T2 = open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1 ->
  T2 = T1).
Proof.
apply_mutual_ind dtyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dtyp_wrt_dtyp_rec_inj :
forall T2 T1 X1 n1,
  X1 `notin` ftv_in_dtyp T2 ->
  X1 `notin` ftv_in_dtyp T1 ->
  open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T2 = open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1 ->
  T2 = T1.
Proof.
pose proof open_dtyp_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dtyp_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_dtyp_rec_inj_mutual :
(forall b2 b1 X1 n1,
  X1 `notin` ftv_in_binding b2 ->
  X1 `notin` ftv_in_binding b1 ->
  open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b2 = open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind binding_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_dtyp_rec_inj :
forall b2 b1 X1 n1,
  X1 `notin` ftv_in_binding b2 ->
  X1 `notin` ftv_in_binding b1 ->
  open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b2 = open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1 ->
  b2 = b1.
Proof.
pose proof open_binding_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_binding_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dtyp_rec_inj_open_dexp_wrt_dtyp_rec_inj_mutual :
(forall dbody2 dbody1 X1 n1,
  X1 `notin` ftv_in_dbody dbody2 ->
  X1 `notin` ftv_in_dbody dbody1 ->
  open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody2 = open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1 ->
  dbody2 = dbody1) /\
(forall e2 e1 X1 n1,
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp e1 ->
  open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e2 = open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dtyp_rec_inj :
forall dbody2 dbody1 X1 n1,
  X1 `notin` ftv_in_dbody dbody2 ->
  X1 `notin` ftv_in_dbody dbody1 ->
  open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody2 = open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1 ->
  dbody2 = dbody1.
Proof.
pose proof open_dbody_wrt_dtyp_rec_inj_open_dexp_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dbody_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dtyp_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp e1 ->
  open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e2 = open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_dbody_wrt_dtyp_rec_inj_open_dexp_wrt_dtyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dexp_wrt_dtyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dexp_rec_inj_open_dexp_wrt_dexp_rec_inj_mutual :
(forall dbody2 dbody1 x1 n1,
  x1 `notin` fv_in_dbody dbody2 ->
  x1 `notin` fv_in_dbody dbody1 ->
  open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody2 = open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1 ->
  dbody2 = dbody1) /\
(forall e2 e1 x1 n1,
  x1 `notin` fv_in_dexp e2 ->
  x1 `notin` fv_in_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e2 = open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dexp_rec_inj :
forall dbody2 dbody1 x1 n1,
  x1 `notin` fv_in_dbody dbody2 ->
  x1 `notin` fv_in_dbody dbody1 ->
  open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody2 = open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1 ->
  dbody2 = dbody1.
Proof.
pose proof open_dbody_wrt_dexp_rec_inj_open_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dbody_wrt_dexp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_in_dexp e2 ->
  x1 `notin` fv_in_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e2 = open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_dbody_wrt_dexp_rec_inj_open_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dexp_wrt_dexp_rec_inj : lngen.

(* end hide *)

Lemma open_dtyp_wrt_dtyp_inj :
forall T2 T1 X1,
  X1 `notin` ftv_in_dtyp T2 ->
  X1 `notin` ftv_in_dtyp T1 ->
  open_dtyp_wrt_dtyp T2 (dtyp_var_f X1) = open_dtyp_wrt_dtyp T1 (dtyp_var_f X1) ->
  T2 = T1.
Proof.
unfold open_dtyp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_dtyp_wrt_dtyp_inj : lngen.

Lemma open_binding_wrt_dtyp_inj :
forall b2 b1 X1,
  X1 `notin` ftv_in_binding b2 ->
  X1 `notin` ftv_in_binding b1 ->
  open_binding_wrt_dtyp b2 (dtyp_var_f X1) = open_binding_wrt_dtyp b1 (dtyp_var_f X1) ->
  b2 = b1.
Proof.
unfold open_binding_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_binding_wrt_dtyp_inj : lngen.

Lemma open_dbody_wrt_dtyp_inj :
forall dbody2 dbody1 X1,
  X1 `notin` ftv_in_dbody dbody2 ->
  X1 `notin` ftv_in_dbody dbody1 ->
  open_dbody_wrt_dtyp dbody2 (dtyp_var_f X1) = open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1) ->
  dbody2 = dbody1.
Proof.
unfold open_dbody_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_dbody_wrt_dtyp_inj : lngen.

Lemma open_dexp_wrt_dtyp_inj :
forall e2 e1 X1,
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp e1 ->
  open_dexp_wrt_dtyp e2 (dtyp_var_f X1) = open_dexp_wrt_dtyp e1 (dtyp_var_f X1) ->
  e2 = e1.
Proof.
unfold open_dexp_wrt_dtyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_dexp_wrt_dtyp_inj : lngen.

Lemma open_dbody_wrt_dexp_inj :
forall dbody2 dbody1 x1,
  x1 `notin` fv_in_dbody dbody2 ->
  x1 `notin` fv_in_dbody dbody1 ->
  open_dbody_wrt_dexp dbody2 (dexp_var_f x1) = open_dbody_wrt_dexp dbody1 (dexp_var_f x1) ->
  dbody2 = dbody1.
Proof.
unfold open_dbody_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate open_dbody_wrt_dexp_inj : lngen.

Lemma open_dexp_wrt_dexp_inj :
forall e2 e1 x1,
  x1 `notin` fv_in_dexp e2 ->
  x1 `notin` fv_in_dexp e1 ->
  open_dexp_wrt_dexp e2 (dexp_var_f x1) = open_dexp_wrt_dexp e1 (dexp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

#[export] Hint Immediate open_dexp_wrt_dexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_dtyp_wrt_dtyp_of_lc_dtyp_mutual :
(forall T1,
  lc_dtyp T1 ->
  degree_dtyp_wrt_dtyp 0 T1).
Proof.
apply_mutual_ind lc_dtyp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dtyp_wrt_dtyp_of_lc_dtyp :
forall T1,
  lc_dtyp T1 ->
  degree_dtyp_wrt_dtyp 0 T1.
Proof.
pose proof degree_dtyp_wrt_dtyp_of_lc_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dtyp_wrt_dtyp_of_lc_dtyp : lngen.

(* begin hide *)

Lemma degree_binding_wrt_dtyp_of_lc_binding_mutual :
(forall b1,
  lc_binding b1 ->
  degree_binding_wrt_dtyp 0 b1).
Proof.
apply_mutual_ind lc_binding_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_binding_wrt_dtyp_of_lc_binding :
forall b1,
  lc_binding b1 ->
  degree_binding_wrt_dtyp 0 b1.
Proof.
pose proof degree_binding_wrt_dtyp_of_lc_binding_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_binding_wrt_dtyp_of_lc_binding : lngen.

(* begin hide *)

Lemma degree_dbody_wrt_dtyp_of_lc_dbody_degree_dexp_wrt_dtyp_of_lc_dexp_mutual :
(forall dbody1,
  lc_dbody dbody1 ->
  degree_dbody_wrt_dtyp 0 dbody1) /\
(forall e1,
  lc_dexp e1 ->
  degree_dexp_wrt_dtyp 0 e1).
Proof.
apply_mutual_ind lc_dbody_lc_dexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dbody_wrt_dtyp_of_lc_dbody :
forall dbody1,
  lc_dbody dbody1 ->
  degree_dbody_wrt_dtyp 0 dbody1.
Proof.
pose proof degree_dbody_wrt_dtyp_of_lc_dbody_degree_dexp_wrt_dtyp_of_lc_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dtyp_of_lc_dbody : lngen.

Lemma degree_dexp_wrt_dtyp_of_lc_dexp :
forall e1,
  lc_dexp e1 ->
  degree_dexp_wrt_dtyp 0 e1.
Proof.
pose proof degree_dbody_wrt_dtyp_of_lc_dbody_degree_dexp_wrt_dtyp_of_lc_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dtyp_of_lc_dexp : lngen.

(* begin hide *)

Lemma degree_dbody_wrt_dexp_of_lc_dbody_degree_dexp_wrt_dexp_of_lc_dexp_mutual :
(forall dbody1,
  lc_dbody dbody1 ->
  degree_dbody_wrt_dexp 0 dbody1) /\
(forall e1,
  lc_dexp e1 ->
  degree_dexp_wrt_dexp 0 e1).
Proof.
apply_mutual_ind lc_dbody_lc_dexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dbody_wrt_dexp_of_lc_dbody :
forall dbody1,
  lc_dbody dbody1 ->
  degree_dbody_wrt_dexp 0 dbody1.
Proof.
pose proof degree_dbody_wrt_dexp_of_lc_dbody_degree_dexp_wrt_dexp_of_lc_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbody_wrt_dexp_of_lc_dbody : lngen.

Lemma degree_dexp_wrt_dexp_of_lc_dexp :
forall e1,
  lc_dexp e1 ->
  degree_dexp_wrt_dexp 0 e1.
Proof.
pose proof degree_dbody_wrt_dexp_of_lc_dbody_degree_dexp_wrt_dexp_of_lc_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dexp_wrt_dexp_of_lc_dexp : lngen.

(* begin hide *)

Lemma lc_dtyp_of_degree_size_mutual :
forall i1,
(forall T1,
  size_dtyp T1 = i1 ->
  degree_dtyp_wrt_dtyp 0 T1 ->
  lc_dtyp T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dtyp_mutind;
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

Lemma lc_dtyp_of_degree :
forall T1,
  degree_dtyp_wrt_dtyp 0 T1 ->
  lc_dtyp T1.
Proof.
intros T1; intros;
pose proof (lc_dtyp_of_degree_size_mutual (size_dtyp T1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_dtyp_of_degree : lngen.

(* begin hide *)

Lemma lc_binding_of_degree_size_mutual :
forall i1,
(forall b1,
  size_binding b1 = i1 ->
  degree_binding_wrt_dtyp 0 b1 ->
  lc_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind binding_mutind;
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

Lemma lc_binding_of_degree :
forall b1,
  degree_binding_wrt_dtyp 0 b1 ->
  lc_binding b1.
Proof.
intros b1; intros;
pose proof (lc_binding_of_degree_size_mutual (size_binding b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_binding_of_degree : lngen.

(* begin hide *)

Lemma lc_dbody_of_degree_lc_dexp_of_degree_size_mutual :
forall i1,
(forall dbody1,
  size_dbody dbody1 = i1 ->
  degree_dbody_wrt_dtyp 0 dbody1 ->
  degree_dbody_wrt_dexp 0 dbody1 ->
  lc_dbody dbody1) /\
(forall e1,
  size_dexp e1 = i1 ->
  degree_dexp_wrt_dtyp 0 e1 ->
  degree_dexp_wrt_dexp 0 e1 ->
  lc_dexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dbody_dexp_mutind;
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

Lemma lc_dbody_of_degree :
forall dbody1,
  degree_dbody_wrt_dtyp 0 dbody1 ->
  degree_dbody_wrt_dexp 0 dbody1 ->
  lc_dbody dbody1.
Proof.
intros dbody1; intros;
pose proof (lc_dbody_of_degree_lc_dexp_of_degree_size_mutual (size_dbody dbody1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_dbody_of_degree : lngen.

Lemma lc_dexp_of_degree :
forall e1,
  degree_dexp_wrt_dtyp 0 e1 ->
  degree_dexp_wrt_dexp 0 e1 ->
  lc_dexp e1.
Proof.
intros e1; intros;
pose proof (lc_dbody_of_degree_lc_dexp_of_degree_size_mutual (size_dexp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_dexp_of_degree : lngen.

Ltac dtyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dtyp_wrt_dtyp_of_lc_dtyp in J1; clear H
          end).

Ltac binding_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_binding_wrt_dtyp_of_lc_binding in J1; clear H
          end).

Ltac dbody_dexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dbody_wrt_dtyp_of_lc_dbody in J1;
              let J2 := fresh in pose proof H as J2; apply degree_dbody_wrt_dexp_of_lc_dbody in J2; clear H
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dexp_wrt_dtyp_of_lc_dexp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_dexp_wrt_dexp_of_lc_dexp in J2; clear H
          end).

Lemma lc_dtyp_all_exists :
forall X1 T1,
  lc_dtyp (open_dtyp_wrt_dtyp T1 (dtyp_var_f X1)) ->
  lc_dtyp (dtyp_all T1).
Proof.
intros; dtyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_dexp_abs_exists :
forall x1 e1,
  lc_dexp (open_dexp_wrt_dexp e1 (dexp_var_f x1)) ->
  lc_dexp (dexp_abs e1).
Proof.
intros; dbody_dexp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_dexp_tabs_exists :
forall X1 dbody1,
  lc_dbody (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)) ->
  lc_dexp (dexp_tabs dbody1).
Proof.
intros; dbody_dexp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_dtyp (dtyp_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_dtyp_all_exists X1) : core.

#[export] Hint Extern 1 (lc_dexp (dexp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_dexp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_dexp (dexp_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_dexp_tabs_exists X1) : core.

Lemma lc_body_dtyp_wrt_dtyp :
forall T1 T2,
  body_dtyp_wrt_dtyp T1 ->
  lc_dtyp T2 ->
  lc_dtyp (open_dtyp_wrt_dtyp T1 T2).
Proof.
unfold body_dtyp_wrt_dtyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
dtyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dtyp_wrt_dtyp : lngen.

Lemma lc_body_binding_wrt_dtyp :
forall b1 T1,
  body_binding_wrt_dtyp b1 ->
  lc_dtyp T1 ->
  lc_binding (open_binding_wrt_dtyp b1 T1).
Proof.
unfold body_binding_wrt_dtyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
binding_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_binding_wrt_dtyp : lngen.

Lemma lc_body_dbody_wrt_dtyp :
forall dbody1 T1,
  body_dbody_wrt_dtyp dbody1 ->
  lc_dtyp T1 ->
  lc_dbody (open_dbody_wrt_dtyp dbody1 T1).
Proof.
unfold body_dbody_wrt_dtyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
dbody_dexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dbody_wrt_dtyp : lngen.

Lemma lc_body_dexp_wrt_dtyp :
forall e1 T1,
  body_dexp_wrt_dtyp e1 ->
  lc_dtyp T1 ->
  lc_dexp (open_dexp_wrt_dtyp e1 T1).
Proof.
unfold body_dexp_wrt_dtyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
dbody_dexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dexp_wrt_dtyp : lngen.

Lemma lc_body_dbody_wrt_dexp :
forall dbody1 e1,
  body_dbody_wrt_dexp dbody1 ->
  lc_dexp e1 ->
  lc_dbody (open_dbody_wrt_dexp dbody1 e1).
Proof.
unfold body_dbody_wrt_dexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
dbody_dexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dbody_wrt_dexp : lngen.

Lemma lc_body_dexp_wrt_dexp :
forall e1 e2,
  body_dexp_wrt_dexp e1 ->
  lc_dexp e2 ->
  lc_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold body_dexp_wrt_dexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
dbody_dexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dexp_wrt_dexp : lngen.

Lemma lc_body_dtyp_all_1 :
forall T1,
  lc_dtyp (dtyp_all T1) ->
  body_dtyp_wrt_dtyp T1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_dtyp_all_1 : lngen.

Lemma lc_body_dexp_abs_1 :
forall e1,
  lc_dexp (dexp_abs e1) ->
  body_dexp_wrt_dexp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_dexp_abs_1 : lngen.

Lemma lc_body_dexp_tabs_1 :
forall dbody1,
  lc_dexp (dexp_tabs dbody1) ->
  body_dbody_wrt_dtyp dbody1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_dexp_tabs_1 : lngen.

(* begin hide *)

Lemma lc_dtyp_unique_mutual :
(forall T1 (proof2 proof3 : lc_dtyp T1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dtyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dtyp_unique :
forall T1 (proof2 proof3 : lc_dtyp T1), proof2 = proof3.
Proof.
pose proof lc_dtyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dtyp_unique : lngen.

(* begin hide *)

Lemma lc_binding_unique_mutual :
(forall b1 (proof2 proof3 : lc_binding b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_binding_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_binding_unique :
forall b1 (proof2 proof3 : lc_binding b1), proof2 = proof3.
Proof.
pose proof lc_binding_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_binding_unique : lngen.

(* begin hide *)

Lemma lc_dbody_unique_lc_dexp_unique_mutual :
(forall dbody1 (proof2 proof3 : lc_dbody dbody1), proof2 = proof3) /\
(forall e1 (proof2 proof3 : lc_dexp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dbody_lc_dexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dbody_unique :
forall dbody1 (proof2 proof3 : lc_dbody dbody1), proof2 = proof3.
Proof.
pose proof lc_dbody_unique_lc_dexp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dbody_unique : lngen.

Lemma lc_dexp_unique :
forall e1 (proof2 proof3 : lc_dexp e1), proof2 = proof3.
Proof.
pose proof lc_dbody_unique_lc_dexp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dexp_unique : lngen.

(* begin hide *)

Lemma lc_dtyp_of_lc_set_dtyp_mutual :
(forall T1, lc_set_dtyp T1 -> lc_dtyp T1).
Proof.
apply_mutual_ind lc_set_dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dtyp_of_lc_set_dtyp :
forall T1, lc_set_dtyp T1 -> lc_dtyp T1.
Proof.
pose proof lc_dtyp_of_lc_set_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dtyp_of_lc_set_dtyp : lngen.

(* begin hide *)

Lemma lc_binding_of_lc_set_binding_mutual :
(forall b1, lc_set_binding b1 -> lc_binding b1).
Proof.
apply_mutual_ind lc_set_binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_binding_of_lc_set_binding :
forall b1, lc_set_binding b1 -> lc_binding b1.
Proof.
pose proof lc_binding_of_lc_set_binding_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_binding_of_lc_set_binding : lngen.

(* begin hide *)

Lemma lc_dbody_of_lc_set_dbody_lc_dexp_of_lc_set_dexp_mutual :
(forall dbody1, lc_set_dbody dbody1 -> lc_dbody dbody1) /\
(forall e1, lc_set_dexp e1 -> lc_dexp e1).
Proof.
apply_mutual_ind lc_set_dbody_lc_set_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dbody_of_lc_set_dbody :
forall dbody1, lc_set_dbody dbody1 -> lc_dbody dbody1.
Proof.
pose proof lc_dbody_of_lc_set_dbody_lc_dexp_of_lc_set_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dbody_of_lc_set_dbody : lngen.

Lemma lc_dexp_of_lc_set_dexp :
forall e1, lc_set_dexp e1 -> lc_dexp e1.
Proof.
pose proof lc_dbody_of_lc_set_dbody_lc_dexp_of_lc_set_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dexp_of_lc_set_dexp : lngen.

(* begin hide *)

Lemma lc_set_dtyp_of_lc_dtyp_size_mutual :
forall i1,
(forall T1,
  size_dtyp T1 = i1 ->
  lc_dtyp T1 ->
  lc_set_dtyp T1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dtyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_dtyp_of_lc_dtyp];
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

Lemma lc_set_dtyp_of_lc_dtyp :
forall T1,
  lc_dtyp T1 ->
  lc_set_dtyp T1.
Proof.
intros T1; intros;
pose proof (lc_set_dtyp_of_lc_dtyp_size_mutual (size_dtyp T1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_dtyp_of_lc_dtyp : lngen.

(* begin hide *)

Lemma lc_set_binding_of_lc_binding_size_mutual :
forall i1,
(forall b1,
  size_binding b1 = i1 ->
  lc_binding b1 ->
  lc_set_binding b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind binding_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_dtyp_of_lc_dtyp
 | apply lc_set_binding_of_lc_binding];
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

Lemma lc_set_binding_of_lc_binding :
forall b1,
  lc_binding b1 ->
  lc_set_binding b1.
Proof.
intros b1; intros;
pose proof (lc_set_binding_of_lc_binding_size_mutual (size_binding b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_binding_of_lc_binding : lngen.

(* begin hide *)

Lemma lc_set_dbody_of_lc_dbody_lc_set_dexp_of_lc_dexp_size_mutual :
forall i1,
(forall dbody1,
  size_dbody dbody1 = i1 ->
  lc_dbody dbody1 ->
  lc_set_dbody dbody1) *
(forall e1,
  size_dexp e1 = i1 ->
  lc_dexp e1 ->
  lc_set_dexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dbody_dexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_dtyp_of_lc_dtyp
 | apply lc_set_dbody_of_lc_dbody
 | apply lc_set_dexp_of_lc_dexp
 | apply lc_set_dtyp_of_lc_dtyp
 | apply lc_set_dbody_of_lc_dbody
 | apply lc_set_dexp_of_lc_dexp];
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

Lemma lc_set_dbody_of_lc_dbody :
forall dbody1,
  lc_dbody dbody1 ->
  lc_set_dbody dbody1.
Proof.
intros dbody1; intros;
pose proof (lc_set_dbody_of_lc_dbody_lc_set_dexp_of_lc_dexp_size_mutual (size_dbody dbody1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_dbody_of_lc_dbody : lngen.

Lemma lc_set_dexp_of_lc_dexp :
forall e1,
  lc_dexp e1 ->
  lc_set_dexp e1.
Proof.
intros e1; intros;
pose proof (lc_set_dbody_of_lc_dbody_lc_set_dexp_of_lc_dexp_size_mutual (size_dexp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_dexp_of_lc_dexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp_mutual :
(forall T1 X1 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  close_dtyp_wrt_dtyp_rec n1 X1 T1 = T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp :
forall T1 X1 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  close_dtyp_wrt_dtyp_rec n1 X1 T1 = T1.
Proof.
pose proof close_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp : lngen.
#[export] Hint Rewrite close_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp_mutual :
(forall b1 X1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  X1 `notin` ftv_in_binding b1 ->
  close_binding_wrt_dtyp_rec n1 X1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp :
forall b1 X1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  X1 `notin` ftv_in_binding b1 ->
  close_binding_wrt_dtyp_rec n1 X1 b1 = b1.
Proof.
pose proof close_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp : lngen.
#[export] Hint Rewrite close_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp_close_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp_mutual :
(forall dbody1 X1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  X1 `notin` ftv_in_dbody dbody1 ->
  close_dbody_wrt_dtyp_rec n1 X1 dbody1 = dbody1) /\
(forall e1 X1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  X1 `notin` ftv_in_dexp e1 ->
  close_dexp_wrt_dtyp_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp :
forall dbody1 X1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  X1 `notin` ftv_in_dbody dbody1 ->
  close_dbody_wrt_dtyp_rec n1 X1 dbody1 = dbody1.
Proof.
pose proof close_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp_close_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite close_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp :
forall e1 X1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  X1 `notin` ftv_in_dexp e1 ->
  close_dexp_wrt_dtyp_rec n1 X1 e1 = e1.
Proof.
pose proof close_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp_close_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite close_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp_close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual :
(forall dbody1 x1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  x1 `notin` fv_in_dbody dbody1 ->
  close_dbody_wrt_dexp_rec n1 x1 dbody1 = dbody1) /\
(forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 `notin` fv_in_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp :
forall dbody1 x1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  x1 `notin` fv_in_dbody dbody1 ->
  close_dbody_wrt_dexp_rec n1 x1 dbody1 = dbody1.
Proof.
pose proof close_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp_close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite close_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp :
forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 `notin` fv_in_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 e1 = e1.
Proof.
pose proof close_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp_close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp using solve [auto] : lngen.

(* end hide *)

Lemma close_dtyp_wrt_dtyp_lc_dtyp :
forall T1 X1,
  lc_dtyp T1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  close_dtyp_wrt_dtyp X1 T1 = T1.
Proof.
unfold close_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_dtyp_wrt_dtyp_lc_dtyp : lngen.
#[export] Hint Rewrite close_dtyp_wrt_dtyp_lc_dtyp using solve [auto] : lngen.

Lemma close_binding_wrt_dtyp_lc_binding :
forall b1 X1,
  lc_binding b1 ->
  X1 `notin` ftv_in_binding b1 ->
  close_binding_wrt_dtyp X1 b1 = b1.
Proof.
unfold close_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_binding_wrt_dtyp_lc_binding : lngen.
#[export] Hint Rewrite close_binding_wrt_dtyp_lc_binding using solve [auto] : lngen.

Lemma close_dbody_wrt_dtyp_lc_dbody :
forall dbody1 X1,
  lc_dbody dbody1 ->
  X1 `notin` ftv_in_dbody dbody1 ->
  close_dbody_wrt_dtyp X1 dbody1 = dbody1.
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_dbody_wrt_dtyp_lc_dbody : lngen.
#[export] Hint Rewrite close_dbody_wrt_dtyp_lc_dbody using solve [auto] : lngen.

Lemma close_dexp_wrt_dtyp_lc_dexp :
forall e1 X1,
  lc_dexp e1 ->
  X1 `notin` ftv_in_dexp e1 ->
  close_dexp_wrt_dtyp X1 e1 = e1.
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve close_dexp_wrt_dtyp_lc_dexp : lngen.
#[export] Hint Rewrite close_dexp_wrt_dtyp_lc_dexp using solve [auto] : lngen.

Lemma close_dbody_wrt_dexp_lc_dbody :
forall dbody1 x1,
  lc_dbody dbody1 ->
  x1 `notin` fv_in_dbody dbody1 ->
  close_dbody_wrt_dexp x1 dbody1 = dbody1.
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve close_dbody_wrt_dexp_lc_dbody : lngen.
#[export] Hint Rewrite close_dbody_wrt_dexp_lc_dbody using solve [auto] : lngen.

Lemma close_dexp_wrt_dexp_lc_dexp :
forall e1 x1,
  lc_dexp e1 ->
  x1 `notin` fv_in_dexp e1 ->
  close_dexp_wrt_dexp x1 e1 = e1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve close_dexp_wrt_dexp_lc_dexp : lngen.
#[export] Hint Rewrite close_dexp_wrt_dexp_lc_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp_mutual :
(forall T2 T1 n1,
  degree_dtyp_wrt_dtyp n1 T2 ->
  open_dtyp_wrt_dtyp_rec n1 T1 T2 = T2).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp :
forall T2 T1 n1,
  degree_dtyp_wrt_dtyp n1 T2 ->
  open_dtyp_wrt_dtyp_rec n1 T1 T2 = T2.
Proof.
pose proof open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp : lngen.
#[export] Hint Rewrite open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp_mutual :
(forall b1 T1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  open_binding_wrt_dtyp_rec n1 T1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp :
forall b1 T1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  open_binding_wrt_dtyp_rec n1 T1 b1 = b1.
Proof.
pose proof open_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp : lngen.
#[export] Hint Rewrite open_binding_wrt_dtyp_rec_degree_binding_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp_open_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp_mutual :
(forall dbody1 T1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  open_dbody_wrt_dtyp_rec n1 T1 dbody1 = dbody1) /\
(forall e1 T1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  open_dexp_wrt_dtyp_rec n1 T1 e1 = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp :
forall dbody1 T1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  open_dbody_wrt_dtyp_rec n1 T1 dbody1 = dbody1.
Proof.
pose proof open_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp_open_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite open_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp :
forall e1 T1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  open_dexp_wrt_dtyp_rec n1 T1 e1 = e1.
Proof.
pose proof open_dbody_wrt_dtyp_rec_degree_dbody_wrt_dtyp_open_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite open_dexp_wrt_dtyp_rec_degree_dexp_wrt_dtyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp_open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual :
(forall dbody1 e1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  open_dbody_wrt_dexp_rec n1 e1 dbody1 = dbody1) /\
(forall e2 e1 n1,
  degree_dexp_wrt_dexp n1 e2 ->
  open_dexp_wrt_dexp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp :
forall dbody1 e1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  open_dbody_wrt_dexp_rec n1 e1 dbody1 = dbody1.
Proof.
pose proof open_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp_open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite open_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp :
forall e2 e1 n1,
  degree_dexp_wrt_dexp n1 e2 ->
  open_dexp_wrt_dexp_rec n1 e1 e2 = e2.
Proof.
pose proof open_dbody_wrt_dexp_rec_degree_dbody_wrt_dexp_open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp using solve [auto] : lngen.

(* end hide *)

Lemma open_dtyp_wrt_dtyp_lc_dtyp :
forall T2 T1,
  lc_dtyp T2 ->
  open_dtyp_wrt_dtyp T2 T1 = T2.
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_dtyp_wrt_dtyp_lc_dtyp : lngen.
#[export] Hint Rewrite open_dtyp_wrt_dtyp_lc_dtyp using solve [auto] : lngen.

Lemma open_binding_wrt_dtyp_lc_binding :
forall b1 T1,
  lc_binding b1 ->
  open_binding_wrt_dtyp b1 T1 = b1.
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_binding_wrt_dtyp_lc_binding : lngen.
#[export] Hint Rewrite open_binding_wrt_dtyp_lc_binding using solve [auto] : lngen.

Lemma open_dbody_wrt_dtyp_lc_dbody :
forall dbody1 T1,
  lc_dbody dbody1 ->
  open_dbody_wrt_dtyp dbody1 T1 = dbody1.
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_dbody_wrt_dtyp_lc_dbody : lngen.
#[export] Hint Rewrite open_dbody_wrt_dtyp_lc_dbody using solve [auto] : lngen.

Lemma open_dexp_wrt_dtyp_lc_dexp :
forall e1 T1,
  lc_dexp e1 ->
  open_dexp_wrt_dtyp e1 T1 = e1.
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve open_dexp_wrt_dtyp_lc_dexp : lngen.
#[export] Hint Rewrite open_dexp_wrt_dtyp_lc_dexp using solve [auto] : lngen.

Lemma open_dbody_wrt_dexp_lc_dbody :
forall dbody1 e1,
  lc_dbody dbody1 ->
  open_dbody_wrt_dexp dbody1 e1 = dbody1.
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve open_dbody_wrt_dexp_lc_dbody : lngen.
#[export] Hint Rewrite open_dbody_wrt_dexp_lc_dbody using solve [auto] : lngen.

Lemma open_dexp_wrt_dexp_lc_dexp :
forall e2 e1,
  lc_dexp e2 ->
  open_dexp_wrt_dexp e2 e1 = e2.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve open_dexp_wrt_dexp_lc_dexp : lngen.
#[export] Hint Rewrite open_dexp_wrt_dexp_lc_dexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftv_in_dtyp_close_dtyp_wrt_dtyp_rec_mutual :
(forall T1 X1 n1,
  ftv_in_dtyp (close_dtyp_wrt_dtyp_rec n1 X1 T1) [=] remove X1 (ftv_in_dtyp T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dtyp_close_dtyp_wrt_dtyp_rec :
forall T1 X1 n1,
  ftv_in_dtyp (close_dtyp_wrt_dtyp_rec n1 X1 T1) [=] remove X1 (ftv_in_dtyp T1).
Proof.
pose proof ftv_in_dtyp_close_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_close_dtyp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite ftv_in_dtyp_close_dtyp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_binding_close_binding_wrt_dtyp_rec_mutual :
(forall b1 X1 n1,
  ftv_in_binding (close_binding_wrt_dtyp_rec n1 X1 b1) [=] remove X1 (ftv_in_binding b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_binding_close_binding_wrt_dtyp_rec :
forall b1 X1 n1,
  ftv_in_binding (close_binding_wrt_dtyp_rec n1 X1 b1) [=] remove X1 (ftv_in_binding b1).
Proof.
pose proof ftv_in_binding_close_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_close_binding_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite ftv_in_binding_close_binding_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_close_dbody_wrt_dtyp_rec_ftv_in_dexp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1,
  ftv_in_dbody (close_dbody_wrt_dtyp_rec n1 X1 dbody1) [=] remove X1 (ftv_in_dbody dbody1)) /\
(forall e1 X1 n1,
  ftv_in_dexp (close_dexp_wrt_dtyp_rec n1 X1 e1) [=] remove X1 (ftv_in_dexp e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_close_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1,
  ftv_in_dbody (close_dbody_wrt_dtyp_rec n1 X1 dbody1) [=] remove X1 (ftv_in_dbody dbody1).
Proof.
pose proof ftv_in_dbody_close_dbody_wrt_dtyp_rec_ftv_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_close_dbody_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite ftv_in_dbody_close_dbody_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dexp_close_dexp_wrt_dtyp_rec :
forall e1 X1 n1,
  ftv_in_dexp (close_dexp_wrt_dtyp_rec n1 X1 e1) [=] remove X1 (ftv_in_dexp e1).
Proof.
pose proof ftv_in_dbody_close_dbody_wrt_dtyp_rec_ftv_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_close_dexp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite ftv_in_dexp_close_dexp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_close_dbody_wrt_dexp_rec_ftv_in_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1,
  ftv_in_dbody (close_dbody_wrt_dexp_rec n1 x1 dbody1) [=] ftv_in_dbody dbody1) /\
(forall e1 x1 n1,
  ftv_in_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) [=] ftv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_close_dbody_wrt_dexp_rec :
forall dbody1 x1 n1,
  ftv_in_dbody (close_dbody_wrt_dexp_rec n1 x1 dbody1) [=] ftv_in_dbody dbody1.
Proof.
pose proof ftv_in_dbody_close_dbody_wrt_dexp_rec_ftv_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_close_dbody_wrt_dexp_rec : lngen.
#[export] Hint Rewrite ftv_in_dbody_close_dbody_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  ftv_in_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) [=] ftv_in_dexp e1.
Proof.
pose proof ftv_in_dbody_close_dbody_wrt_dexp_rec_ftv_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_close_dexp_wrt_dexp_rec : lngen.
#[export] Hint Rewrite ftv_in_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_close_dbody_wrt_dtyp_rec_fv_in_dexp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 X1 n1,
  fv_in_dbody (close_dbody_wrt_dtyp_rec n1 X1 dbody1) [=] fv_in_dbody dbody1) /\
(forall e1 X1 n1,
  fv_in_dexp (close_dexp_wrt_dtyp_rec n1 X1 e1) [=] fv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_close_dbody_wrt_dtyp_rec :
forall dbody1 X1 n1,
  fv_in_dbody (close_dbody_wrt_dtyp_rec n1 X1 dbody1) [=] fv_in_dbody dbody1.
Proof.
pose proof fv_in_dbody_close_dbody_wrt_dtyp_rec_fv_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_close_dbody_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite fv_in_dbody_close_dbody_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dexp_close_dexp_wrt_dtyp_rec :
forall e1 X1 n1,
  fv_in_dexp (close_dexp_wrt_dtyp_rec n1 X1 e1) [=] fv_in_dexp e1.
Proof.
pose proof fv_in_dbody_close_dbody_wrt_dtyp_rec_fv_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_close_dexp_wrt_dtyp_rec : lngen.
#[export] Hint Rewrite fv_in_dexp_close_dexp_wrt_dtyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_close_dbody_wrt_dexp_rec_fv_in_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 x1 n1,
  fv_in_dbody (close_dbody_wrt_dexp_rec n1 x1 dbody1) [=] remove x1 (fv_in_dbody dbody1)) /\
(forall e1 x1 n1,
  fv_in_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) [=] remove x1 (fv_in_dexp e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_close_dbody_wrt_dexp_rec :
forall dbody1 x1 n1,
  fv_in_dbody (close_dbody_wrt_dexp_rec n1 x1 dbody1) [=] remove x1 (fv_in_dbody dbody1).
Proof.
pose proof fv_in_dbody_close_dbody_wrt_dexp_rec_fv_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_close_dbody_wrt_dexp_rec : lngen.
#[export] Hint Rewrite fv_in_dbody_close_dbody_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  fv_in_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) [=] remove x1 (fv_in_dexp e1).
Proof.
pose proof fv_in_dbody_close_dbody_wrt_dexp_rec_fv_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_close_dexp_wrt_dexp_rec : lngen.
#[export] Hint Rewrite fv_in_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftv_in_dtyp_close_dtyp_wrt_dtyp :
forall T1 X1,
  ftv_in_dtyp (close_dtyp_wrt_dtyp X1 T1) [=] remove X1 (ftv_in_dtyp T1).
Proof.
unfold close_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dtyp_close_dtyp_wrt_dtyp : lngen.
#[export] Hint Rewrite ftv_in_dtyp_close_dtyp_wrt_dtyp using solve [auto] : lngen.

Lemma ftv_in_binding_close_binding_wrt_dtyp :
forall b1 X1,
  ftv_in_binding (close_binding_wrt_dtyp X1 b1) [=] remove X1 (ftv_in_binding b1).
Proof.
unfold close_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_binding_close_binding_wrt_dtyp : lngen.
#[export] Hint Rewrite ftv_in_binding_close_binding_wrt_dtyp using solve [auto] : lngen.

Lemma ftv_in_dbody_close_dbody_wrt_dtyp :
forall dbody1 X1,
  ftv_in_dbody (close_dbody_wrt_dtyp X1 dbody1) [=] remove X1 (ftv_in_dbody dbody1).
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dbody_close_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite ftv_in_dbody_close_dbody_wrt_dtyp using solve [auto] : lngen.

Lemma ftv_in_dexp_close_dexp_wrt_dtyp :
forall e1 X1,
  ftv_in_dexp (close_dexp_wrt_dtyp X1 e1) [=] remove X1 (ftv_in_dexp e1).
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dexp_close_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite ftv_in_dexp_close_dexp_wrt_dtyp using solve [auto] : lngen.

Lemma ftv_in_dbody_close_dbody_wrt_dexp :
forall dbody1 x1,
  ftv_in_dbody (close_dbody_wrt_dexp x1 dbody1) [=] ftv_in_dbody dbody1.
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dbody_close_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite ftv_in_dbody_close_dbody_wrt_dexp using solve [auto] : lngen.

Lemma ftv_in_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  ftv_in_dexp (close_dexp_wrt_dexp x1 e1) [=] ftv_in_dexp e1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dexp_close_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite ftv_in_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

Lemma fv_in_dbody_close_dbody_wrt_dtyp :
forall dbody1 X1,
  fv_in_dbody (close_dbody_wrt_dtyp X1 dbody1) [=] fv_in_dbody dbody1.
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dbody_close_dbody_wrt_dtyp : lngen.
#[export] Hint Rewrite fv_in_dbody_close_dbody_wrt_dtyp using solve [auto] : lngen.

Lemma fv_in_dexp_close_dexp_wrt_dtyp :
forall e1 X1,
  fv_in_dexp (close_dexp_wrt_dtyp X1 e1) [=] fv_in_dexp e1.
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dexp_close_dexp_wrt_dtyp : lngen.
#[export] Hint Rewrite fv_in_dexp_close_dexp_wrt_dtyp using solve [auto] : lngen.

Lemma fv_in_dbody_close_dbody_wrt_dexp :
forall dbody1 x1,
  fv_in_dbody (close_dbody_wrt_dexp x1 dbody1) [=] remove x1 (fv_in_dbody dbody1).
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dbody_close_dbody_wrt_dexp : lngen.
#[export] Hint Rewrite fv_in_dbody_close_dbody_wrt_dexp using solve [auto] : lngen.

Lemma fv_in_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  fv_in_dexp (close_dexp_wrt_dexp x1 e1) [=] remove x1 (fv_in_dexp e1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dexp_close_dexp_wrt_dexp : lngen.
#[export] Hint Rewrite fv_in_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_lower_mutual :
(forall T1 T2 n1,
  ftv_in_dtyp T1 [<=] ftv_in_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_lower :
forall T1 T2 n1,
  ftv_in_dtyp T1 [<=] ftv_in_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1).
Proof.
pose proof ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_binding_open_binding_wrt_dtyp_rec_lower_mutual :
(forall b1 T1 n1,
  ftv_in_binding b1 [<=] ftv_in_binding (open_binding_wrt_dtyp_rec n1 T1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_binding_open_binding_wrt_dtyp_rec_lower :
forall b1 T1 n1,
  ftv_in_binding b1 [<=] ftv_in_binding (open_binding_wrt_dtyp_rec n1 T1 b1).
Proof.
pose proof ftv_in_binding_open_binding_wrt_dtyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_open_binding_wrt_dtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dtyp_rec_lower_ftv_in_dexp_open_dexp_wrt_dtyp_rec_lower_mutual :
(forall dbody1 T1 n1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1)) /\
(forall e1 T1 n1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dtyp_rec_lower :
forall dbody1 T1 n1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1).
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dtyp_rec_lower_ftv_in_dexp_open_dexp_wrt_dtyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dexp_open_dexp_wrt_dtyp_rec_lower :
forall e1 T1 n1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1).
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dtyp_rec_lower_ftv_in_dexp_open_dexp_wrt_dtyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dexp_rec_lower_ftv_in_dexp_open_dexp_wrt_dexp_rec_lower_mutual :
(forall dbody1 e1 n1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1)) /\
(forall e1 e2 n1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dexp_rec_lower :
forall dbody1 e1 n1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1).
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dexp_rec_lower_ftv_in_dexp_open_dexp_wrt_dexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dexp_open_dexp_wrt_dexp_rec_lower :
forall e1 e2 n1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dexp_rec_lower_ftv_in_dexp_open_dexp_wrt_dexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dtyp_rec_lower_fv_in_dexp_open_dexp_wrt_dtyp_rec_lower_mutual :
(forall dbody1 T1 n1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1)) /\
(forall e1 T1 n1,
  fv_in_dexp e1 [<=] fv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dtyp_rec_lower :
forall dbody1 T1 n1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1).
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dtyp_rec_lower_fv_in_dexp_open_dexp_wrt_dtyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dexp_open_dexp_wrt_dtyp_rec_lower :
forall e1 T1 n1,
  fv_in_dexp e1 [<=] fv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1).
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dtyp_rec_lower_fv_in_dexp_open_dexp_wrt_dtyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dtyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dexp_rec_lower_fv_in_dexp_open_dexp_wrt_dexp_rec_lower_mutual :
(forall dbody1 e1 n1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1)) /\
(forall e1 e2 n1,
  fv_in_dexp e1 [<=] fv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dexp_rec_lower :
forall dbody1 e1 n1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1).
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dexp_rec_lower_fv_in_dexp_open_dexp_wrt_dexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dexp_open_dexp_wrt_dexp_rec_lower :
forall e1 e2 n1,
  fv_in_dexp e1 [<=] fv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dexp_rec_lower_fv_in_dexp_open_dexp_wrt_dexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dexp_rec_lower : lngen.

(* end hide *)

Lemma ftv_in_dtyp_open_dtyp_wrt_dtyp_lower :
forall T1 T2,
  ftv_in_dtyp T1 [<=] ftv_in_dtyp (open_dtyp_wrt_dtyp T1 T2).
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dtyp_open_dtyp_wrt_dtyp_lower : lngen.

Lemma ftv_in_binding_open_binding_wrt_dtyp_lower :
forall b1 T1,
  ftv_in_binding b1 [<=] ftv_in_binding (open_binding_wrt_dtyp b1 T1).
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_binding_open_binding_wrt_dtyp_lower : lngen.

Lemma ftv_in_dbody_open_dbody_wrt_dtyp_lower :
forall dbody1 T1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (open_dbody_wrt_dtyp dbody1 T1).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dtyp_lower : lngen.

Lemma ftv_in_dexp_open_dexp_wrt_dtyp_lower :
forall e1 T1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (open_dexp_wrt_dtyp e1 T1).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dtyp_lower : lngen.

Lemma ftv_in_dbody_open_dbody_wrt_dexp_lower :
forall dbody1 e1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (open_dbody_wrt_dexp dbody1 e1).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dexp_lower : lngen.

Lemma ftv_in_dexp_open_dexp_wrt_dexp_lower :
forall e1 e2,
  ftv_in_dexp e1 [<=] ftv_in_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dexp_lower : lngen.

Lemma fv_in_dbody_open_dbody_wrt_dtyp_lower :
forall dbody1 T1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (open_dbody_wrt_dtyp dbody1 T1).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dtyp_lower : lngen.

Lemma fv_in_dexp_open_dexp_wrt_dtyp_lower :
forall e1 T1,
  fv_in_dexp e1 [<=] fv_in_dexp (open_dexp_wrt_dtyp e1 T1).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dtyp_lower : lngen.

Lemma fv_in_dbody_open_dbody_wrt_dexp_lower :
forall dbody1 e1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (open_dbody_wrt_dexp dbody1 e1).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dexp_lower : lngen.

Lemma fv_in_dexp_open_dexp_wrt_dexp_lower :
forall e1 e2,
  fv_in_dexp e1 [<=] fv_in_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dexp_lower : lngen.

(* begin hide *)

Lemma ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper_mutual :
(forall T1 T2 n1,
  ftv_in_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1) [<=] ftv_in_dtyp T2 `union` ftv_in_dtyp T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper :
forall T1 T2 n1,
  ftv_in_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1) [<=] ftv_in_dtyp T2 `union` ftv_in_dtyp T1.
Proof.
pose proof ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_binding_open_binding_wrt_dtyp_rec_upper_mutual :
(forall b1 T1 n1,
  ftv_in_binding (open_binding_wrt_dtyp_rec n1 T1 b1) [<=] ftv_in_dtyp T1 `union` ftv_in_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_binding_open_binding_wrt_dtyp_rec_upper :
forall b1 T1 n1,
  ftv_in_binding (open_binding_wrt_dtyp_rec n1 T1 b1) [<=] ftv_in_dtyp T1 `union` ftv_in_binding b1.
Proof.
pose proof ftv_in_binding_open_binding_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_open_binding_wrt_dtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dtyp_rec_upper_ftv_in_dexp_open_dexp_wrt_dtyp_rec_upper_mutual :
(forall dbody1 T1 n1,
  ftv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1) [<=] ftv_in_dtyp T1 `union` ftv_in_dbody dbody1) /\
(forall e1 T1 n1,
  ftv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1) [<=] ftv_in_dtyp T1 `union` ftv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dtyp_rec_upper :
forall dbody1 T1 n1,
  ftv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1) [<=] ftv_in_dtyp T1 `union` ftv_in_dbody dbody1.
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dtyp_rec_upper_ftv_in_dexp_open_dexp_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dexp_open_dexp_wrt_dtyp_rec_upper :
forall e1 T1 n1,
  ftv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1) [<=] ftv_in_dtyp T1 `union` ftv_in_dexp e1.
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dtyp_rec_upper_ftv_in_dexp_open_dexp_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dexp_rec_upper_ftv_in_dexp_open_dexp_wrt_dexp_rec_upper_mutual :
(forall dbody1 e1 n1,
  ftv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1) [<=] ftv_in_dexp e1 `union` ftv_in_dbody dbody1) /\
(forall e1 e2 n1,
  ftv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1) [<=] ftv_in_dexp e2 `union` ftv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dbody_open_dbody_wrt_dexp_rec_upper :
forall dbody1 e1 n1,
  ftv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1) [<=] ftv_in_dexp e1 `union` ftv_in_dbody dbody1.
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dexp_rec_upper_ftv_in_dexp_open_dexp_wrt_dexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftv_in_dexp_open_dexp_wrt_dexp_rec_upper :
forall e1 e2 n1,
  ftv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1) [<=] ftv_in_dexp e2 `union` ftv_in_dexp e1.
Proof.
pose proof ftv_in_dbody_open_dbody_wrt_dexp_rec_upper_ftv_in_dexp_open_dexp_wrt_dexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dtyp_rec_upper_fv_in_dexp_open_dexp_wrt_dtyp_rec_upper_mutual :
(forall dbody1 T1 n1,
  fv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1) [<=] fv_in_dbody dbody1) /\
(forall e1 T1 n1,
  fv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1) [<=] fv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dtyp_rec_upper :
forall dbody1 T1 n1,
  fv_in_dbody (open_dbody_wrt_dtyp_rec n1 T1 dbody1) [<=] fv_in_dbody dbody1.
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dtyp_rec_upper_fv_in_dexp_open_dexp_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dexp_open_dexp_wrt_dtyp_rec_upper :
forall e1 T1 n1,
  fv_in_dexp (open_dexp_wrt_dtyp_rec n1 T1 e1) [<=] fv_in_dexp e1.
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dtyp_rec_upper_fv_in_dexp_open_dexp_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dtyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dexp_rec_upper_fv_in_dexp_open_dexp_wrt_dexp_rec_upper_mutual :
(forall dbody1 e1 n1,
  fv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1) [<=] fv_in_dexp e1 `union` fv_in_dbody dbody1) /\
(forall e1 e2 n1,
  fv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1) [<=] fv_in_dexp e2 `union` fv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_in_dbody_open_dbody_wrt_dexp_rec_upper :
forall dbody1 e1 n1,
  fv_in_dbody (open_dbody_wrt_dexp_rec n1 e1 dbody1) [<=] fv_in_dexp e1 `union` fv_in_dbody dbody1.
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dexp_rec_upper_fv_in_dexp_open_dexp_wrt_dexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_in_dexp_open_dexp_wrt_dexp_rec_upper :
forall e1 e2 n1,
  fv_in_dexp (open_dexp_wrt_dexp_rec n1 e2 e1) [<=] fv_in_dexp e2 `union` fv_in_dexp e1.
Proof.
pose proof fv_in_dbody_open_dbody_wrt_dexp_rec_upper_fv_in_dexp_open_dexp_wrt_dexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dexp_rec_upper : lngen.

(* end hide *)

Lemma ftv_in_dtyp_open_dtyp_wrt_dtyp_upper :
forall T1 T2,
  ftv_in_dtyp (open_dtyp_wrt_dtyp T1 T2) [<=] ftv_in_dtyp T2 `union` ftv_in_dtyp T1.
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dtyp_open_dtyp_wrt_dtyp_upper : lngen.

Lemma ftv_in_binding_open_binding_wrt_dtyp_upper :
forall b1 T1,
  ftv_in_binding (open_binding_wrt_dtyp b1 T1) [<=] ftv_in_dtyp T1 `union` ftv_in_binding b1.
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_binding_open_binding_wrt_dtyp_upper : lngen.

Lemma ftv_in_dbody_open_dbody_wrt_dtyp_upper :
forall dbody1 T1,
  ftv_in_dbody (open_dbody_wrt_dtyp dbody1 T1) [<=] ftv_in_dtyp T1 `union` ftv_in_dbody dbody1.
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dtyp_upper : lngen.

Lemma ftv_in_dexp_open_dexp_wrt_dtyp_upper :
forall e1 T1,
  ftv_in_dexp (open_dexp_wrt_dtyp e1 T1) [<=] ftv_in_dtyp T1 `union` ftv_in_dexp e1.
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dtyp_upper : lngen.

Lemma ftv_in_dbody_open_dbody_wrt_dexp_upper :
forall dbody1 e1,
  ftv_in_dbody (open_dbody_wrt_dexp dbody1 e1) [<=] ftv_in_dexp e1 `union` ftv_in_dbody dbody1.
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dbody_open_dbody_wrt_dexp_upper : lngen.

Lemma ftv_in_dexp_open_dexp_wrt_dexp_upper :
forall e1 e2,
  ftv_in_dexp (open_dexp_wrt_dexp e1 e2) [<=] ftv_in_dexp e2 `union` ftv_in_dexp e1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve ftv_in_dexp_open_dexp_wrt_dexp_upper : lngen.

Lemma fv_in_dbody_open_dbody_wrt_dtyp_upper :
forall dbody1 T1,
  fv_in_dbody (open_dbody_wrt_dtyp dbody1 T1) [<=] fv_in_dbody dbody1.
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dtyp_upper : lngen.

Lemma fv_in_dexp_open_dexp_wrt_dtyp_upper :
forall e1 T1,
  fv_in_dexp (open_dexp_wrt_dtyp e1 T1) [<=] fv_in_dexp e1.
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dtyp_upper : lngen.

Lemma fv_in_dbody_open_dbody_wrt_dexp_upper :
forall dbody1 e1,
  fv_in_dbody (open_dbody_wrt_dexp dbody1 e1) [<=] fv_in_dexp e1 `union` fv_in_dbody dbody1.
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dbody_open_dbody_wrt_dexp_upper : lngen.

Lemma fv_in_dexp_open_dexp_wrt_dexp_upper :
forall e1 e2,
  fv_in_dexp (open_dexp_wrt_dexp e1 e2) [<=] fv_in_dexp e2 `union` fv_in_dexp e1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve fv_in_dexp_open_dexp_wrt_dexp_upper : lngen.

(* begin hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_fresh_mutual :
(forall T1 T2 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1) [=] ftv_in_dtyp T1).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_fresh :
forall T1 T2 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1) [=] ftv_in_dtyp T1.
Proof.
pose proof ftv_in_dtyp_d_subst_tv_in_dtyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_d_subst_tv_in_dtyp_fresh : lngen.
#[export] Hint Rewrite ftv_in_dtyp_d_subst_tv_in_dtyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_fresh_mutual :
(forall b1 T1 X1,
  X1 `notin` ftv_in_binding b1 ->
  ftv_in_binding (d_subst_tv_in_binding T1 X1 b1) [=] ftv_in_binding b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_fresh :
forall b1 T1 X1,
  X1 `notin` ftv_in_binding b1 ->
  ftv_in_binding (d_subst_tv_in_binding T1 X1 b1) [=] ftv_in_binding b1.
Proof.
pose proof ftv_in_binding_d_subst_tv_in_binding_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_d_subst_tv_in_binding_fresh : lngen.
#[export] Hint Rewrite ftv_in_binding_d_subst_tv_in_binding_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_fresh_ftv_in_dexp_d_subst_tv_in_dexp_fresh_mutual :
(forall dbody1 T1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [=] ftv_in_dbody dbody1) /\
(forall e1 T1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [=] ftv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_fresh :
forall dbody1 T1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [=] ftv_in_dbody dbody1.
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_fresh_ftv_in_dexp_d_subst_tv_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_tv_in_dbody_fresh : lngen.
#[export] Hint Rewrite ftv_in_dbody_d_subst_tv_in_dbody_fresh using solve [auto] : lngen.

Lemma ftv_in_dexp_d_subst_tv_in_dexp_fresh :
forall e1 T1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [=] ftv_in_dexp e1.
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_fresh_ftv_in_dexp_d_subst_tv_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_tv_in_dexp_fresh : lngen.
#[export] Hint Rewrite ftv_in_dexp_d_subst_tv_in_dexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_fresh_ftv_in_dexp_d_subst_v_in_dexp_fresh_mutual :
(forall dbody1 T1 X1,
  fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [=] fv_in_dbody dbody1) /\
(forall e1 T1 X1,
  fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [=] fv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_fresh :
forall dbody1 T1 X1,
  fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [=] fv_in_dbody dbody1.
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_fresh_ftv_in_dexp_d_subst_v_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_v_in_dbody_fresh : lngen.
#[export] Hint Rewrite ftv_in_dbody_d_subst_v_in_dbody_fresh using solve [auto] : lngen.

Lemma ftv_in_dexp_d_subst_v_in_dexp_fresh :
forall e1 T1 X1,
  fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [=] fv_in_dexp e1.
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_fresh_ftv_in_dexp_d_subst_v_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_v_in_dexp_fresh : lngen.
#[export] Hint Rewrite ftv_in_dexp_d_subst_v_in_dexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_fresh_fv_in_dexp_d_subst_v_in_dexp_fresh_mutual :
(forall dbody1 e1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1) [=] fv_in_dbody dbody1) /\
(forall e1 e2 x1,
  x1 `notin` fv_in_dexp e1 ->
  fv_in_dexp (d_subst_v_in_dexp e2 x1 e1) [=] fv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_fresh :
forall dbody1 e1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1) [=] fv_in_dbody dbody1.
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_fresh_fv_in_dexp_d_subst_v_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_v_in_dbody_fresh : lngen.
#[export] Hint Rewrite fv_in_dbody_d_subst_v_in_dbody_fresh using solve [auto] : lngen.

Lemma fv_in_dexp_d_subst_v_in_dexp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_in_dexp e1 ->
  fv_in_dexp (d_subst_v_in_dexp e2 x1 e1) [=] fv_in_dexp e1.
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_fresh_fv_in_dexp_d_subst_v_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_v_in_dexp_fresh : lngen.
#[export] Hint Rewrite fv_in_dexp_d_subst_v_in_dexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_lower_mutual :
(forall T1 T2 X1,
  remove X1 (ftv_in_dtyp T1) [<=] ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_lower :
forall T1 T2 X1,
  remove X1 (ftv_in_dtyp T1) [<=] ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1).
Proof.
pose proof ftv_in_dtyp_d_subst_tv_in_dtyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_d_subst_tv_in_dtyp_lower : lngen.

(* begin hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_lower_mutual :
(forall b1 T1 X1,
  remove X1 (ftv_in_binding b1) [<=] ftv_in_binding (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_lower :
forall b1 T1 X1,
  remove X1 (ftv_in_binding b1) [<=] ftv_in_binding (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof ftv_in_binding_d_subst_tv_in_binding_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_d_subst_tv_in_binding_lower : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_lower_ftv_in_dexp_d_subst_tv_in_dexp_lower_mutual :
(forall dbody1 T1 X1,
  remove X1 (ftv_in_dbody dbody1) [<=] ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1,
  remove X1 (ftv_in_dexp e1) [<=] ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_lower :
forall dbody1 T1 X1,
  remove X1 (ftv_in_dbody dbody1) [<=] ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_lower_ftv_in_dexp_d_subst_tv_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_tv_in_dbody_lower : lngen.

Lemma ftv_in_dexp_d_subst_tv_in_dexp_lower :
forall e1 T1 X1,
  remove X1 (ftv_in_dexp e1) [<=] ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_lower_ftv_in_dexp_d_subst_tv_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_tv_in_dexp_lower : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_lower_ftv_in_dexp_d_subst_v_in_dexp_lower_mutual :
(forall dbody1 e1 x1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 x1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_lower :
forall dbody1 e1 x1,
  ftv_in_dbody dbody1 [<=] ftv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_lower_ftv_in_dexp_d_subst_v_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_v_in_dbody_lower : lngen.

Lemma ftv_in_dexp_d_subst_v_in_dexp_lower :
forall e1 e2 x1,
  ftv_in_dexp e1 [<=] ftv_in_dexp (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_lower_ftv_in_dexp_d_subst_v_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_v_in_dexp_lower : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_tv_in_dbody_lower_fv_in_dexp_d_subst_tv_in_dexp_lower_mutual :
(forall dbody1 T1 X1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1,
  fv_in_dexp e1 [<=] fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_tv_in_dbody_lower :
forall dbody1 T1 X1,
  fv_in_dbody dbody1 [<=] fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof fv_in_dbody_d_subst_tv_in_dbody_lower_fv_in_dexp_d_subst_tv_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_tv_in_dbody_lower : lngen.

Lemma fv_in_dexp_d_subst_tv_in_dexp_lower :
forall e1 T1 X1,
  fv_in_dexp e1 [<=] fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof fv_in_dbody_d_subst_tv_in_dbody_lower_fv_in_dexp_d_subst_tv_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_tv_in_dexp_lower : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_lower_fv_in_dexp_d_subst_v_in_dexp_lower_mutual :
(forall dbody1 e1 x1,
  remove x1 (fv_in_dbody dbody1) [<=] fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 x1,
  remove x1 (fv_in_dexp e1) [<=] fv_in_dexp (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_lower :
forall dbody1 e1 x1,
  remove x1 (fv_in_dbody dbody1) [<=] fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_lower_fv_in_dexp_d_subst_v_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_v_in_dbody_lower : lngen.

Lemma fv_in_dexp_d_subst_v_in_dexp_lower :
forall e1 e2 x1,
  remove x1 (fv_in_dexp e1) [<=] fv_in_dexp (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_lower_fv_in_dexp_d_subst_v_in_dexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_v_in_dexp_lower : lngen.

(* begin hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_notin_mutual :
(forall T1 T2 X1 X2,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_dtyp T2 ->
  X2 `notin` ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_notin :
forall T1 T2 X1 X2,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_dtyp T2 ->
  X2 `notin` ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1).
Proof.
pose proof ftv_in_dtyp_d_subst_tv_in_dtyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_d_subst_tv_in_dtyp_notin : lngen.

(* begin hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_notin_mutual :
(forall b1 T1 X1 X2,
  X2 `notin` ftv_in_binding b1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_binding (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_notin :
forall b1 T1 X1 X2,
  X2 `notin` ftv_in_binding b1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_binding (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof ftv_in_binding_d_subst_tv_in_binding_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_d_subst_tv_in_binding_notin : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_notin_ftv_in_dexp_d_subst_tv_in_dexp_notin_mutual :
(forall dbody1 T1 X1 X2,
  X2 `notin` ftv_in_dbody dbody1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1 X2,
  X2 `notin` ftv_in_dexp e1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_notin :
forall dbody1 T1 X1 X2,
  X2 `notin` ftv_in_dbody dbody1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_notin_ftv_in_dexp_d_subst_tv_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_tv_in_dbody_notin : lngen.

Lemma ftv_in_dexp_d_subst_tv_in_dexp_notin :
forall e1 T1 X1 X2,
  X2 `notin` ftv_in_dexp e1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 `notin` ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_notin_ftv_in_dexp_d_subst_tv_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_tv_in_dexp_notin : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_notin_ftv_in_dexp_d_subst_v_in_dexp_notin_mutual :
(forall dbody1 e1 x1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dexp e1 ->
  X1 `notin` ftv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 x1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_notin :
forall dbody1 e1 x1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dexp e1 ->
  X1 `notin` ftv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_notin_ftv_in_dexp_d_subst_v_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_v_in_dbody_notin : lngen.

Lemma ftv_in_dexp_d_subst_v_in_dexp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_notin_ftv_in_dexp_d_subst_v_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_v_in_dexp_notin : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_tv_in_dbody_notin_fv_in_dexp_d_subst_tv_in_dexp_notin_mutual :
(forall dbody1 T1 X1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  x1 `notin` fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1 x1,
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_tv_in_dbody_notin :
forall dbody1 T1 X1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  x1 `notin` fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof fv_in_dbody_d_subst_tv_in_dbody_notin_fv_in_dexp_d_subst_tv_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_tv_in_dbody_notin : lngen.

Lemma fv_in_dexp_d_subst_tv_in_dexp_notin :
forall e1 T1 X1 x1,
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof fv_in_dbody_d_subst_tv_in_dbody_notin_fv_in_dexp_d_subst_tv_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_tv_in_dexp_notin : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_notin_fv_in_dexp_d_subst_v_in_dexp_notin_mutual :
(forall dbody1 e1 x1 x2,
  x2 `notin` fv_in_dbody dbody1 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 `notin` fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 x1 x2,
  x2 `notin` fv_in_dexp e1 ->
  x2 `notin` fv_in_dexp e2 ->
  x2 `notin` fv_in_dexp (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_notin :
forall dbody1 e1 x1 x2,
  x2 `notin` fv_in_dbody dbody1 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 `notin` fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_notin_fv_in_dexp_d_subst_v_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_v_in_dbody_notin : lngen.

Lemma fv_in_dexp_d_subst_v_in_dexp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_in_dexp e1 ->
  x2 `notin` fv_in_dexp e2 ->
  x2 `notin` fv_in_dexp (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_notin_fv_in_dexp_d_subst_v_in_dexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_v_in_dexp_notin : lngen.

(* begin hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_upper_mutual :
(forall T1 T2 X1,
  ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1) [<=] ftv_in_dtyp T2 `union` remove X1 (ftv_in_dtyp T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dtyp_d_subst_tv_in_dtyp_upper :
forall T1 T2 X1,
  ftv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T1) [<=] ftv_in_dtyp T2 `union` remove X1 (ftv_in_dtyp T1).
Proof.
pose proof ftv_in_dtyp_d_subst_tv_in_dtyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dtyp_d_subst_tv_in_dtyp_upper : lngen.

(* begin hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_upper_mutual :
(forall b1 T1 X1,
  ftv_in_binding (d_subst_tv_in_binding T1 X1 b1) [<=] ftv_in_dtyp T1 `union` remove X1 (ftv_in_binding b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_binding_d_subst_tv_in_binding_upper :
forall b1 T1 X1,
  ftv_in_binding (d_subst_tv_in_binding T1 X1 b1) [<=] ftv_in_dtyp T1 `union` remove X1 (ftv_in_binding b1).
Proof.
pose proof ftv_in_binding_d_subst_tv_in_binding_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_binding_d_subst_tv_in_binding_upper : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_upper_ftv_in_dexp_d_subst_tv_in_dexp_upper_mutual :
(forall dbody1 T1 X1,
  ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [<=] ftv_in_dtyp T1 `union` remove X1 (ftv_in_dbody dbody1)) /\
(forall e1 T1 X1,
  ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [<=] ftv_in_dtyp T1 `union` remove X1 (ftv_in_dexp e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_tv_in_dbody_upper :
forall dbody1 T1 X1,
  ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [<=] ftv_in_dtyp T1 `union` remove X1 (ftv_in_dbody dbody1).
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_upper_ftv_in_dexp_d_subst_tv_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_tv_in_dbody_upper : lngen.

Lemma ftv_in_dexp_d_subst_tv_in_dexp_upper :
forall e1 T1 X1,
  ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [<=] ftv_in_dtyp T1 `union` remove X1 (ftv_in_dexp e1).
Proof.
pose proof ftv_in_dbody_d_subst_tv_in_dbody_upper_ftv_in_dexp_d_subst_tv_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_tv_in_dexp_upper : lngen.

(* begin hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_upper_ftv_in_dexp_d_subst_v_in_dexp_upper_mutual :
(forall dbody1 e1 x1,
  ftv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1) [<=] ftv_in_dexp e1 `union` ftv_in_dbody dbody1) /\
(forall e1 e2 x1,
  ftv_in_dexp (d_subst_v_in_dexp e2 x1 e1) [<=] ftv_in_dexp e2 `union` ftv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftv_in_dbody_d_subst_v_in_dbody_upper :
forall dbody1 e1 x1,
  ftv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1) [<=] ftv_in_dexp e1 `union` ftv_in_dbody dbody1.
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_upper_ftv_in_dexp_d_subst_v_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dbody_d_subst_v_in_dbody_upper : lngen.

Lemma ftv_in_dexp_d_subst_v_in_dexp_upper :
forall e1 e2 x1,
  ftv_in_dexp (d_subst_v_in_dexp e2 x1 e1) [<=] ftv_in_dexp e2 `union` ftv_in_dexp e1.
Proof.
pose proof ftv_in_dbody_d_subst_v_in_dbody_upper_ftv_in_dexp_d_subst_v_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftv_in_dexp_d_subst_v_in_dexp_upper : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_tv_in_dbody_upper_fv_in_dexp_d_subst_tv_in_dexp_upper_mutual :
(forall dbody1 T1 X1,
  fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [<=] fv_in_dbody dbody1) /\
(forall e1 T1 X1,
  fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [<=] fv_in_dexp e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_tv_in_dbody_upper :
forall dbody1 T1 X1,
  fv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1) [<=] fv_in_dbody dbody1.
Proof.
pose proof fv_in_dbody_d_subst_tv_in_dbody_upper_fv_in_dexp_d_subst_tv_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_tv_in_dbody_upper : lngen.

Lemma fv_in_dexp_d_subst_tv_in_dexp_upper :
forall e1 T1 X1,
  fv_in_dexp (d_subst_tv_in_dexp T1 X1 e1) [<=] fv_in_dexp e1.
Proof.
pose proof fv_in_dbody_d_subst_tv_in_dbody_upper_fv_in_dexp_d_subst_tv_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_tv_in_dexp_upper : lngen.

(* begin hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_upper_fv_in_dexp_d_subst_v_in_dexp_upper_mutual :
(forall dbody1 e1 x1,
  fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1) [<=] fv_in_dexp e1 `union` remove x1 (fv_in_dbody dbody1)) /\
(forall e1 e2 x1,
  fv_in_dexp (d_subst_v_in_dexp e2 x1 e1) [<=] fv_in_dexp e2 `union` remove x1 (fv_in_dexp e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_in_dbody_d_subst_v_in_dbody_upper :
forall dbody1 e1 x1,
  fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1) [<=] fv_in_dexp e1 `union` remove x1 (fv_in_dbody dbody1).
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_upper_fv_in_dexp_d_subst_v_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dbody_d_subst_v_in_dbody_upper : lngen.

Lemma fv_in_dexp_d_subst_v_in_dexp_upper :
forall e1 e2 x1,
  fv_in_dexp (d_subst_v_in_dexp e2 x1 e1) [<=] fv_in_dexp e2 `union` remove x1 (fv_in_dexp e1).
Proof.
pose proof fv_in_dbody_d_subst_v_in_dbody_upper_fv_in_dexp_d_subst_v_in_dexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fv_in_dexp_d_subst_v_in_dexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec_mutual :
(forall T2 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 (close_dtyp_wrt_dtyp_rec n1 X2 T2) = close_dtyp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dtyp T1 X1 T2)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec :
forall T2 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 (close_dtyp_wrt_dtyp_rec n1 X2 T2) = close_dtyp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
pose proof d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_close_binding_wrt_dtyp_rec_mutual :
(forall b1 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 (close_binding_wrt_dtyp_rec n1 X2 b1) = close_binding_wrt_dtyp_rec n1 X2 (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_close_binding_wrt_dtyp_rec :
forall b1 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 (close_binding_wrt_dtyp_rec n1 X2 b1) = close_binding_wrt_dtyp_rec n1 X2 (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof d_subst_tv_in_binding_close_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_close_binding_wrt_dtyp_rec : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 (close_dbody_wrt_dtyp_rec n1 X2 dbody1) = close_dbody_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 (close_dexp_wrt_dtyp_rec n1 X2 e1) = close_dexp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec :
forall dbody1 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 (close_dbody_wrt_dtyp_rec n1 X2 dbody1) = close_dbody_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec : lngen.

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec :
forall e1 T1 X1 X2 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 (close_dexp_wrt_dtyp_rec n1 X2 e1) = close_dexp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 T1 x1 X1 n1,
  d_subst_tv_in_dbody T1 x1 (close_dbody_wrt_dexp_rec n1 X1 dbody1) = close_dbody_wrt_dexp_rec n1 X1 (d_subst_tv_in_dbody T1 x1 dbody1)) /\
(forall e1 T1 x1 X1 n1,
  d_subst_tv_in_dexp T1 x1 (close_dexp_wrt_dexp_rec n1 X1 e1) = close_dexp_wrt_dexp_rec n1 X1 (d_subst_tv_in_dexp T1 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec :
forall dbody1 T1 x1 X1 n1,
  d_subst_tv_in_dbody T1 x1 (close_dbody_wrt_dexp_rec n1 X1 dbody1) = close_dbody_wrt_dexp_rec n1 X1 (d_subst_tv_in_dbody T1 x1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec : lngen.

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec :
forall e1 T1 x1 X1 n1,
  d_subst_tv_in_dexp T1 x1 (close_dexp_wrt_dexp_rec n1 X1 e1) = close_dexp_wrt_dexp_rec n1 X1 (d_subst_tv_in_dexp T1 x1 e1).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 e1 X1 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  x1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dbody e1 X1 (close_dbody_wrt_dtyp_rec n1 x1 dbody1) = close_dbody_wrt_dtyp_rec n1 x1 (d_subst_v_in_dbody e1 X1 dbody1)) /\
(forall e2 e1 X1 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  x1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dexp e1 X1 (close_dexp_wrt_dtyp_rec n1 x1 e2) = close_dexp_wrt_dtyp_rec n1 x1 (d_subst_v_in_dexp e1 X1 e2)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec :
forall dbody1 e1 X1 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  x1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dbody e1 X1 (close_dbody_wrt_dtyp_rec n1 x1 dbody1) = close_dbody_wrt_dtyp_rec n1 x1 (d_subst_v_in_dbody e1 X1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec : lngen.

Lemma d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec :
forall e2 e1 X1 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  x1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dexp e1 X1 (close_dexp_wrt_dtyp_rec n1 x1 e2) = close_dexp_wrt_dtyp_rec n1 x1 (d_subst_v_in_dexp e1 X1 e2).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall dbody1 e1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (close_dbody_wrt_dexp_rec n1 x2 dbody1) = close_dbody_wrt_dexp_rec n1 x2 (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e2 e1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (close_dexp_wrt_dexp_rec n1 x2 e2) = close_dexp_wrt_dexp_rec n1 x2 (d_subst_v_in_dexp e1 x1 e2)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dexp_rec :
forall dbody1 e1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (close_dbody_wrt_dexp_rec n1 x2 dbody1) = close_dbody_wrt_dexp_rec n1 x2 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dexp_rec : lngen.

Lemma d_subst_v_in_dexp_close_dexp_wrt_dexp_rec :
forall e2 e1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_in_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (close_dexp_wrt_dexp_rec n1 x2 e2) = close_dexp_wrt_dexp_rec n1 x2 (d_subst_v_in_dexp e1 x1 e2).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dexp_rec : lngen.

Lemma d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp :
forall T2 T1 X1 X2,
  lc_dtyp T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 (close_dtyp_wrt_dtyp X2 T2) = close_dtyp_wrt_dtyp X2 (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
unfold close_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp : lngen.

Lemma d_subst_tv_in_binding_close_binding_wrt_dtyp :
forall b1 T1 X1 X2,
  lc_dtyp T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 (close_binding_wrt_dtyp X2 b1) = close_binding_wrt_dtyp X2 (d_subst_tv_in_binding T1 X1 b1).
Proof.
unfold close_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_close_binding_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dtyp :
forall dbody1 T1 X1 X2,
  lc_dtyp T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 (close_dbody_wrt_dtyp X2 dbody1) = close_dbody_wrt_dtyp X2 (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dtyp :
forall e1 T1 X1 X2,
  lc_dtyp T1 ->  X1 <> X2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 (close_dexp_wrt_dtyp X2 e1) = close_dexp_wrt_dtyp X2 (d_subst_tv_in_dexp T1 X1 e1).
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dexp :
forall dbody1 T1 x1 X1,
  lc_dtyp T1 ->  d_subst_tv_in_dbody T1 x1 (close_dbody_wrt_dexp X1 dbody1) = close_dbody_wrt_dexp X1 (d_subst_tv_in_dbody T1 x1 dbody1).
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dexp : lngen.

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dexp :
forall e1 T1 x1 X1,
  lc_dtyp T1 ->  d_subst_tv_in_dexp T1 x1 (close_dexp_wrt_dexp X1 e1) = close_dexp_wrt_dexp X1 (d_subst_tv_in_dexp T1 x1 e1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dexp : lngen.

Lemma d_subst_v_in_dbody_close_dbody_wrt_dtyp :
forall dbody1 e1 X1 x1,
  lc_dexp e1 ->  x1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dbody e1 X1 (close_dbody_wrt_dtyp x1 dbody1) = close_dbody_wrt_dtyp x1 (d_subst_v_in_dbody e1 X1 dbody1).
Proof.
unfold close_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dtyp : lngen.

Lemma d_subst_v_in_dexp_close_dexp_wrt_dtyp :
forall e2 e1 X1 x1,
  lc_dexp e1 ->  x1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dexp e1 X1 (close_dexp_wrt_dtyp x1 e2) = close_dexp_wrt_dtyp x1 (d_subst_v_in_dexp e1 X1 e2).
Proof.
unfold close_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dtyp : lngen.

Lemma d_subst_v_in_dbody_close_dbody_wrt_dexp :
forall dbody1 e1 x1 x2,
  lc_dexp e1 ->  x1 <> x2 ->
  x2 `notin` fv_in_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (close_dbody_wrt_dexp x2 dbody1) = close_dbody_wrt_dexp x2 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
unfold close_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dexp : lngen.

Lemma d_subst_v_in_dexp_close_dexp_wrt_dexp :
forall e2 e1 x1 x2,
  lc_dexp e1 ->  x1 <> x2 ->
  x2 `notin` fv_in_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (close_dexp_wrt_dexp x2 e2) = close_dexp_wrt_dexp x2 (d_subst_v_in_dexp e1 x1 e2).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_degree_dtyp_wrt_dtyp_mutual :
(forall T1 T2 X1 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dtyp_wrt_dtyp n1 T2 ->
  degree_dtyp_wrt_dtyp n1 (d_subst_tv_in_dtyp T2 X1 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_degree_dtyp_wrt_dtyp :
forall T1 T2 X1 n1,
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dtyp_wrt_dtyp n1 T2 ->
  degree_dtyp_wrt_dtyp n1 (d_subst_tv_in_dtyp T2 X1 T1).
Proof.
pose proof d_subst_tv_in_dtyp_degree_dtyp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_degree_dtyp_wrt_dtyp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_degree_binding_wrt_dtyp_mutual :
(forall b1 T1 X1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_binding_wrt_dtyp n1 (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_degree_binding_wrt_dtyp :
forall b1 T1 X1 n1,
  degree_binding_wrt_dtyp n1 b1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_binding_wrt_dtyp n1 (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof d_subst_tv_in_binding_degree_binding_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_degree_binding_wrt_dtyp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_degree_dbody_wrt_dtyp_d_subst_tv_in_dexp_degree_dexp_wrt_dtyp_mutual :
(forall dbody1 T1 X1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dbody_wrt_dtyp n1 (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dexp_wrt_dtyp n1 (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_degree_dbody_wrt_dtyp :
forall dbody1 T1 X1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dbody_wrt_dtyp n1 (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_degree_dbody_wrt_dtyp_d_subst_tv_in_dexp_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_degree_dbody_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dexp_degree_dexp_wrt_dtyp :
forall e1 T1 X1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  degree_dexp_wrt_dtyp n1 (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_degree_dbody_wrt_dtyp_d_subst_tv_in_dexp_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_degree_dexp_wrt_dtyp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_degree_dbody_wrt_dexp_d_subst_tv_in_dexp_degree_dexp_wrt_dexp_mutual :
(forall dbody1 T1 X1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp n1 (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_degree_dbody_wrt_dexp :
forall dbody1 T1 X1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dbody_wrt_dexp n1 (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_degree_dbody_wrt_dexp_d_subst_tv_in_dexp_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_degree_dbody_wrt_dexp : lngen.

Lemma d_subst_tv_in_dexp_degree_dexp_wrt_dexp :
forall e1 T1 X1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_degree_dbody_wrt_dexp_d_subst_tv_in_dexp_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_degree_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_degree_dbody_wrt_dtyp_d_subst_v_in_dexp_degree_dexp_wrt_dtyp_mutual :
(forall dbody1 e1 x1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dbody_wrt_dtyp n1 (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp n1 e2 ->
  degree_dexp_wrt_dtyp n1 (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_degree_dbody_wrt_dtyp :
forall dbody1 e1 x1 n1,
  degree_dbody_wrt_dtyp n1 dbody1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dbody_wrt_dtyp n1 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_degree_dbody_wrt_dtyp_d_subst_v_in_dexp_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_degree_dbody_wrt_dtyp : lngen.

Lemma d_subst_v_in_dexp_degree_dexp_wrt_dtyp :
forall e1 e2 x1 n1,
  degree_dexp_wrt_dtyp n1 e1 ->
  degree_dexp_wrt_dtyp n1 e2 ->
  degree_dexp_wrt_dtyp n1 (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof d_subst_v_in_dbody_degree_dbody_wrt_dtyp_d_subst_v_in_dexp_degree_dexp_wrt_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_degree_dexp_wrt_dtyp : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_degree_dbody_wrt_dexp_d_subst_v_in_dexp_degree_dexp_wrt_dexp_mutual :
(forall dbody1 e1 x1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dbody_wrt_dexp n1 (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_degree_dbody_wrt_dexp :
forall dbody1 e1 x1 n1,
  degree_dbody_wrt_dexp n1 dbody1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dbody_wrt_dexp n1 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_degree_dbody_wrt_dexp_d_subst_v_in_dexp_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_degree_dbody_wrt_dexp : lngen.

Lemma d_subst_v_in_dexp_degree_dexp_wrt_dexp :
forall e1 e2 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof d_subst_v_in_dbody_degree_dbody_wrt_dexp_d_subst_v_in_dexp_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_degree_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_fresh_eq_mutual :
(forall T2 T1 X1,
  X1 `notin` ftv_in_dtyp T2 ->
  d_subst_tv_in_dtyp T1 X1 T2 = T2).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_fresh_eq :
forall T2 T1 X1,
  X1 `notin` ftv_in_dtyp T2 ->
  d_subst_tv_in_dtyp T1 X1 T2 = T2.
Proof.
pose proof d_subst_tv_in_dtyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_fresh_eq : lngen.
#[export] Hint Rewrite d_subst_tv_in_dtyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_fresh_eq_mutual :
(forall b1 T1 X1,
  X1 `notin` ftv_in_binding b1 ->
  d_subst_tv_in_binding T1 X1 b1 = b1).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_fresh_eq :
forall b1 T1 X1,
  X1 `notin` ftv_in_binding b1 ->
  d_subst_tv_in_binding T1 X1 b1 = b1.
Proof.
pose proof d_subst_tv_in_binding_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_fresh_eq : lngen.
#[export] Hint Rewrite d_subst_tv_in_binding_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_fresh_eq_d_subst_tv_in_dexp_fresh_eq_mutual :
(forall dbody1 T1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = dbody1) /\
(forall e1 T1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  d_subst_tv_in_dexp T1 X1 e1 = e1).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_fresh_eq :
forall dbody1 T1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = dbody1.
Proof.
pose proof d_subst_tv_in_dbody_fresh_eq_d_subst_tv_in_dexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_fresh_eq : lngen.
#[export] Hint Rewrite d_subst_tv_in_dbody_fresh_eq using solve [auto] : lngen.

Lemma d_subst_tv_in_dexp_fresh_eq :
forall e1 T1 X1,
  X1 `notin` ftv_in_dexp e1 ->
  d_subst_tv_in_dexp T1 X1 e1 = e1.
Proof.
pose proof d_subst_tv_in_dbody_fresh_eq_d_subst_tv_in_dexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_fresh_eq : lngen.
#[export] Hint Rewrite d_subst_tv_in_dexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_fresh_eq_d_subst_v_in_dexp_fresh_eq_mutual :
(forall dbody1 e1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = dbody1) /\
(forall e2 e1 x1,
  x1 `notin` fv_in_dexp e2 ->
  d_subst_v_in_dexp e1 x1 e2 = e2).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_fresh_eq :
forall dbody1 e1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = dbody1.
Proof.
pose proof d_subst_v_in_dbody_fresh_eq_d_subst_v_in_dexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_fresh_eq : lngen.
#[export] Hint Rewrite d_subst_v_in_dbody_fresh_eq using solve [auto] : lngen.

Lemma d_subst_v_in_dexp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_in_dexp e2 ->
  d_subst_v_in_dexp e1 x1 e2 = e2.
Proof.
pose proof d_subst_v_in_dbody_fresh_eq_d_subst_v_in_dexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_fresh_eq : lngen.
#[export] Hint Rewrite d_subst_v_in_dexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_fresh_same_mutual :
(forall T2 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dtyp (d_subst_tv_in_dtyp T1 X1 T2)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_fresh_same :
forall T2 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dtyp (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
pose proof d_subst_tv_in_dtyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_fresh_same : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_fresh_same_mutual :
(forall b1 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_binding (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_fresh_same :
forall b1 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_binding (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof d_subst_tv_in_binding_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_fresh_same : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_fresh_same_d_subst_tv_in_dexp_fresh_same_mutual :
(forall dbody1 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_fresh_same :
forall dbody1 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dbody (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_fresh_same_d_subst_tv_in_dexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_fresh_same : lngen.

Lemma d_subst_tv_in_dexp_fresh_same :
forall e1 T1 X1,
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dexp (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_fresh_same_d_subst_tv_in_dexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_fresh_same : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_fresh_same_d_subst_v_in_dexp_fresh_same_mutual :
(forall dbody1 e1 x1,
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e2 e1 x1,
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dexp (d_subst_v_in_dexp e1 x1 e2)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_fresh_same :
forall dbody1 e1 x1,
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dbody (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_fresh_same_d_subst_v_in_dexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_fresh_same : lngen.

Lemma d_subst_v_in_dexp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dexp (d_subst_v_in_dexp e1 x1 e2).
Proof.
pose proof d_subst_v_in_dbody_fresh_same_d_subst_v_in_dexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_fresh_same : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_fresh_mutual :
(forall T2 T1 X1 X2,
  X1 `notin` ftv_in_dtyp T2 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dtyp (d_subst_tv_in_dtyp T1 X2 T2)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_fresh :
forall T2 T1 X1 X2,
  X1 `notin` ftv_in_dtyp T2 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dtyp (d_subst_tv_in_dtyp T1 X2 T2).
Proof.
pose proof d_subst_tv_in_dtyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_fresh : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_fresh_mutual :
(forall b1 T1 X1 X2,
  X1 `notin` ftv_in_binding b1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_binding (d_subst_tv_in_binding T1 X2 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_fresh :
forall b1 T1 X1 X2,
  X1 `notin` ftv_in_binding b1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_binding (d_subst_tv_in_binding T1 X2 b1).
Proof.
pose proof d_subst_tv_in_binding_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_fresh : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_fresh_d_subst_tv_in_dexp_fresh_mutual :
(forall dbody1 T1 X1 X2,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dbody (d_subst_tv_in_dbody T1 X2 dbody1)) /\
(forall e1 T1 X1 X2,
  X1 `notin` ftv_in_dexp e1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dexp (d_subst_tv_in_dexp T1 X2 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_fresh :
forall dbody1 T1 X1 X2,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dbody (d_subst_tv_in_dbody T1 X2 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_fresh_d_subst_tv_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_fresh : lngen.

Lemma d_subst_tv_in_dexp_fresh :
forall e1 T1 X1 X2,
  X1 `notin` ftv_in_dexp e1 ->
  X1 `notin` ftv_in_dtyp T1 ->
  X1 `notin` ftv_in_dexp (d_subst_tv_in_dexp T1 X2 e1).
Proof.
pose proof d_subst_tv_in_dbody_fresh_d_subst_tv_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_fresh : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_fresh_d_subst_v_in_dexp_fresh_mutual :
(forall dbody1 e1 x1 x2,
  x1 `notin` fv_in_dbody dbody1 ->
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dbody (d_subst_v_in_dbody e1 x2 dbody1)) /\
(forall e2 e1 x1 x2,
  x1 `notin` fv_in_dexp e2 ->
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dexp (d_subst_v_in_dexp e1 x2 e2)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_fresh :
forall dbody1 e1 x1 x2,
  x1 `notin` fv_in_dbody dbody1 ->
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dbody (d_subst_v_in_dbody e1 x2 dbody1).
Proof.
pose proof d_subst_v_in_dbody_fresh_d_subst_v_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_fresh : lngen.

Lemma d_subst_v_in_dexp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_in_dexp e2 ->
  x1 `notin` fv_in_dexp e1 ->
  x1 `notin` fv_in_dexp (d_subst_v_in_dexp e1 x2 e2).
Proof.
pose proof d_subst_v_in_dbody_fresh_d_subst_v_in_dexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_fresh : lngen.

Lemma d_subst_tv_in_dtyp_lc_dtyp :
forall T1 T2 X1,
  lc_dtyp T1 ->
  lc_dtyp T2 ->
  lc_dtyp (d_subst_tv_in_dtyp T2 X1 T1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_lc_dtyp : lngen.

Lemma d_subst_tv_in_binding_lc_binding :
forall b1 T1 X1,
  lc_binding b1 ->
  lc_dtyp T1 ->
  lc_binding (d_subst_tv_in_binding T1 X1 b1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_lc_binding : lngen.

Lemma d_subst_tv_in_dbody_lc_dbody :
forall dbody1 T1 X1,
  lc_dbody dbody1 ->
  lc_dtyp T1 ->
  lc_dbody (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_lc_dbody : lngen.

Lemma d_subst_tv_in_dexp_lc_dexp :
forall e1 T1 X1,
  lc_dexp e1 ->
  lc_dtyp T1 ->
  lc_dexp (d_subst_tv_in_dexp T1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_lc_dexp : lngen.

Lemma d_subst_v_in_dbody_lc_dbody :
forall dbody1 e1 x1,
  lc_dbody dbody1 ->
  lc_dexp e1 ->
  lc_dbody (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_lc_dbody : lngen.

Lemma d_subst_v_in_dexp_lc_dexp :
forall e1 e2 x1,
  lc_dexp e1 ->
  lc_dexp e2 ->
  lc_dexp (d_subst_v_in_dexp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_lc_dexp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_rec_mutual :
(forall T3 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp_rec n1 T2 T3) = open_dtyp_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_dtyp T1 X1 T3)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_rec :
forall T3 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp_rec n1 T2 T3) = open_dtyp_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_dtyp T1 X1 T3).
Proof.
pose proof d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_binding_open_binding_wrt_dtyp_rec_mutual :
(forall b1 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp_rec n1 T2 b1) = open_binding_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_binding_open_binding_wrt_dtyp_rec :
forall b1 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp_rec n1 T2 b1) = open_binding_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof d_subst_tv_in_binding_open_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_open_binding_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp_rec n1 T2 dbody1) = open_dbody_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp_rec n1 T2 e1) = open_dexp_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dtyp_rec :
forall dbody1 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp_rec n1 T2 dbody1) = open_dbody_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_open_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dexp_open_dexp_wrt_dtyp_rec :
forall e1 T1 T2 X1 n1,
  lc_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp_rec n1 T2 e1) = open_dexp_wrt_dtyp_rec n1 (d_subst_tv_in_dtyp T1 X1 T2) (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_open_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 T1 e1 X1 n1,
  d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp_rec n1 e1 dbody1) = open_dbody_wrt_dexp_rec n1 (d_subst_tv_in_dexp T1 X1 e1) (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e2 T1 e1 X1 n1,
  d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp_rec n1 e1 e2) = open_dexp_wrt_dexp_rec n1 (d_subst_tv_in_dexp T1 X1 e1) (d_subst_tv_in_dexp T1 X1 e2)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dexp_rec :
forall dbody1 T1 e1 X1 n1,
  d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp_rec n1 e1 dbody1) = open_dbody_wrt_dexp_rec n1 (d_subst_tv_in_dexp T1 X1 e1) (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_open_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dexp_open_dexp_wrt_dexp_rec :
forall e2 T1 e1 X1 n1,
  d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp_rec n1 e1 e2) = open_dexp_wrt_dexp_rec n1 (d_subst_tv_in_dexp T1 X1 e1) (d_subst_tv_in_dexp T1 X1 e2).
Proof.
pose proof d_subst_tv_in_dbody_open_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_open_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 e1 T1 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp_rec n1 T1 dbody1) = open_dbody_wrt_dtyp_rec n1 T1 (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e2 e1 T1 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp_rec n1 T1 e2) = open_dexp_wrt_dtyp_rec n1 T1 (d_subst_v_in_dexp e1 x1 e2)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_open_dbody_wrt_dtyp_rec :
forall dbody1 e1 T1 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp_rec n1 T1 dbody1) = open_dbody_wrt_dtyp_rec n1 T1 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_open_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dexp_open_dexp_wrt_dtyp_rec :
forall e2 e1 T1 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp_rec n1 T1 e2) = open_dexp_wrt_dtyp_rec n1 T1 (d_subst_v_in_dexp e1 x1 e2).
Proof.
pose proof d_subst_v_in_dbody_open_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_open_dbody_wrt_dexp_rec_d_subst_v_in_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 e1 e2 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp_rec n1 e2 dbody1) = open_dbody_wrt_dexp_rec n1 (d_subst_v_in_dexp e1 x1 e2) (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e3 e1 e2 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 e2 e3) = open_dexp_wrt_dexp_rec n1 (d_subst_v_in_dexp e1 x1 e2) (d_subst_v_in_dexp e1 x1 e3)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_open_dbody_wrt_dexp_rec :
forall dbody1 e1 e2 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp_rec n1 e2 dbody1) = open_dbody_wrt_dexp_rec n1 (d_subst_v_in_dexp e1 x1 e2) (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_open_dbody_wrt_dexp_rec_d_subst_v_in_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dexp_open_dexp_wrt_dexp_rec :
forall e3 e1 e2 x1 n1,
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 e2 e3) = open_dexp_wrt_dexp_rec n1 (d_subst_v_in_dexp e1 x1 e2) (d_subst_v_in_dexp e1 x1 e3).
Proof.
pose proof d_subst_v_in_dbody_open_dbody_wrt_dexp_rec_d_subst_v_in_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp :
forall T3 T1 T2 X1,
  lc_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp T3 T2) = open_dtyp_wrt_dtyp (d_subst_tv_in_dtyp T1 X1 T3) (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp : lngen.

Lemma d_subst_tv_in_binding_open_binding_wrt_dtyp :
forall b1 T1 T2 X1,
  lc_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp b1 T2) = open_binding_wrt_dtyp (d_subst_tv_in_binding T1 X1 b1) (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_open_binding_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dtyp :
forall dbody1 T1 T2 X1,
  lc_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp dbody1 T2) = open_dbody_wrt_dtyp (d_subst_tv_in_dbody T1 X1 dbody1) (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_open_dbody_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dexp_open_dexp_wrt_dtyp :
forall e1 T1 T2 X1,
  lc_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp e1 T2) = open_dexp_wrt_dtyp (d_subst_tv_in_dexp T1 X1 e1) (d_subst_tv_in_dtyp T1 X1 T2).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_open_dexp_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dexp :
forall dbody1 T1 e1 X1,
  d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp dbody1 e1) = open_dbody_wrt_dexp (d_subst_tv_in_dbody T1 X1 dbody1) (d_subst_tv_in_dexp T1 X1 e1).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_open_dbody_wrt_dexp : lngen.

Lemma d_subst_tv_in_dexp_open_dexp_wrt_dexp :
forall e2 T1 e1 X1,
  d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp e2 e1) = open_dexp_wrt_dexp (d_subst_tv_in_dexp T1 X1 e2) (d_subst_tv_in_dexp T1 X1 e1).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_open_dexp_wrt_dexp : lngen.

Lemma d_subst_v_in_dbody_open_dbody_wrt_dtyp :
forall dbody1 e1 T1 x1,
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp dbody1 T1) = open_dbody_wrt_dtyp (d_subst_v_in_dbody e1 x1 dbody1) T1.
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_open_dbody_wrt_dtyp : lngen.

Lemma d_subst_v_in_dexp_open_dexp_wrt_dtyp :
forall e2 e1 T1 x1,
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp e2 T1) = open_dexp_wrt_dtyp (d_subst_v_in_dexp e1 x1 e2) T1.
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_open_dexp_wrt_dtyp : lngen.

Lemma d_subst_v_in_dbody_open_dbody_wrt_dexp :
forall dbody1 e1 e2 x1,
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp dbody1 e2) = open_dbody_wrt_dexp (d_subst_v_in_dbody e1 x1 dbody1) (d_subst_v_in_dexp e1 x1 e2).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_open_dbody_wrt_dexp : lngen.

Lemma d_subst_v_in_dexp_open_dexp_wrt_dexp :
forall e3 e1 e2 x1,
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp e3 e2) = open_dexp_wrt_dexp (d_subst_v_in_dexp e1 x1 e3) (d_subst_v_in_dexp e1 x1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_open_dexp_wrt_dexp : lngen.

Lemma d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_var :
forall T2 T1 X1 X2,
  X1 <> X2 ->
  lc_dtyp T1 ->
  open_dtyp_wrt_dtyp (d_subst_tv_in_dtyp T1 X1 T2) (dtyp_var_f X2) = d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp T2 (dtyp_var_f X2)).
Proof.
intros; rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_var : lngen.

Lemma d_subst_tv_in_binding_open_binding_wrt_dtyp_var :
forall b1 T1 X1 X2,
  X1 <> X2 ->
  lc_dtyp T1 ->
  open_binding_wrt_dtyp (d_subst_tv_in_binding T1 X1 b1) (dtyp_var_f X2) = d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp b1 (dtyp_var_f X2)).
Proof.
intros; rewrite d_subst_tv_in_binding_open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_open_binding_wrt_dtyp_var : lngen.

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dtyp_var :
forall dbody1 T1 X1 X2,
  X1 <> X2 ->
  lc_dtyp T1 ->
  open_dbody_wrt_dtyp (d_subst_tv_in_dbody T1 X1 dbody1) (dtyp_var_f X2) = d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X2)).
Proof.
intros; rewrite d_subst_tv_in_dbody_open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_open_dbody_wrt_dtyp_var : lngen.

Lemma d_subst_tv_in_dexp_open_dexp_wrt_dtyp_var :
forall e1 T1 X1 X2,
  X1 <> X2 ->
  lc_dtyp T1 ->
  open_dexp_wrt_dtyp (d_subst_tv_in_dexp T1 X1 e1) (dtyp_var_f X2) = d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp e1 (dtyp_var_f X2)).
Proof.
intros; rewrite d_subst_tv_in_dexp_open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_open_dexp_wrt_dtyp_var : lngen.

Lemma d_subst_tv_in_dbody_open_dbody_wrt_dexp_var :
forall dbody1 T1 X1 x1,
  open_dbody_wrt_dexp (d_subst_tv_in_dbody T1 X1 dbody1) (dexp_var_f x1) = d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp dbody1 (dexp_var_f x1)).
Proof.
intros; rewrite d_subst_tv_in_dbody_open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_open_dbody_wrt_dexp_var : lngen.

Lemma d_subst_tv_in_dexp_open_dexp_wrt_dexp_var :
forall e1 T1 X1 x1,
  open_dexp_wrt_dexp (d_subst_tv_in_dexp T1 X1 e1) (dexp_var_f x1) = d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp e1 (dexp_var_f x1)).
Proof.
intros; rewrite d_subst_tv_in_dexp_open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_open_dexp_wrt_dexp_var : lngen.

Lemma d_subst_v_in_dbody_open_dbody_wrt_dtyp_var :
forall dbody1 e1 x1 X1,
  lc_dexp e1 ->
  open_dbody_wrt_dtyp (d_subst_v_in_dbody e1 x1 dbody1) (dtyp_var_f X1) = d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)).
Proof.
intros; rewrite d_subst_v_in_dbody_open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_open_dbody_wrt_dtyp_var : lngen.

Lemma d_subst_v_in_dexp_open_dexp_wrt_dtyp_var :
forall e2 e1 x1 X1,
  lc_dexp e1 ->
  open_dexp_wrt_dtyp (d_subst_v_in_dexp e1 x1 e2) (dtyp_var_f X1) = d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp e2 (dtyp_var_f X1)).
Proof.
intros; rewrite d_subst_v_in_dexp_open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_open_dexp_wrt_dtyp_var : lngen.

Lemma d_subst_v_in_dbody_open_dbody_wrt_dexp_var :
forall dbody1 e1 x1 x2,
  x1 <> x2 ->
  lc_dexp e1 ->
  open_dbody_wrt_dexp (d_subst_v_in_dbody e1 x1 dbody1) (dexp_var_f x2) = d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp dbody1 (dexp_var_f x2)).
Proof.
intros; rewrite d_subst_v_in_dbody_open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_open_dbody_wrt_dexp_var : lngen.

Lemma d_subst_v_in_dexp_open_dexp_wrt_dexp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_dexp e1 ->
  open_dexp_wrt_dexp (d_subst_v_in_dexp e1 x1 e2) (dexp_var_f x2) = d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp e2 (dexp_var_f x2)).
Proof.
intros; rewrite d_subst_v_in_dexp_open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_open_dexp_wrt_dexp_var : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_spec_rec_mutual :
(forall T1 T2 X1 n1,
  d_subst_tv_in_dtyp T2 X1 T1 = open_dtyp_wrt_dtyp_rec n1 T2 (close_dtyp_wrt_dtyp_rec n1 X1 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dtyp_spec_rec :
forall T1 T2 X1 n1,
  d_subst_tv_in_dtyp T2 X1 T1 = open_dtyp_wrt_dtyp_rec n1 T2 (close_dtyp_wrt_dtyp_rec n1 X1 T1).
Proof.
pose proof d_subst_tv_in_dtyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_binding_spec_rec_mutual :
(forall b1 T1 X1 n1,
  d_subst_tv_in_binding T1 X1 b1 = open_binding_wrt_dtyp_rec n1 T1 (close_binding_wrt_dtyp_rec n1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_binding_spec_rec :
forall b1 T1 X1 n1,
  d_subst_tv_in_binding T1 X1 b1 = open_binding_wrt_dtyp_rec n1 T1 (close_binding_wrt_dtyp_rec n1 X1 b1).
Proof.
pose proof d_subst_tv_in_binding_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_spec_rec_d_subst_tv_in_dexp_spec_rec_mutual :
(forall dbody1 T1 X1 n1,
  d_subst_tv_in_dbody T1 X1 dbody1 = open_dbody_wrt_dtyp_rec n1 T1 (close_dbody_wrt_dtyp_rec n1 X1 dbody1)) /\
(forall e1 T1 X1 n1,
  d_subst_tv_in_dexp T1 X1 e1 = open_dexp_wrt_dtyp_rec n1 T1 (close_dexp_wrt_dtyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_spec_rec :
forall dbody1 T1 X1 n1,
  d_subst_tv_in_dbody T1 X1 dbody1 = open_dbody_wrt_dtyp_rec n1 T1 (close_dbody_wrt_dtyp_rec n1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_spec_rec_d_subst_tv_in_dexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dexp_spec_rec :
forall e1 T1 X1 n1,
  d_subst_tv_in_dexp T1 X1 e1 = open_dexp_wrt_dtyp_rec n1 T1 (close_dexp_wrt_dtyp_rec n1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_spec_rec_d_subst_tv_in_dexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_spec_rec_d_subst_v_in_dexp_spec_rec_mutual :
(forall dbody1 e1 x1 n1,
  d_subst_v_in_dbody e1 x1 dbody1 = open_dbody_wrt_dexp_rec n1 e1 (close_dbody_wrt_dexp_rec n1 x1 dbody1)) /\
(forall e1 e2 x1 n1,
  d_subst_v_in_dexp e2 x1 e1 = open_dexp_wrt_dexp_rec n1 e2 (close_dexp_wrt_dexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_spec_rec :
forall dbody1 e1 x1 n1,
  d_subst_v_in_dbody e1 x1 dbody1 = open_dbody_wrt_dexp_rec n1 e1 (close_dbody_wrt_dexp_rec n1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_spec_rec_d_subst_v_in_dexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dexp_spec_rec :
forall e1 e2 x1 n1,
  d_subst_v_in_dexp e2 x1 e1 = open_dexp_wrt_dexp_rec n1 e2 (close_dexp_wrt_dexp_rec n1 x1 e1).
Proof.
pose proof d_subst_v_in_dbody_spec_rec_d_subst_v_in_dexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_spec_rec : lngen.

(* end hide *)

Lemma d_subst_tv_in_dtyp_spec :
forall T1 T2 X1,
  d_subst_tv_in_dtyp T2 X1 T1 = open_dtyp_wrt_dtyp (close_dtyp_wrt_dtyp X1 T1) T2.
Proof.
unfold close_dtyp_wrt_dtyp; unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_spec : lngen.

Lemma d_subst_tv_in_binding_spec :
forall b1 T1 X1,
  d_subst_tv_in_binding T1 X1 b1 = open_binding_wrt_dtyp (close_binding_wrt_dtyp X1 b1) T1.
Proof.
unfold close_binding_wrt_dtyp; unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_spec : lngen.

Lemma d_subst_tv_in_dbody_spec :
forall dbody1 T1 X1,
  d_subst_tv_in_dbody T1 X1 dbody1 = open_dbody_wrt_dtyp (close_dbody_wrt_dtyp X1 dbody1) T1.
Proof.
unfold close_dbody_wrt_dtyp; unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_spec : lngen.

Lemma d_subst_tv_in_dexp_spec :
forall e1 T1 X1,
  d_subst_tv_in_dexp T1 X1 e1 = open_dexp_wrt_dtyp (close_dexp_wrt_dtyp X1 e1) T1.
Proof.
unfold close_dexp_wrt_dtyp; unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_spec : lngen.

Lemma d_subst_v_in_dbody_spec :
forall dbody1 e1 x1,
  d_subst_v_in_dbody e1 x1 dbody1 = open_dbody_wrt_dexp (close_dbody_wrt_dexp x1 dbody1) e1.
Proof.
unfold close_dbody_wrt_dexp; unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_spec : lngen.

Lemma d_subst_v_in_dexp_spec :
forall e1 e2 x1,
  d_subst_v_in_dexp e2 x1 e1 = open_dexp_wrt_dexp (close_dexp_wrt_dexp x1 e1) e2.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_spec : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_d_subst_tv_in_dtyp_mutual :
(forall T1 T2 T3 X2 X1,
  X2 `notin` ftv_in_dtyp T2 ->
  X2 <> X1 ->
  d_subst_tv_in_dtyp T2 X1 (d_subst_tv_in_dtyp T3 X2 T1) = d_subst_tv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T3) X2 (d_subst_tv_in_dtyp T2 X1 T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_d_subst_tv_in_dtyp :
forall T1 T2 T3 X2 X1,
  X2 `notin` ftv_in_dtyp T2 ->
  X2 <> X1 ->
  d_subst_tv_in_dtyp T2 X1 (d_subst_tv_in_dtyp T3 X2 T1) = d_subst_tv_in_dtyp (d_subst_tv_in_dtyp T2 X1 T3) X2 (d_subst_tv_in_dtyp T2 X1 T1).
Proof.
pose proof d_subst_tv_in_dtyp_d_subst_tv_in_dtyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_d_subst_tv_in_dtyp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_d_subst_tv_in_binding_mutual :
(forall b1 T1 T2 X2 X1,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  d_subst_tv_in_binding T1 X1 (d_subst_tv_in_binding T2 X2 b1) = d_subst_tv_in_binding (d_subst_tv_in_dtyp T1 X1 T2) X2 (d_subst_tv_in_binding T1 X1 b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_d_subst_tv_in_binding :
forall b1 T1 T2 X2 X1,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  d_subst_tv_in_binding T1 X1 (d_subst_tv_in_binding T2 X2 b1) = d_subst_tv_in_binding (d_subst_tv_in_dtyp T1 X1 T2) X2 (d_subst_tv_in_binding T1 X1 b1).
Proof.
pose proof d_subst_tv_in_binding_d_subst_tv_in_binding_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_d_subst_tv_in_binding : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_d_subst_tv_in_dbody_d_subst_tv_in_dexp_d_subst_tv_in_dexp_mutual :
(forall dbody1 T1 T2 X2 X1,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  d_subst_tv_in_dbody T1 X1 (d_subst_tv_in_dbody T2 X2 dbody1) = d_subst_tv_in_dbody (d_subst_tv_in_dtyp T1 X1 T2) X2 (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 T2 X2 X1,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  d_subst_tv_in_dexp T1 X1 (d_subst_tv_in_dexp T2 X2 e1) = d_subst_tv_in_dexp (d_subst_tv_in_dtyp T1 X1 T2) X2 (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_d_subst_tv_in_dbody :
forall dbody1 T1 T2 X2 X1,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  d_subst_tv_in_dbody T1 X1 (d_subst_tv_in_dbody T2 X2 dbody1) = d_subst_tv_in_dbody (d_subst_tv_in_dtyp T1 X1 T2) X2 (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_d_subst_tv_in_dbody_d_subst_tv_in_dexp_d_subst_tv_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_d_subst_tv_in_dbody : lngen.

Lemma d_subst_tv_in_dexp_d_subst_tv_in_dexp :
forall e1 T1 T2 X2 X1,
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  d_subst_tv_in_dexp T1 X1 (d_subst_tv_in_dexp T2 X2 e1) = d_subst_tv_in_dexp (d_subst_tv_in_dtyp T1 X1 T2) X2 (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_d_subst_tv_in_dbody_d_subst_tv_in_dexp_d_subst_tv_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_d_subst_tv_in_dexp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_d_subst_v_in_dbody_d_subst_tv_in_dexp_d_subst_v_in_dexp_mutual :
(forall dbody1 T1 e1 x1 X1,
  d_subst_tv_in_dbody T1 X1 (d_subst_v_in_dbody e1 x1 dbody1) = d_subst_v_in_dbody (d_subst_tv_in_dexp T1 X1 e1) x1 (d_subst_tv_in_dbody T1 X1 dbody1)) /\
(forall e1 T1 e2 x1 X1,
  d_subst_tv_in_dexp T1 X1 (d_subst_v_in_dexp e2 x1 e1) = d_subst_v_in_dexp (d_subst_tv_in_dexp T1 X1 e2) x1 (d_subst_tv_in_dexp T1 X1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_d_subst_v_in_dbody :
forall dbody1 T1 e1 x1 X1,
  d_subst_tv_in_dbody T1 X1 (d_subst_v_in_dbody e1 x1 dbody1) = d_subst_v_in_dbody (d_subst_tv_in_dexp T1 X1 e1) x1 (d_subst_tv_in_dbody T1 X1 dbody1).
Proof.
pose proof d_subst_tv_in_dbody_d_subst_v_in_dbody_d_subst_tv_in_dexp_d_subst_v_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_d_subst_v_in_dbody : lngen.

Lemma d_subst_tv_in_dexp_d_subst_v_in_dexp :
forall e1 T1 e2 x1 X1,
  d_subst_tv_in_dexp T1 X1 (d_subst_v_in_dexp e2 x1 e1) = d_subst_v_in_dexp (d_subst_tv_in_dexp T1 X1 e2) x1 (d_subst_tv_in_dexp T1 X1 e1).
Proof.
pose proof d_subst_tv_in_dbody_d_subst_v_in_dbody_d_subst_tv_in_dexp_d_subst_v_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_d_subst_v_in_dexp : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_d_subst_tv_in_dbody_d_subst_v_in_dexp_d_subst_tv_in_dexp_mutual :
(forall dbody1 e1 T1 X1 x1,
  X1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (d_subst_tv_in_dbody T1 X1 dbody1) = d_subst_tv_in_dbody T1 X1 (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 T1 X1 x1,
  X1 `notin` ftv_in_dexp e2 ->
  d_subst_v_in_dexp e2 x1 (d_subst_tv_in_dexp T1 X1 e1) = d_subst_tv_in_dexp T1 X1 (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_d_subst_tv_in_dbody :
forall dbody1 e1 T1 X1 x1,
  X1 `notin` ftv_in_dexp e1 ->
  d_subst_v_in_dbody e1 x1 (d_subst_tv_in_dbody T1 X1 dbody1) = d_subst_tv_in_dbody T1 X1 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_d_subst_tv_in_dbody_d_subst_v_in_dexp_d_subst_tv_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_d_subst_tv_in_dbody : lngen.

Lemma d_subst_v_in_dexp_d_subst_tv_in_dexp :
forall e1 e2 T1 X1 x1,
  X1 `notin` ftv_in_dexp e2 ->
  d_subst_v_in_dexp e2 x1 (d_subst_tv_in_dexp T1 X1 e1) = d_subst_tv_in_dexp T1 X1 (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof d_subst_v_in_dbody_d_subst_tv_in_dbody_d_subst_v_in_dexp_d_subst_tv_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_d_subst_tv_in_dexp : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_d_subst_v_in_dbody_d_subst_v_in_dexp_d_subst_v_in_dexp_mutual :
(forall dbody1 e1 e2 x2 x1,
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  d_subst_v_in_dbody e1 x1 (d_subst_v_in_dbody e2 x2 dbody1) = d_subst_v_in_dbody (d_subst_v_in_dexp e1 x1 e2) x2 (d_subst_v_in_dbody e1 x1 dbody1)) /\
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_in_dexp e2 ->
  x2 <> x1 ->
  d_subst_v_in_dexp e2 x1 (d_subst_v_in_dexp e3 x2 e1) = d_subst_v_in_dexp (d_subst_v_in_dexp e2 x1 e3) x2 (d_subst_v_in_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_d_subst_v_in_dbody :
forall dbody1 e1 e2 x2 x1,
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  d_subst_v_in_dbody e1 x1 (d_subst_v_in_dbody e2 x2 dbody1) = d_subst_v_in_dbody (d_subst_v_in_dexp e1 x1 e2) x2 (d_subst_v_in_dbody e1 x1 dbody1).
Proof.
pose proof d_subst_v_in_dbody_d_subst_v_in_dbody_d_subst_v_in_dexp_d_subst_v_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_d_subst_v_in_dbody : lngen.

Lemma d_subst_v_in_dexp_d_subst_v_in_dexp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_in_dexp e2 ->
  x2 <> x1 ->
  d_subst_v_in_dexp e2 x1 (d_subst_v_in_dexp e3 x2 e1) = d_subst_v_in_dexp (d_subst_v_in_dexp e2 x1 e3) x2 (d_subst_v_in_dexp e2 x1 e1).
Proof.
pose proof d_subst_v_in_dbody_d_subst_v_in_dbody_d_subst_v_in_dexp_d_subst_v_in_dexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_d_subst_v_in_dexp : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec_mutual :
(forall T2 T1 X1 X2 n1,
  X2 `notin` ftv_in_dtyp T2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_dtyp T1 X1 T2 = close_dtyp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X2) T2))).
Proof.
apply_mutual_ind dtyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec :
forall T2 T1 X1 X2 n1,
  X2 `notin` ftv_in_dtyp T2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_dtyp T1 X1 T2 = close_dtyp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X2) T2)).
Proof.
pose proof d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_rec_open_dtyp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_binding_close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec_mutual :
(forall b1 T1 X1 X2 n1,
  X2 `notin` ftv_in_binding b1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_binding T1 X1 b1 = close_binding_wrt_dtyp_rec n1 X2 (d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X2) b1))).
Proof.
apply_mutual_ind binding_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_binding_close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec :
forall b1 T1 X1 X2 n1,
  X2 `notin` ftv_in_binding b1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_binding T1 X1 b1 = close_binding_wrt_dtyp_rec n1 X2 (d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X2) b1)).
Proof.
pose proof d_subst_tv_in_binding_close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_close_binding_wrt_dtyp_rec_open_binding_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 T1 X1 X2 n1,
  X2 `notin` ftv_in_dbody dbody1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = close_dbody_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X2) dbody1))) *
(forall e1 T1 X1 X2 n1,
  X2 `notin` ftv_in_dexp e1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_dexp T1 X1 e1 = close_dexp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X2) e1))).
Proof.
apply_mutual_ind dbody_dexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec :
forall dbody1 T1 X1 X2 n1,
  X2 `notin` ftv_in_dbody dbody1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = close_dbody_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X2) dbody1)).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec :
forall e1 T1 X1 X2 n1,
  X2 `notin` ftv_in_dexp e1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  degree_dtyp_wrt_dtyp n1 T1 ->
  d_subst_tv_in_dexp T1 X1 e1 = close_dexp_wrt_dtyp_rec n1 X2 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X2) e1)).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 T1 X1 x1 n1,
  x1 `notin` fv_in_dbody dbody1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = close_dbody_wrt_dexp_rec n1 x1 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1))) *
(forall e1 T1 X1 x1 n1,
  x1 `notin` fv_in_dexp e1 ->
  d_subst_tv_in_dexp T1 X1 e1 = close_dexp_wrt_dexp_rec n1 x1 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1))).
Proof.
apply_mutual_ind dbody_dexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec :
forall dbody1 T1 X1 x1 n1,
  x1 `notin` fv_in_dbody dbody1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = close_dbody_wrt_dexp_rec n1 x1 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1)).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall e1 T1 X1 x1 n1,
  x1 `notin` fv_in_dexp e1 ->
  d_subst_tv_in_dexp T1 X1 e1 = close_dexp_wrt_dexp_rec n1 x1 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1)).
Proof.
pose proof d_subst_tv_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual :
(forall dbody1 e1 x1 X1 n1,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dexp e1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = close_dbody_wrt_dtyp_rec n1 X1 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1))) *
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp e1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  d_subst_v_in_dexp e1 x1 e2 = close_dexp_wrt_dtyp_rec n1 X1 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e2))).
Proof.
apply_mutual_ind dbody_dexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec :
forall dbody1 e1 x1 X1 n1,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dexp e1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = close_dbody_wrt_dtyp_rec n1 X1 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1)).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp e1 ->
  degree_dexp_wrt_dtyp n1 e1 ->
  d_subst_v_in_dexp e1 x1 e2 = close_dexp_wrt_dtyp_rec n1 X1 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e2)).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dtyp_rec_open_dbody_wrt_dtyp_rec_d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dtyp_rec_open_dexp_wrt_dtyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall dbody1 e1 x1 x2 n1,
  x2 `notin` fv_in_dbody dbody1 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = close_dbody_wrt_dexp_rec n1 x2 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x2) dbody1))) *
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_in_dexp e2 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  d_subst_v_in_dexp e1 x1 e2 = close_dexp_wrt_dexp_rec n1 x2 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x2) e2))).
Proof.
apply_mutual_ind dbody_dexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec :
forall dbody1 e1 x1 x2 n1,
  x2 `notin` fv_in_dbody dbody1 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = close_dbody_wrt_dexp_rec n1 x2 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x2) dbody1)).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_in_dexp e2 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  d_subst_v_in_dexp e1 x1 e2 = close_dexp_wrt_dexp_rec n1 x2 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x2) e2)).
Proof.
pose proof d_subst_v_in_dbody_close_dbody_wrt_dexp_rec_open_dbody_wrt_dexp_rec_d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp :
forall T2 T1 X1 X2,
  X2 `notin` ftv_in_dtyp T2 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  lc_dtyp T1 ->
  d_subst_tv_in_dtyp T1 X1 T2 = close_dtyp_wrt_dtyp X2 (d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp T2 (dtyp_var_f X2))).
Proof.
unfold close_dtyp_wrt_dtyp; unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_close_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp : lngen.

Lemma d_subst_tv_in_binding_close_binding_wrt_dtyp_open_binding_wrt_dtyp :
forall b1 T1 X1 X2,
  X2 `notin` ftv_in_binding b1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  lc_dtyp T1 ->
  d_subst_tv_in_binding T1 X1 b1 = close_binding_wrt_dtyp X2 (d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp b1 (dtyp_var_f X2))).
Proof.
unfold close_binding_wrt_dtyp; unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_close_binding_wrt_dtyp_open_binding_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dtyp_open_dbody_wrt_dtyp :
forall dbody1 T1 X1 X2,
  X2 `notin` ftv_in_dbody dbody1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  lc_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = close_dbody_wrt_dtyp X2 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X2))).
Proof.
unfold close_dbody_wrt_dtyp; unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dtyp_open_dbody_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dtyp_open_dexp_wrt_dtyp :
forall e1 T1 X1 X2,
  X2 `notin` ftv_in_dexp e1 ->
  X2 `notin` ftv_in_dtyp T1 ->
  X2 <> X1 ->
  lc_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 e1 = close_dexp_wrt_dtyp X2 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp e1 (dtyp_var_f X2))).
Proof.
unfold close_dexp_wrt_dtyp; unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dtyp_open_dexp_wrt_dtyp : lngen.

Lemma d_subst_tv_in_dbody_close_dbody_wrt_dexp_open_dbody_wrt_dexp :
forall dbody1 T1 X1 x1,
  x1 `notin` fv_in_dbody dbody1 ->
  lc_dtyp T1 ->
  d_subst_tv_in_dbody T1 X1 dbody1 = close_dbody_wrt_dexp x1 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dexp dbody1 (dexp_var_f x1))).
Proof.
unfold close_dbody_wrt_dexp; unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_close_dbody_wrt_dexp_open_dbody_wrt_dexp : lngen.

Lemma d_subst_tv_in_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e1 T1 X1 x1,
  x1 `notin` fv_in_dexp e1 ->
  lc_dtyp T1 ->
  d_subst_tv_in_dexp T1 X1 e1 = close_dexp_wrt_dexp x1 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp e1 (dexp_var_f x1))).
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

Lemma d_subst_v_in_dbody_close_dbody_wrt_dtyp_open_dbody_wrt_dtyp :
forall dbody1 e1 x1 X1,
  X1 `notin` ftv_in_dbody dbody1 ->
  X1 `notin` ftv_in_dexp e1 ->
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = close_dbody_wrt_dtyp X1 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1))).
Proof.
unfold close_dbody_wrt_dtyp; unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dtyp_open_dbody_wrt_dtyp : lngen.

Lemma d_subst_v_in_dexp_close_dexp_wrt_dtyp_open_dexp_wrt_dtyp :
forall e2 e1 x1 X1,
  X1 `notin` ftv_in_dexp e2 ->
  X1 `notin` ftv_in_dexp e1 ->
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 e2 = close_dexp_wrt_dtyp X1 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dtyp e2 (dtyp_var_f X1))).
Proof.
unfold close_dexp_wrt_dtyp; unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dtyp_open_dexp_wrt_dtyp : lngen.

Lemma d_subst_v_in_dbody_close_dbody_wrt_dexp_open_dbody_wrt_dexp :
forall dbody1 e1 x1 x2,
  x2 `notin` fv_in_dbody dbody1 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  lc_dexp e1 ->
  d_subst_v_in_dbody e1 x1 dbody1 = close_dbody_wrt_dexp x2 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp dbody1 (dexp_var_f x2))).
Proof.
unfold close_dbody_wrt_dexp; unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_close_dbody_wrt_dexp_open_dbody_wrt_dexp : lngen.

Lemma d_subst_v_in_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e2 e1 x1 x2,
  x2 `notin` fv_in_dexp e2 ->
  x2 `notin` fv_in_dexp e1 ->
  x2 <> x1 ->
  lc_dexp e1 ->
  d_subst_v_in_dexp e1 x1 e2 = close_dexp_wrt_dexp x2 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp e2 (dexp_var_f x2))).
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

Lemma d_subst_tv_in_dtyp_dtyp_all :
forall X2 T2 T1 X1,
  lc_dtyp T1 ->
  X2 `notin` ftv_in_dtyp T1 `union` ftv_in_dtyp T2 `union` singleton X1 ->
  d_subst_tv_in_dtyp T1 X1 (dtyp_all T2) = dtyp_all (close_dtyp_wrt_dtyp X2 (d_subst_tv_in_dtyp T1 X1 (open_dtyp_wrt_dtyp T2 (dtyp_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_dtyp_all : lngen.

Lemma d_subst_tv_in_dexp_dexp_abs :
forall x1 e1 T1 X1,
  lc_dtyp T1 ->
  x1 `notin` fv_in_dexp e1 ->
  d_subst_tv_in_dexp T1 X1 (dexp_abs e1) = dexp_abs (close_dexp_wrt_dexp x1 (d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dexp e1 (dexp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_dexp_abs : lngen.

Lemma d_subst_tv_in_dexp_dexp_tabs :
forall X2 dbody1 T1 X1,
  lc_dtyp T1 ->
  X2 `notin` ftv_in_dtyp T1 `union` ftv_in_dbody dbody1 `union` singleton X1 ->
  d_subst_tv_in_dexp T1 X1 (dexp_tabs dbody1) = dexp_tabs (close_dbody_wrt_dtyp X2 (d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_dexp_tabs : lngen.

Lemma d_subst_v_in_dexp_dexp_abs :
forall x2 e2 e1 x1,
  lc_dexp e1 ->
  x2 `notin` fv_in_dexp e1 `union` fv_in_dexp e2 `union` singleton x1 ->
  d_subst_v_in_dexp e1 x1 (dexp_abs e2) = dexp_abs (close_dexp_wrt_dexp x2 (d_subst_v_in_dexp e1 x1 (open_dexp_wrt_dexp e2 (dexp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_dexp_abs : lngen.

Lemma d_subst_v_in_dexp_dexp_tabs :
forall X1 dbody1 e1 x1,
  lc_dexp e1 ->
  X1 `notin` ftv_in_dexp e1 `union` ftv_in_dbody dbody1 ->
  d_subst_v_in_dexp e1 x1 (dexp_tabs dbody1) = dexp_tabs (close_dbody_wrt_dtyp X1 (d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_dexp_tabs : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dtyp_intro_rec_mutual :
(forall T1 X1 T2 n1,
  X1 `notin` ftv_in_dtyp T1 ->
  open_dtyp_wrt_dtyp_rec n1 T2 T1 = d_subst_tv_in_dtyp T2 X1 (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1)).
Proof.
apply_mutual_ind dtyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dtyp_intro_rec :
forall T1 X1 T2 n1,
  X1 `notin` ftv_in_dtyp T1 ->
  open_dtyp_wrt_dtyp_rec n1 T2 T1 = d_subst_tv_in_dtyp T2 X1 (open_dtyp_wrt_dtyp_rec n1 (dtyp_var_f X1) T1).
Proof.
pose proof d_subst_tv_in_dtyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_intro_rec : lngen.
#[export] Hint Rewrite d_subst_tv_in_dtyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_tv_in_binding_intro_rec_mutual :
(forall b1 X1 T1 n1,
  X1 `notin` ftv_in_binding b1 ->
  open_binding_wrt_dtyp_rec n1 T1 b1 = d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1)).
Proof.
apply_mutual_ind binding_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_binding_intro_rec :
forall b1 X1 T1 n1,
  X1 `notin` ftv_in_binding b1 ->
  open_binding_wrt_dtyp_rec n1 T1 b1 = d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp_rec n1 (dtyp_var_f X1) b1).
Proof.
pose proof d_subst_tv_in_binding_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_intro_rec : lngen.
#[export] Hint Rewrite d_subst_tv_in_binding_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_tv_in_dbody_intro_rec_d_subst_tv_in_dexp_intro_rec_mutual :
(forall dbody1 X1 T1 n1,
  X1 `notin` ftv_in_dbody dbody1 ->
  open_dbody_wrt_dtyp_rec n1 T1 dbody1 = d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1)) /\
(forall e1 X1 T1 n1,
  X1 `notin` ftv_in_dexp e1 ->
  open_dexp_wrt_dtyp_rec n1 T1 e1 = d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_tv_in_dbody_intro_rec :
forall dbody1 X1 T1 n1,
  X1 `notin` ftv_in_dbody dbody1 ->
  open_dbody_wrt_dtyp_rec n1 T1 dbody1 = d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp_rec n1 (dtyp_var_f X1) dbody1).
Proof.
pose proof d_subst_tv_in_dbody_intro_rec_d_subst_tv_in_dexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_intro_rec : lngen.
#[export] Hint Rewrite d_subst_tv_in_dbody_intro_rec using solve [auto] : lngen.

Lemma d_subst_tv_in_dexp_intro_rec :
forall e1 X1 T1 n1,
  X1 `notin` ftv_in_dexp e1 ->
  open_dexp_wrt_dtyp_rec n1 T1 e1 = d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp_rec n1 (dtyp_var_f X1) e1).
Proof.
pose proof d_subst_tv_in_dbody_intro_rec_d_subst_tv_in_dexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_intro_rec : lngen.
#[export] Hint Rewrite d_subst_tv_in_dexp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma d_subst_v_in_dbody_intro_rec_d_subst_v_in_dexp_intro_rec_mutual :
(forall dbody1 x1 e1 n1,
  x1 `notin` fv_in_dbody dbody1 ->
  open_dbody_wrt_dexp_rec n1 e1 dbody1 = d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1)) /\
(forall e1 x1 e2 n1,
  x1 `notin` fv_in_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 e2 e1 = d_subst_v_in_dexp e2 x1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1)).
Proof.
apply_mutual_ind dbody_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma d_subst_v_in_dbody_intro_rec :
forall dbody1 x1 e1 n1,
  x1 `notin` fv_in_dbody dbody1 ->
  open_dbody_wrt_dexp_rec n1 e1 dbody1 = d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp_rec n1 (dexp_var_f x1) dbody1).
Proof.
pose proof d_subst_v_in_dbody_intro_rec_d_subst_v_in_dexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_intro_rec : lngen.
#[export] Hint Rewrite d_subst_v_in_dbody_intro_rec using solve [auto] : lngen.

Lemma d_subst_v_in_dexp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_in_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 e2 e1 = d_subst_v_in_dexp e2 x1 (open_dexp_wrt_dexp_rec n1 (dexp_var_f x1) e1).
Proof.
pose proof d_subst_v_in_dbody_intro_rec_d_subst_v_in_dexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_intro_rec : lngen.
#[export] Hint Rewrite d_subst_v_in_dexp_intro_rec using solve [auto] : lngen.

Lemma d_subst_tv_in_dtyp_intro :
forall X1 T1 T2,
  X1 `notin` ftv_in_dtyp T1 ->
  open_dtyp_wrt_dtyp T1 T2 = d_subst_tv_in_dtyp T2 X1 (open_dtyp_wrt_dtyp T1 (dtyp_var_f X1)).
Proof.
unfold open_dtyp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dtyp_intro : lngen.

Lemma d_subst_tv_in_binding_intro :
forall X1 b1 T1,
  X1 `notin` ftv_in_binding b1 ->
  open_binding_wrt_dtyp b1 T1 = d_subst_tv_in_binding T1 X1 (open_binding_wrt_dtyp b1 (dtyp_var_f X1)).
Proof.
unfold open_binding_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_binding_intro : lngen.

Lemma d_subst_tv_in_dbody_intro :
forall X1 dbody1 T1,
  X1 `notin` ftv_in_dbody dbody1 ->
  open_dbody_wrt_dtyp dbody1 T1 = d_subst_tv_in_dbody T1 X1 (open_dbody_wrt_dtyp dbody1 (dtyp_var_f X1)).
Proof.
unfold open_dbody_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dbody_intro : lngen.

Lemma d_subst_tv_in_dexp_intro :
forall X1 e1 T1,
  X1 `notin` ftv_in_dexp e1 ->
  open_dexp_wrt_dtyp e1 T1 = d_subst_tv_in_dexp T1 X1 (open_dexp_wrt_dtyp e1 (dtyp_var_f X1)).
Proof.
unfold open_dexp_wrt_dtyp; default_simp.
Qed.

#[export] Hint Resolve d_subst_tv_in_dexp_intro : lngen.

Lemma d_subst_v_in_dbody_intro :
forall x1 dbody1 e1,
  x1 `notin` fv_in_dbody dbody1 ->
  open_dbody_wrt_dexp dbody1 e1 = d_subst_v_in_dbody e1 x1 (open_dbody_wrt_dexp dbody1 (dexp_var_f x1)).
Proof.
unfold open_dbody_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dbody_intro : lngen.

Lemma d_subst_v_in_dexp_intro :
forall x1 e1 e2,
  x1 `notin` fv_in_dexp e1 ->
  open_dexp_wrt_dexp e1 e2 = d_subst_v_in_dexp e2 x1 (open_dexp_wrt_dexp e1 (dexp_var_f x1)).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

#[export] Hint Resolve d_subst_v_in_dexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
