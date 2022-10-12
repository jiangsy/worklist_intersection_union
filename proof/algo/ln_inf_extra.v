Require Import Coq.Program.Equality.

Require Import algo.ott.
Require Import algo.ln_inf.
Require Export algo.notations.



Lemma la_type_subst_open_comm : forall x t1 A t2,
  lc_la_type t1 -> 
  x `notin` fx_la_type t2 -> 
  ([t1 /ᵃ x] A) ^^ᵃ t2 = [t1 /ᵃ x] A ^^ᵃ t2.
Proof.
  intros.
  rewrite subst_la_type_open_la_type_wrt_la_type.
  rewrite (subst_la_type_fresh_eq t2).
  all: easy.
Qed.


Lemma ex_subst_la_type_open_la_type_wrt_la_type_rec_mutual :
(forall t3 t1 t2 x1 n1,
  lc_la_type t1 ->
  ex_subst_la_type t1 x1 (open_la_type_wrt_la_type_rec n1 t2 t3) = open_la_type_wrt_la_type_rec n1 (ex_subst_la_type t1 x1 t2) (ex_subst_la_type t1 x1 t3)).
Proof.
  apply_mutual_ind la_type_mutind;
  default_simp.
  rewrite open_la_type_wrt_la_type_rec_degree_la_type_wrt_la_type; auto.
  apply degree_la_type_wrt_la_type_O.
  apply degree_la_type_wrt_la_type_of_lc_la_type. auto.
Qed.

Lemma ex_subst_la_type_open_la_type_wrt_la_type :
forall t3 t1 t2 x1,
  lc_la_type t1 ->
  ex_subst_la_type t1 x1 (open_la_type_wrt_la_type t3 t2) = open_la_type_wrt_la_type (ex_subst_la_type t1 x1 t3) (ex_subst_la_type t1 x1 t2).
Proof.
unfold open_la_type_wrt_la_type; default_simp.
apply ex_subst_la_type_open_la_type_wrt_la_type_rec_mutual. auto.
Qed.

Lemma ex_subst_la_type_fresh_eq :
(forall t2 t1 x1,
  x1 `notin` fex_la_type t2 ->
  ex_subst_la_type t1 x1 t2 = t2).
Proof.
apply_mutual_ind la_type_mutind;
default_simp.
Qed.

Lemma la_type_ex_subst_open_comm : forall x t1 A t2,
  lc_la_type t1 -> 
  x `notin` fex_la_type t2 -> 
  ([t1 /^ᵃ x] A) ^^ᵃ t2 = [t1 /^ᵃ x] A ^^ᵃ t2.
Proof.
  intros.
  rewrite ex_subst_la_type_open_la_type_wrt_la_type.
  rewrite (ex_subst_la_type_fresh_eq t2); auto.
  auto.
Qed.

Lemma fx_la_type_open_la_type_notin_rec : forall x e2,
  x `notin` fx_la_type e2 -> 
  forall e1 n, 
    x `notin` fx_la_type e1 ->
    x `notin` fx_la_type (open_la_type_wrt_la_type_rec n e2 e1).
Proof.
  intros until e1.
  induction e1; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0). destruct s.
    all: auto.
Qed.

Lemma fx_la_type_open_la_type_notin : forall x e1 e2, 
  x `notin` fx_la_type e1 -> 
  x `notin` fx_la_type e2 -> 
  x `notin` fx_la_type (e1 ^^ᵃ e2).
Proof.
  intros.
  eauto using fx_la_type_open_la_type_notin_rec.
Qed.


Lemma fex_la_type_open_la_type_notin_rec : forall x e2,
  x `notin` fex_la_type e2 -> 
  forall e1 n, 
    x `notin` fex_la_type e1 ->
    x `notin` fex_la_type (open_la_type_wrt_la_type_rec n e2 e1).
Proof.
  intros until e1.
  induction e1; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0). destruct s.
    all: auto.
Qed.

Lemma fex_la_type_open_la_type_notin : forall x e1 e2, 
  x `notin` fex_la_type e1 -> 
  x `notin` fex_la_type e2 -> 
  x `notin` fex_la_type (e1 ^^ᵃ e2).
Proof.
  intros.
  eauto using fex_la_type_open_la_type_notin_rec.
Qed.
