Require Import Coq.Program.Equality.

Require Import algo.ott.
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
