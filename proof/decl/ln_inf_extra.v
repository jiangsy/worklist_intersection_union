Require Import decl.ott.
Require Export decl.notations.


Lemma ld_type_open_r_close_l : forall t1 t2 x
  , x `notin` fv_ld_type t2
  -> t1 = open_ld_type_wrt_ld_type t2 `x -> close_ld_type_wrt_ld_type x t1 = t2.
Proof.
  intros * Fr H.
  assert (close_ld_type_wrt_ld_type x t1 = close_ld_type_wrt_ld_type x (open_ld_type_wrt_ld_type t2 `x)) by now rewrite H.
  now rewrite close_ld_type_wrt_ld_type_open_ld_type_wrt_ld_type in H0.
Qed.


Lemma close_ld_type_notin_rec : forall x e n,
    x `notin` fv_ld_type (close_ld_type_wrt_ld_type_rec n x e).
Proof.
  intros until e.

  induction e; simpl; intros; auto.
  - destruct (lt_ge_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.


Lemma close_ld_type_notin : forall x e,
    x `notin` fv_ld_type (close_ld_type_wrt_ld_type x e).
Proof.
  intros. apply close_ld_type_notin_rec.
Qed.
