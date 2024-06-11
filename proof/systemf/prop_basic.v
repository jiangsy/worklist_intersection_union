Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import systemf.def_ott.
Require Import systemf.prop_ln.

Lemma close_ftyp_wrt_ftyp_notin_rec : forall X A n,
   X `notin` ftvar_in_ftyp (close_ftyp_wrt_ftyp_rec n X A).
Proof.
  intros until A.
  induction A; simpl; intros; auto.
  - destruct (lt_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.

Lemma close_ftyp_wrt_ftyp_notin : forall X A,
  X `notin` ftvar_in_ftyp (close_ftyp_wrt_ftyp X A).
Proof.
  intros. apply close_ftyp_wrt_ftyp_notin_rec.
Qed.

Lemma close_fexp_wrt_ftyp_notin_rec : forall X e n,
   X `notin` ftvar_in_fexp (close_fexp_wrt_ftyp_rec n X e).
Proof with eauto using close_ftyp_wrt_ftyp_notin_rec.
  intros until e.
  induction e; simpl; intros; auto...
Qed.

Lemma close_fexp_wrt_ftyp_notin : forall X e,
  X `notin` ftvar_in_fexp (close_fexp_wrt_ftyp X e).
Proof.
  intros. apply close_fexp_wrt_ftyp_notin_rec.
Qed.

Lemma close_fexp_wrt_fexp_notin_rec : forall x e n,
  x `notin` fvar_in_fexp (close_fexp_wrt_fexp_rec n x e).
Proof.
  intros until e. induction e; simpl; intros; auto.
  - destruct (lt_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.

Lemma close_fexp_wrt_fexp_notin : forall x e,
    x `notin` fvar_in_fexp (close_fexp_wrt_fexp x e).
Proof.
  intros until e. unfold close_fexp_wrt_fexp.
  apply close_fexp_wrt_fexp_notin_rec.
Qed.

Lemma open_fexp_wrt_fexp_rec_lc_fexp : forall e2 e1 n,
  lc_fexp e2 -> open_fexp_wrt_fexp_rec n e1 e2 = e2.
Proof.
  intros. apply open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp.
  apply degree_fexp_wrt_fexp_O.
  apply degree_fexp_wrt_fexp_of_lc_fexp. auto.
Qed.

Lemma open_fexp_wrt_ftyp_rec_lc_fexp : forall e T n,
  lc_fexp e -> open_fexp_wrt_ftyp_rec n T e = e.
Proof.
  intros. apply open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp.
  apply degree_fexp_wrt_ftyp_O.
  apply degree_fexp_wrt_ftyp_of_lc_fexp. auto.
Qed.
