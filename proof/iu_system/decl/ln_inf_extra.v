Require Import decl.ott.
Require Export decl.notations.


Lemma dtyp_subst_open_comm : forall X T1 T2 T3,
  lc_dtyp T2 -> 
  X `notin` ftv_in_dtyp T3 -> 
  ([T2 /ᵈ X] T1) ^^ᵈ T3 = [T2 /ᵈ X] T1 ^^ᵈ T3.
Proof.
  intros.
  rewrite dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
  rewrite (dsubst_tv_in_dtyp_fresh_eq T3); auto.
Qed.


Lemma dtyp_open_r_close_l : forall T1 T2 X
  , X `notin` ftv_in_dtyp T2
  -> T1 = open_dtyp_wrt_dtyp T2 `ᵈ X -> close_dtyp_wrt_dtyp X T1 = T2.
Proof.
  intros * Fr H.
  assert (close_dtyp_wrt_dtyp X T1 = close_dtyp_wrt_dtyp X (open_dtyp_wrt_dtyp T2 `ᵈ X)) by now rewrite H.
  now rewrite close_dtyp_wrt_dtyp_open_dtyp_wrt_dtyp in H0.
Qed.


Lemma close_dtyp_notin_rec : forall X e n,
    X `notin` ftv_in_dtyp (close_dtyp_wrt_dtyp_rec n X e).
Proof.
  intros until e.
  induction e; simpl; intros; auto.
  - destruct (lt_ge_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.


Lemma close_ld_type_notin : forall X e,
    X `notin` ftv_in_dtyp (close_dtyp_wrt_dtyp X e).
Proof.
  intros. apply close_dtyp_notin_rec.
Qed.
