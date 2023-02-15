Require Import decl.ott.
Require Export decl.notations.


Lemma subst_same_tvar_eq : forall T X,
  T = {`ᵈ X /ᵈ X} T.
Proof.
  intros.
  induction T; auto; simpl.
  - destruct (X0==X); subst; auto. 
  - simpl. rewrite <- IHT1. rewrite <- IHT2. auto.
  - simpl. rewrite <- IHT. auto.
  - simpl. rewrite <- IHT1. rewrite <- IHT2. auto.
  - simpl. rewrite <- IHT1. rewrite <- IHT2. auto.
Qed.

(* Lemma n_lt_n_false : forall n,
  n < n -> False.
Admitted.

Ltac lt_refl_contra :=
  match goal with 
  | H : ?n < ?n |- _ =>
    apply n_lt_n_false in H; contradiction
  end. *)

Lemma open_dtyp_wrt_dtyp_rec_comm : forall S1 S2 T n1 n2,
  n1 <> n2 ->
  lc_dtyp S1 ->
  lc_dtyp S2 ->
  open_dtyp_wrt_dtyp_rec n1 S1 (open_dtyp_wrt_dtyp_rec n2 S2 T) = open_dtyp_wrt_dtyp_rec n2 S2 (open_dtyp_wrt_dtyp_rec n1 S1 T).
Proof.
  induction T; intros; simpl in *; auto; try solve [f_equal; auto].
  - destruct (lt_eq_lt_dec n n2 ); destruct (lt_eq_lt_dec n n1); simpl.
    + admit.
    + destruct s; simpl.
      * destruct (lt_eq_lt_dec n n1).
        -- destruct s. 
          ++ admit.
          ++ admit.
        -- admit.
      * subst. destruct (lt_eq_lt_dec (n2 - 1) n2).
        -- destruct s.
          ++ simpl.
Admitted.

Lemma dtyp_subst_open_comm : forall X T1 T2 T3,
  lc_dtyp T2 -> 
  X `notin` ftv_in_dtyp T3 -> 
  ({T2 /ᵈ X} T1) ^^ᵈ T3 = {T2 /ᵈ X} T1 ^^ᵈ T3.
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

Lemma dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp_rec_mutual :
(forall T3 T1 T2 SX n1,
  lc_dtyp T1 ->
  dsubst_stv_in_dtyp T1 SX (open_dtyp_wrt_dtyp_rec n1 T2 T3) = open_dtyp_wrt_dtyp_rec n1 (dsubst_stv_in_dtyp T1 SX T2) (dsubst_stv_in_dtyp T1 SX T3)).
Proof.
  apply_mutual_ind dtyp_mutind;
  default_simp.
  rewrite open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp; auto.
  apply degree_dtyp_wrt_dtyp_O.
  apply degree_dtyp_wrt_dtyp_of_lc_dtyp. auto.
Qed.


Lemma dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp:
forall T3 T1 T2 SX,
  lc_dtyp T1 ->
  dsubst_stv_in_dtyp T1 SX (open_dtyp_wrt_dtyp T3 T2) = open_dtyp_wrt_dtyp (dsubst_stv_in_dtyp T1 SX T3) (dsubst_stv_in_dtyp T1 SX T2).
Proof.
  unfold open_dtyp_wrt_dtyp; default_simp.
  apply dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp_rec_mutual. 
  auto.
Qed.

Lemma dsubst_stv_in_dtyp_fresh_eq :
(forall T2 T1 SX,
  SX `notin` fstv_in_dtyp T2 ->
  dsubst_stv_in_dtyp T1 SX T2 = T2).
Proof.
  apply_mutual_ind dtyp_mutind;
  default_simp.
Qed.

Lemma dsubst_stv_in_dtyp_open_comm : forall SX T3 T1 T2,
  lc_dtyp T3 -> 
  SX `notin` fstv_in_dtyp T2 -> 
  ({T3 /ₛᵈ SX} T1) ^^ᵈ T2 = {T3 /ₛᵈ SX} T1 ^^ᵈ T2.
Proof.
  intros.
  rewrite dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp.
  rewrite (dsubst_stv_in_dtyp_fresh_eq T2); auto.
  auto.
Qed.


Lemma dsubst_stv_lc_dtyp : forall SX T1 T2,
  lc_dtyp T1 ->
  lc_dtyp T2 ->
  lc_dtyp ({ T2 /ₛᵈ SX } T1).
Proof.
  intros. induction H; simpl; auto.
  - destruct (SX0 == SX); auto.
  - eapply lc_dtyp_all. intros.
    replace (({T2 /ₛᵈ SX} T) ^ᵈ X) with ({T2 /ₛᵈ SX} T ^ᵈ X); auto. 
    rewrite dsubst_stv_in_dtyp_open_comm; auto.
Qed.
