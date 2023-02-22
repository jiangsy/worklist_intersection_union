Require Import Coq.Program.Equality.

Require Import ln_utils.
Require Import decl.prop_ln.
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

Lemma fstv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper_mutual :
(forall T1 T2 n1,
  fstv_in_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1) [<=] fstv_in_dtyp T2 `union` fstv_in_dtyp T1).
Proof.
  apply_mutual_ind dtyp_mutind;
  default_simp; try fsetdec.
  - rewrite IHdtyp1; rewrite IHdtyp2. fsetdec.
  - rewrite IHdtyp1; rewrite IHdtyp2. fsetdec.
  - rewrite IHdtyp1; rewrite IHdtyp2. fsetdec.
Qed.

Lemma fstv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper : forall T1 T2 n1,
  fstv_in_dtyp (open_dtyp_wrt_dtyp_rec n1 T2 T1) [<=] fstv_in_dtyp T2 `union` fstv_in_dtyp T1.
Proof.
  pose proof fstv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper_mutual as H; intuition eauto.
Qed.

Lemma fstv_in_dtyp_open_dtyp_wrt_dtyp_upper : forall T1 T2,
  fstv_in_dtyp (open_dtyp_wrt_dtyp T1 T2) [<=] fstv_in_dtyp T2 `union` fstv_in_dtyp T1.
Proof.
  intros.
  unfold open_dtyp_wrt_dtyp.
  apply fstv_in_dtyp_open_dtyp_wrt_dtyp_rec_upper.
Qed.

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
  - destruct (lt_dec n n0); auto.
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


Hint Constructors ds_in_s: core.
Hint Constructors ds_in: core.

Lemma ftv_sin_dtyp_stvar_fstv_sin_dtyp : forall X T,
  ds_in X T ->
  ds_in_s X ({dtyp_svar X /ᵈ X} T).
Proof.
  intros. induction H; simpl; auto.
  - destruct (X == X).
    + constructor.
    + contradiction.
  - apply dsins_arrow1; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - apply dsins_all with (L:=L `union` singleton X). intros.
    inst_cofinites_with Y. 
    replace (({dtyp_svar X /ᵈ X} T) ^ᵈ Y) with ({dtyp_svar X /ᵈ X} T ^ᵈ Y).
    auto.
    rewrite dtyp_subst_open_comm; auto.
Qed.

Lemma sin_in : forall X T, 
  ds_in X T ->
  X `in` ftv_in_dtyp T.
Proof.
  intros. induction H; simpl; auto.
  - inst_cofinites_by (L `union` singleton X).
    rewrite ftv_in_dtyp_open_dtyp_wrt_dtyp_upper in H0.
    apply AtomSetImpl.union_1 in H0; inversion H0; auto.
    + simpl in H1. apply AtomSetImpl.singleton_1 in H1.
      apply notin_union_2 in Fr. subst.
      apply notin_singleton_1 in Fr. contradiction.
Qed.

Lemma lc_dtyp_subst : forall T X S,
  lc_dtyp ({S /ᵈ X} T) ->
  lc_dtyp S ->
  lc_dtyp T.
Proof.
  intros.
  dependent induction H; auto.
  - destruct T; try solve [inversion x]; auto.
  - destruct T; try solve [inversion x]; auto.
  - destruct T; try solve [inversion x]; auto.
  - destruct T; try solve [inversion x]; auto.
  - destruct T; try solve [inversion x]; auto.
  - destruct T; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct T; try solve [inversion x]; auto.
    inversion x. 
    inst_cofinites_by (singleton X).
    eapply lc_dtyp_all_exists with (X1:=x0). intros.
    specialize (H0 x0 (T ^ᵈ x0) X S). apply H0.
    subst. rewrite <- dtyp_subst_open_comm; auto.
    auto.
  - destruct T; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct T; try solve [inversion x]; auto.
    inversion x; eauto.
Qed.

Lemma ftv_sin_dtyp_subst : forall X Y T S,
  lc_dtyp S ->
  X `notin` ftv_in_dtyp S ->
  X <> Y ->
  ds_in X ({S /ᵈ Y} T) ->
  ds_in X T.
Proof.
  intros. dependent induction H2; simpl; auto.
  - destruct T; simpl; try solve [inversion x].
    inversion x. destruct (X0 == Y).
    + subst. simpl in *. 
      apply notin_singleton_1 in H0. contradiction.
    + inversion H3. auto.
  - destruct T; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0.
      eapply IHds_in with (S:=T1) (Y:=Y); auto. 
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction. 
    + inversion x.
    + apply dsin_arrow1; inversion x; eauto.
      subst.
      eapply lc_dtyp_subst; eauto.
  - destruct T; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0. eapply IHds_in with (S:=T2) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction. 
    + inversion x.
    + apply dsin_arrow2; inversion x; eauto.
      subst. eapply lc_dtyp_subst; eauto.
  - destruct T; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (dtyp_all T0)).
      * eapply dsin_all with (L:=L). intros. inst_cofinites_with Y0.
        auto.
      * apply sin_in in H4. contradiction.
    + inversion x.
    + apply dsin_all with (L:=L `union` singleton Y); intros; inst_cofinites_with Y0. auto.
     inversion x. rewrite H6 in H3. 
    eapply H2; eauto. subst. rewrite dtyp_subst_open_comm; auto.
  - destruct T; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (dtyp_union T1 T2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_union.
      * eapply IHds_in1 with (S:=S) (Y:=Y); eauto.
      * eapply IHds_in2 with (S:=S) (Y:=Y); eauto.
  - destruct T; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (dtyp_intersection T1 T2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_intersection.
      * eapply IHds_in1 with (S:=S) (Y:=Y); eauto.
      * eapply IHds_in2 with (S:=S) (Y:=Y); eauto.
Qed.

Lemma fstv_sin_dtyp_subst_tv : forall SX X T T',
  ds_in_s SX T ->
  lc_dtyp T' ->
  ds_in_s SX ({T' /ᵈ X} T).
Proof.
  intros.
  induction H; simpl; auto.
  - apply dsins_arrow1; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - simpl in H. 
    apply dsins_all with (L:=L `union` singleton X). intros.
    rewrite dtyp_subst_open_comm; auto.
Qed.


Lemma ftv_sins_dtyp_tvar_fstv_sin_dtyp : forall SX T,
  ds_in_s SX T ->
  ds_in SX ({dtyp_var_f SX /ₛᵈ SX} T).
Proof.
  intros. induction H; simpl; auto.
  - destruct (SX == SX).
    + constructor.
    + contradiction.
  - apply dsin_arrow1; auto.
    apply dsubst_stv_lc_dtyp; auto.
  - apply dsin_arrow2; auto.
    apply dsubst_stv_lc_dtyp; auto.
  - apply dsin_all with (L:=L `union` singleton SX). intros.
    inst_cofinites_with Y. 
    replace (({dtyp_var_f SX /ₛᵈ SX} T) ^ᵈ Y) with ({dtyp_var_f SX /ₛᵈ SX} T ^ᵈ Y).
    auto.
    rewrite dsubst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma fstv_sins_dtyp_subst_stv : forall SX X T T',
  ds_in X T ->
  lc_dtyp T' ->
  ds_in X ({T' /ₛᵈ SX} T).
Proof.
  intros.
  induction H; simpl; auto.
  - apply dsin_arrow1; auto.
    now apply dsubst_stv_lc_dtyp.
  - apply dsin_arrow2; auto.
    now apply dsubst_stv_lc_dtyp.
  - simpl in H. 
    apply dsin_all with (L:=L `union` singleton X). intros.
    rewrite dsubst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma fstv_open_tvar : forall T SX,
  SX `notin` fstv_in_dtyp T ->
  ds_in_s SX (T ^^ᵈ dtyp_svar SX) ->
  ds_in SX (T ^ᵈ SX).
Proof.
  intros.
  replace (T ^ᵈ SX) with ({dtyp_var_f SX /ₛᵈ SX} T ^^ᵈ dtyp_svar SX).
  apply ftv_sins_dtyp_tvar_fstv_sin_dtyp; auto.
  rewrite dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp; auto.
  rewrite dsubst_stv_in_dtyp_fresh_eq; auto.
  simpl. unfold eq_dec. destruct (EqDec_eq_of_X SX SX ); auto.
  - contradiction.
Qed.

Lemma ftv_sin_dtyp_subst_inv : forall X Y T S,
  lc_dtyp S ->
  X <> Y ->
  ds_in X T -> 
  ds_in X ({S /ᵈ Y} T).
Proof.
  intros.
  induction H1; try solve [simpl; eauto].
  - simpl. destruct (X == Y).
    + subst. contradiction.
    + auto.
  - simpl. apply dsin_arrow1; auto.
    apply dsubst_tv_in_dtyp_lc_dtyp; auto.
  - simpl. apply dsin_arrow2; auto.
    apply dsubst_tv_in_dtyp_lc_dtyp; auto.
  - simpl. eapply dsin_all with (L:=L `union` singleton Y).
    intros. inst_cofinites_with Y0.
    rewrite dtyp_subst_open_comm; auto.
Qed.
