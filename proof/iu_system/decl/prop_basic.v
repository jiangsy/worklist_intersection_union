Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import decl.notations.
Require Import ln_utils.

Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.


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
  rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
  rewrite (d_subst_tv_in_dtyp_fresh_eq T3); auto.
Qed.



Lemma dtyp_subst_open_var : forall X T1 T2,
  lc_dtyp T2 ->
  X `notin` ftv_in_dtyp T1 ->
  {T2 /ᵈ X} T1 ^ᵈ X = T1 ^^ᵈ T2.
Proof.
  intros.
  rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
  rewrite (d_subst_tv_in_dtyp_fresh_eq T1); auto.
  simpl. unfold eq_dec.
  - destruct (EqDec_eq_of_X X X); auto.
    contradiction.
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


Lemma close_dtyp_notin : forall X T,
    X `notin` ftv_in_dtyp (close_dtyp_wrt_dtyp X T).
Proof.
  intros. apply close_dtyp_notin_rec.
Qed.

Lemma d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp_rec_mutual :
(forall T3 T1 T2 SX n1,
  lc_dtyp T1 ->
  d_subst_stv_in_dtyp T1 SX (open_dtyp_wrt_dtyp_rec n1 T2 T3) = open_dtyp_wrt_dtyp_rec n1 (d_subst_stv_in_dtyp T1 SX T2) (d_subst_stv_in_dtyp T1 SX T3)).
Proof.
  apply_mutual_ind dtyp_mutind;
  default_simp.
  rewrite open_dtyp_wrt_dtyp_rec_degree_dtyp_wrt_dtyp; auto.
  apply degree_dtyp_wrt_dtyp_O.
  apply degree_dtyp_wrt_dtyp_of_lc_dtyp. auto.
Qed.


Lemma d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp:
forall T3 T1 T2 SX,
  lc_dtyp T1 ->
  d_subst_stv_in_dtyp T1 SX (open_dtyp_wrt_dtyp T3 T2) = open_dtyp_wrt_dtyp (d_subst_stv_in_dtyp T1 SX T3) (d_subst_stv_in_dtyp T1 SX T2).
Proof.
  unfold open_dtyp_wrt_dtyp; default_simp.
  apply d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp_rec_mutual.
  auto.
Qed.

Lemma d_subst_stv_in_dtyp_fresh_eq :
(forall T2 T1 SX,
  SX `notin` fstv_in_dtyp T2 ->
  d_subst_stv_in_dtyp T1 SX T2 = T2).
Proof.
  apply_mutual_ind dtyp_mutind;
  default_simp.
Qed.

Lemma d_subst_stv_in_dtyp_open_comm : forall SX T3 T1 T2,
  lc_dtyp T3 ->
  SX `notin` fstv_in_dtyp T2 ->
  ({T3 /ₛᵈ SX} T1) ^^ᵈ T2 = {T3 /ₛᵈ SX} T1 ^^ᵈ T2.
Proof.
  intros.
  rewrite d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp.
  rewrite (d_subst_stv_in_dtyp_fresh_eq T2); auto.
  auto.
Qed.

Lemma dtyp_subst_open_stvar : forall SX T1 T2,
  lc_dtyp T2 ->
  SX `notin` fstv_in_dtyp T1 ->
  {T2 /ₛᵈ SX} T1 ^^ᵈ (dtyp_svar SX) = T1 ^^ᵈ T2.
Proof.
  intros.
  rewrite d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp; auto.
  rewrite (d_subst_stv_in_dtyp_fresh_eq T1); auto.
  simpl. unfold eq_dec.
  - destruct (EqDec_eq_of_X SX SX); auto.
    contradiction.
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
    rewrite d_subst_stv_in_dtyp_open_comm; auto.
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
    now apply d_subst_tv_in_dtyp_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply d_subst_tv_in_dtyp_lc_dtyp.
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

Lemma ftv_sin_dtyp_subst : forall X Y T1 S1,
  lc_dtyp S1 ->
  X `notin` ftv_in_dtyp S1 ->
  X <> Y ->
  ds_in X ({S1 /ᵈ Y} T1) ->
  ds_in X T1.
Proof.
  intros. dependent induction H2; simpl; auto.
  - destruct T1; simpl; try solve [inversion x].
    inversion x. destruct (X0 == Y).
    + subst. simpl in *.
      apply notin_singleton_1 in H0. contradiction.
    + inversion H3. auto.
  - destruct T1; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0.
      eapply IHds_in with (S1:=T0) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply dsin_arrow1; inversion x; eauto.
      subst.
      eapply lc_dtyp_subst; eauto.
  - destruct T1; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0. eapply IHds_in with (S1:=T2) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply dsin_arrow2; inversion x; eauto.
      subst. eapply lc_dtyp_subst; eauto.
  - destruct T1; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (dtyp_all T)).
      * eapply dsin_all with (L:=L). intros. inst_cofinites_with Y0.
        auto.
      * apply sin_in in H4. contradiction.
    + inversion x.
    + apply dsin_all with (L:=L `union` singleton Y); intros; inst_cofinites_with Y0. auto.
     inversion x. rewrite H6 in H3.
    eapply H2; eauto. subst. rewrite dtyp_subst_open_comm; auto.
  - destruct T1; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (dtyp_union T0 T2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_union.
      * eapply IHds_in1 with (S1:=S1) (Y:=Y); eauto.
      * eapply IHds_in2 with (S1:=S1) (Y:=Y); eauto.
  - destruct T1; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (dtyp_intersection T0 T2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_intersection.
      * eapply IHds_in1 with (S1:=S1) (Y:=Y); eauto.
      * eapply IHds_in2 with (S1:=S1) (Y:=Y); eauto.
Qed.

Lemma fstv_sin_dtyp_subst_tv : forall SX X T T',
  ds_in_s SX T ->
  lc_dtyp T' ->
  ds_in_s SX ({T' /ᵈ X} T).
Proof.
  intros.
  induction H; simpl; auto.
  - apply dsins_arrow1; auto.
    now apply d_subst_tv_in_dtyp_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply d_subst_tv_in_dtyp_lc_dtyp.
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
    rewrite d_subst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma fstv_sins_dtyp_subst_stv : forall SX X T1 T2,
  ds_in X T1 ->
  lc_dtyp T2 ->
  ds_in X ({T2 /ₛᵈ SX} T1).
Proof.
  intros.
  induction H; simpl; auto.
  - apply dsin_arrow1; auto.
    now apply dsubst_stv_lc_dtyp.
  - apply dsin_arrow2; auto.
    now apply dsubst_stv_lc_dtyp.
  - simpl in H.
    apply dsin_all with (L:=L `union` singleton X). intros.
    rewrite d_subst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma fstv_sins_dtyp_subst_stv_s : forall SX X T1 T2,
    ds_in_s X T1 ->
    X <> SX ->
    lc_dtyp T2 ->
    ds_in_s X ({T2 /ₛᵈ SX} T1).
Proof.
  intros.
  induction H; simpl; auto.
  - case_if*.
  - apply dsins_arrow1; auto.
    now apply dsubst_stv_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply dsubst_stv_lc_dtyp.
  - simpl in H.
    apply dsins_all with (L:=L `union` singleton SX). intros.
    rewrite d_subst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma fstv_open_tvar : forall T SX,
  SX `notin` fstv_in_dtyp T ->
  ds_in_s SX (T ^^ᵈ dtyp_svar SX) ->
  ds_in SX (T ^ᵈ SX).
Proof.
  intros.
  replace (T ^ᵈ SX) with ({dtyp_var_f SX /ₛᵈ SX} T ^^ᵈ dtyp_svar SX).
  apply ftv_sins_dtyp_tvar_fstv_sin_dtyp; auto.
  rewrite d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp; auto.
  rewrite d_subst_stv_in_dtyp_fresh_eq; auto.
  simpl. unfold eq_dec. destruct (EqDec_eq_of_X SX SX ); auto.
  - contradiction.
Qed.

Lemma ftv_sin_dtyp_subst_inv : forall X Y T1 S1,
  lc_dtyp S1 ->
  X <> Y ->
  ds_in X T1 ->
  ds_in X ({S1 /ᵈ Y} T1).
Proof.
  intros.
  induction H1; try solve [simpl; eauto].
  - simpl. destruct (X == Y).
    + subst. contradiction.
    + auto.
  - simpl. apply dsin_arrow1; auto.
    apply d_subst_tv_in_dtyp_lc_dtyp; auto.
  - simpl. apply dsin_arrow2; auto.
    apply d_subst_tv_in_dtyp_lc_dtyp; auto.
  - simpl. eapply dsin_all with (L:=L `union` singleton Y).
    intros. inst_cofinites_with Y0.
    rewrite dtyp_subst_open_comm; auto.
Qed.

Lemma ds_in_s_regular : forall a b,
    ds_in_s a b -> lc_dtyp b.
Proof with eauto.
  intros* HD.
  induction* HD.
Qed.

#[local] Hint Immediate ds_in_s_regular : core.


Lemma d_mono_typ_lc : forall T,
  dmono_typ T -> lc_dtyp T.
Proof.
  intros; induction H; auto.
Qed.

(* Lemma ftv_in_dtyp_stvar_fstv_in_dtyp : forall X T,
  X `in` ftv_in_dtyp T ->
  X `in` fstv_in_dtyp ({dtyp_svar X /ᵈ X} T).
Proof.
  intros.
  induction T; auto.
  - simpl. destruct (X0 == X).
    + simpl. auto.
    + simpl in H.
      specialize (notin_singleton_2 _ _ n).
      intros. contradiction.
  - simpl. destruct (SX == X).
    + subst. auto.
    + simpl in H.
      apply notin_empty in H. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed.

Lemma fstv_in_dtyp_subst_tv : forall SX X T T',
  SX `in` fstv_in_dtyp T ->
  SX `in` fstv_in_dtyp ({T' /ᵈ X} T).
Proof.
  intros.
  induction T; auto.
  - simpl. destruct (X0 == X).
    + subst. simpl in *. apply notin_empty in H.  contradiction.
    + simpl in H.
      apply notin_empty in H. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed.

Lemma fstv_in_dtyp_tvar_ftv_in_dtyp : forall SX T,
  SX `in` fstv_in_dtyp T ->
  SX `in` ftv_in_dtyp ({dtyp_var_f SX /ₛᵈ SX} T).
Proof.
  intros.
  induction T; auto.
  - simpl in *.
    apply notin_empty in H. contradiction.
  - simpl. destruct (SX0 == SX).
    + subst. auto.
    + simpl in H.
      apply AtomSetImpl.singleton_1 in H.
      subst. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed. *)

(* Lemma fstv_in_dtyp_subst_tv : forall SX X T T',
  SX `in` fstv_in_dtyp T ->
  SX `in` fstv_in_dtyp ({T' /ᵈ X} T).
Proof.
  intros.
  induction T; auto.
  - simpl. destruct (X0 == X).
    + subst. simpl in *. apply notin_empty in H.  contradiction.
    + simpl in H.
      apply notin_empty in H. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed. *)



Lemma d_wf_typ_subst_tvar_stvar : forall E F X T,
  E ++ [(X, dbind_tvar_empty)] ++ F  ⊢ₛ T  ->
  map (d_subst_tv_in_binding (dtyp_svar X) X ) E ++ [(X, dbind_stvar_empty)] ++ F ⊢ₛ { dtyp_svar X /ᵈ X } T.
Proof.
  intros E F X T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
    + econstructor; auto.
    + econstructor.
      induction E.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. constructor.
    induction E.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. constructor.
    + apply IHdwf_typ_s1; auto.
    + apply IHdwf_typ_s2; auto.
  - simpl. eapply dwftyps_all with (L:=L);
    intros; inst_cofinites_with SX.
    + replace  (({dtyp_svar X /ᵈ X} T1) ^^ᵈ dtyp_svar SX) with ({dtyp_svar X /ᵈ X} T1 ^^ᵈ dtyp_svar SX).
    apply fstv_sin_dtyp_subst_tv. auto.
    auto.
    rewrite dtyp_subst_open_comm; auto.
    + replace (SX ~ dbind_stvar_empty ++
    map (d_subst_tv_in_binding (dtyp_svar X) X) E ++ (X, dbind_stvar_empty) :: F
    ) with (
    map (d_subst_tv_in_binding (dtyp_svar X) X) (SX ~ dbind_stvar_empty ++ E) ++ (X, dbind_stvar_empty) :: F
    ) by auto.
    replace (({dtyp_svar X /ᵈ X} T1) ^^ᵈ dtyp_svar SX) with
    ({dtyp_svar X /ᵈ X} T1 ^^ᵈ dtyp_svar SX).
    apply H1. auto.
    rewrite dtyp_subst_open_comm; auto.
  - simpl. constructor.
    + apply IHdwf_typ_s1; auto.
    + apply IHdwf_typ_s2; auto.
  - simpl. constructor.
    + apply IHdwf_typ_s1; auto.
    + apply IHdwf_typ_s2; auto.
Qed.


Lemma d_wf_typ_subst_stvar_tvar : forall E F SX T,
  E ++ [(SX, dbind_stvar_empty)] ++ F  ⊢ T  ->
  map (d_subst_stv_in_binding (dtyp_var_f SX) SX ) E ++ [(SX, dbind_tvar_empty)] ++ F ⊢ { dtyp_var_f SX /ₛᵈ SX } T.
Proof.
  intros E F SX T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. constructor.
    induction E.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X SX0 SX).
    + econstructor; auto.
    + econstructor.
      induction E.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. constructor.
    + apply IHdwf_typ1; auto.
    + apply IHdwf_typ2; auto.
  - simpl. eapply dwftyp_all with (L:=L);
    intros; inst_cofinites_with X.
    + replace  (({`ᵈ SX /ₛᵈ SX} T) ^ᵈ X) with ({`ᵈ SX /ₛᵈ SX} T ^ᵈ X).
      apply fstv_sins_dtyp_subst_stv; auto.
      rewrite d_subst_stv_in_dtyp_open_comm; auto.
    + replace (X ~ dbind_tvar_empty ++
    map (d_subst_stv_in_binding `ᵈ SX SX) E ++ (SX, dbind_tvar_empty) :: F) with (
    map (d_subst_stv_in_binding `ᵈ SX SX) (X ~ dbind_tvar_empty ++ E) ++ (SX, dbind_tvar_empty) :: F) by auto.
      replace (({`ᵈ SX /ₛᵈ SX} T) ^ᵈ X) with ({`ᵈ SX /ₛᵈ SX} T ^ᵈ X).
      apply H1. auto.
      rewrite d_subst_stv_in_dtyp_open_comm; auto.
  - simpl. constructor.
    + apply IHdwf_typ1; auto.
    + apply IHdwf_typ2; auto.
  - simpl. constructor.
    + apply IHdwf_typ1; auto.
    + apply IHdwf_typ2; auto.
Qed.

Corollary d_wf_typ_subst_stvar_tvar_cons : forall E X T,
  X `notin` ftv_in_dtyp T ->
  X ~ dbind_tvar_empty ++ E ⊢ₛ T ^ᵈ X ->
  X ~ dbind_stvar_empty ++ E ⊢ₛ T ^^ᵈ dtyp_svar X.
Proof.
  intros.
  replace (X ~ dbind_tvar_empty ++ E) with (nil ++ X ~ dbind_tvar_empty ++ E) in H0 by auto.
  specialize (d_wf_typ_subst_tvar_stvar _ _ _ _ H0).
  intros.
  rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp in H1.
  simpl in H1.
  unfold eq_dec in H1. destruct (EqDec_eq_of_X X X).
  - rewrite d_subst_tv_in_dtyp_fresh_eq in H1; auto.
  - contradiction.
  - auto.
Qed.

Corollary d_wf_typ_subst_tvar_stvar_cons : forall E SX T,
  SX `notin` fstv_in_dtyp T ->
  SX ~ dbind_stvar_empty ++ E ⊢ T ^^ᵈ dtyp_svar SX ->
  SX ~ dbind_tvar_empty ++ E ⊢ T ^ᵈ SX.
Proof.
  intros.
  replace (SX ~ dbind_stvar_empty ++ E) with (nil ++ SX ~ dbind_stvar_empty ++ E) in H0 by auto.
  specialize (d_wf_typ_subst_stvar_tvar _ _ _ _ H0). intros.
  rewrite d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp in H1; auto. simpl in H1. unfold eq_dec in H1. destruct (EqDec_eq_of_X SX SX).
  - rewrite d_subst_stv_in_dtyp_fresh_eq in H1; auto.
  - contradiction.
Qed.

Lemma dwf_typ_dwf_typ_s : forall E T,
  E ⊢ T -> E ⊢ₛ T.
Proof.
  intros.
  induction H; auto.
  - eapply dwftyps_all with (L:= (L `union` ftv_in_dtyp T));
    intros; inst_cofinites_with SX.
    + replace (T ^^ᵈ dtyp_svar SX) with ({dtyp_svar SX /ᵈ SX}T ^ᵈ SX).
      now apply ftv_sin_dtyp_stvar_fstv_sin_dtyp.
      rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X SX SX).
      * rewrite d_subst_tv_in_dtyp_fresh_eq; auto.
      * contradiction.
    + apply d_wf_typ_subst_stvar_tvar_cons; auto.
Qed.

Lemma dwf_typ_s_dwf_typ : forall E T,
  E ⊢ₛ T -> E ⊢ T.
Proof.
  intros. induction H; auto.
  - eapply dwftyp_all with (L:= (L `union` fstv_in_dtyp T1));
    intros; inst_cofinites_with X.
    + eapply fstv_open_tvar; auto.
    + eapply d_wf_typ_subst_tvar_stvar_cons; auto.
Qed.

Hint Constructors d_sub : core.
Hint Immediate dwf_typ_dwf_typ_s : core.
Hint Immediate dwf_typ_s_dwf_typ : core.

Lemma dwf_typ_dlc_type : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
  intros; induction H; auto.
Qed.

Lemma dwf_typ_s_dlc_type : forall E T,
  E ⊢ₛ T -> lc_dtyp T.
Proof.
  intros.
  eapply dwf_typ_dlc_type.
  apply dwf_typ_s_dwf_typ.
  eauto.
Qed.

Hint Resolve dwf_typ_s_dlc_type : core.

Hint Constructors dneq_union : Core.
Hint Constructors dneq_intersection : Core.


Lemma dwf_typ_open_inv : forall E T1 S1 X,
  lc_dtyp S1 ->
  E ⊢ {S1 /ᵈ X} T1 ->
  binds X dbind_tvar_empty E ->
  E ⊢ T1.
Proof.
  intros. dependent induction H0; auto.
  - destruct T1; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T1; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T1; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T1; simpl in *; try solve [inversion x].
    + destruct (X1 == X) in x; subst.
      auto.
      inversion x. subst. auto.
  - destruct T1; simpl in *; try solve [inversion x].
    + destruct (X0 == X) in x; subst.
      auto.
      inversion x.
    + inversion x. subst. auto.
  - destruct T1; simpl in *; try solve [inversion x].
      destruct (X0 == X) in x.
      subst. auto. inversion x.
    + inversion x. eauto.
  - destruct T1; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    + subst. auto.
    + inversion x.
    + inversion x.
      eapply dwftyp_all with (L:=L `union` singleton X `union` ftv_in_dtyp S1); intros;
      inst_cofinites_with X0.
      * rewrite H5 in H2.
        rewrite dtyp_subst_open_comm in H2; auto.
        eapply ftv_sin_dtyp_subst; eauto.
      * eapply H1 with (X:=X) (S1:=S1); auto.
        -- rewrite H5. rewrite dtyp_subst_open_comm; auto.
  - destruct T1; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
  - destruct T1; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
Qed.


Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.



Lemma dwf_typ_weakening : forall E1 E2 E3 T,
  E3 ++ E1 ⊢ T ->
  (* uniq (E3 ++ E2 ++ E1) -> *)
  E3 ++ E2 ++ E1 ⊢ T.
Proof.
  intros.
  dependent induction H; auto.
  - eapply dwftyp_all with (L:=L `union` dom (E3 ++ E2 ++ E1));
    intros; inst_cofinites_with X.
    + auto.
    + replace (X ~ dbind_tvar_empty ++ E3 ++ E2 ++ E1) with ((X ~ dbind_tvar_empty ++ E3) ++ E2 ++ E1) by auto.
    eapply H1; eauto.
Qed.

Corollary dwf_typ_weakening_cons : forall E X b T,
  E ⊢ T ->
  (* uniq ((X ~ b) ++ E) -> *)
  ((X ~ b) ++ E) ⊢ T.
Proof.
  intros.
  replace (X ~ b ++ E) with (nil ++ X ~ b ++ E) by auto.
  apply dwf_typ_weakening; auto.
Qed.

Corollary dwf_typ_weaken_head: forall E1 E2 T,
  E1 ⊢ T ->
  (* uniq (E2 ++ E1) -> *)
  E2 ++ E1 ⊢ T.
Proof.
  intros.
  rewrite_env (nil++E2++E1).
  applys* dwf_typ_weakening.
Qed.

Lemma d_wf_env_uniq: forall E,
  ⊢ E -> uniq E.
Proof.
  intros.
  induction H; auto.
Qed.

Lemma d_wf_env_strenthening : forall E X F,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  ⊢ F ++ E.
Abort.
(* Wrong Lemma F = (y : X) *)

Lemma d_wf_env_strenthening_head : forall a E,
    ⊢ a :: E -> ⊢ E.
Proof with auto.
  intros * H.
  inverts* H.
Qed.

Hint Resolve d_wf_env_uniq : core.
Hint Resolve dwf_typ_weakening_cons : core.

Lemma dwf_env_binds_dwf_typ : forall E x T,
  ⊢ E ->
  x ~ T ∈ E ->
  E ⊢ T.
Proof.
  intros.
  dependent induction H.
  - inversion H0.
  - simpl in H1. inversion H1.
    + inversion H2.
    + auto.
  - inversion H1.
    + inversion H2.
    + auto.
  - inversion H2.
    + dependent destruction H3. auto.
    + simpl in *. apply IHdwf_env in H3.
      apply dwf_typ_weakening_cons; auto.
Qed.

(* Lemma dwft_subst : forall E X T1 T2,
  X ~ dbind_tvar_empty ++ E ⊢ T1 ^ᵈ X ->
  E ⊢ T2 ->
  E ⊢ T1 ^^ᵈ T2.
Admitted. *)

Hint Constructors d_typing : core.

Lemma d_wft_typ_swap_env : forall F X Y E T ,
    F ++ X ~ dbind_tvar_empty ++ Y ~ dbind_tvar_empty ++ E ⊢ T ->
    F ++ Y ~ dbind_tvar_empty ++ X ~ dbind_tvar_empty ++ E ⊢ T.
Proof with eauto.
  intros * HT.
  inductions HT...
  - forwards* [?|?]: binds_app_1 H.
    forwards* [?|?]: binds_app_1 H0.
  - forwards* [?|?]: binds_app_1 H.
    forwards* [?|?]: binds_app_1 H0.
  - pick fresh y and apply dwftyp_all. inst_cofinites_with y.
    applys* H.
    rewrite_env ((y ~ dbind_tvar_empty ++ F) ++ Y ~ dbind_tvar_empty ++ X ~ dbind_tvar_empty ++ E ).
    applys* H1.
Qed.

Lemma d_wft_typ_subst : forall E X F T1 T2,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  F ++ X ~ dbind_tvar_empty ++ E ⊢ T1 ->
  E ⊢ T2 ->
  map (d_subst_tv_in_binding T2 X) F  ++ E ⊢ {T2 /ᵈ X} T1.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; forwards: d_wf_env_uniq Hwfenv; try solve [simpl; auto]...
  - destruct (X0 == X).
    + subst. simpl. applys* dwf_typ_weaken_head.
      (* solve_uniq. *)
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (d_subst_tv_in_binding T2 X) H1...
      * apply binds_cons_iff in H1. iauto.
  - econstructor.
    forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (d_subst_tv_in_binding T2 X) H1.
    forwards* [(?&?&?)|?]: binds_cons_uniq_1 H1...
  - simpl. inst_cofinites_for dwftyp_all; intros; inst_cofinites_with X0.
    + rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_var...
      applys* ftv_sin_dtyp_subst_inv.
    + rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp_var...
      replace ((X0, dbind_tvar_empty) :: map (d_subst_tv_in_binding T2 X) F ++ E)
      with (map (d_subst_tv_in_binding T2 X) ((X0, dbind_tvar_empty) :: F) ++ E) by auto.
      apply H1; auto...
      econstructor...
Qed.


Lemma d_wft_typ_subst_stvar : forall E SX F T1 T2,
  ⊢ F ++ SX ~ dbind_stvar_empty ++ E ->
  F ++ SX ~ dbind_stvar_empty ++ E ⊢ T1 ->
  E ⊢ T2 ->
  map (d_subst_stv_in_binding T2 SX) F  ++ E ⊢ {T2 /ₛᵈ SX} T1.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2, binds_app_1, binds_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; forwards: d_wf_env_uniq Hwfenv; try solve [simpl; auto]...
  - forwards* [?|?]: binds_app_1 H...
    * forwards: binds_map_2 (d_subst_stv_in_binding T2 SX) H1...
    * apply binds_cons_iff in H1. destruct H1...
        ** inverts* H1...
  - destruct (SX0 == SX); subst...
    + subst. simpl. applys* dwf_typ_weaken_head.
      (* solve_uniq. *)
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (d_subst_stv_in_binding T2 SX) H1...
      * apply binds_cons_iff in H1. iauto.
  - simpl. inst_cofinites_for dwftyp_all; intros; inst_cofinites_with X.
    + rewrite d_subst_stv_in_dtyp_open_comm...
      applys fstv_sins_dtyp_subst_stv...
    + rewrite d_subst_stv_in_dtyp_open_comm...
      replace ((X, dbind_tvar_empty) :: map (d_subst_stv_in_binding T2 SX) F ++ E)
      with (map (d_subst_stv_in_binding T2 SX) ((X, dbind_tvar_empty) :: F) ++ E) by auto.
      apply H1; auto...
      econstructor...
Qed.


Lemma d_new_tv_notin_wf_typ : forall X E T1,
  ⊢ (X, dbind_tvar_empty) :: E ->
  E ⊢ T1 ->
  X `notin` ftv_in_dtyp T1.
Proof.
  intros; induction H0; auto.
  - simpl. destruct (X0 == X).
    + subst. dependent destruction H.
      simpl in *. exfalso.
      eapply binds_dom_contradiction; eauto.
    + apply notin_singleton; auto.
  - simpl. inst_cofinites_by (L `union` singleton X `union` dom E) using_name X.
    assert (⊢ (X, dbind_tvar_empty) :: X0 ~ dbind_tvar_empty ++ E).
    constructor; auto.
    + constructor; auto. dependent destruction H; auto.
    + simpl. apply notin_add_3; auto.
      dependent destruction H; auto.
    + specialize (H2 H3).
      rewrite ftv_in_dtyp_open_dtyp_wrt_dtyp_lower; auto.
Qed.

Lemma dwf_typ_lc_dtyp : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
  intros. induction H; eauto.
Qed.

#[export] Hint Resolve d_mono_typ_lc : core.

Lemma d_mono_typ_neq_all : forall T,
  dmono_typ T -> dneq_all T.
Proof.
  intros; induction H; auto...
Qed.

Lemma d_neq_all_subst_neq_all : forall T1 X T2,
  lc_dtyp T1 ->
  dmono_typ T2 ->
  dneq_all T1 ->
  dneq_all ( {T2 /ᵈ X} T1 ).
Proof.
  intros. induction H; simpl; eauto...
  - destruct (X0 == X); auto.
    apply d_mono_typ_neq_all; auto.
  - eapply dneqall_arrow;
    apply d_subst_tv_in_dtyp_lc_dtyp; eauto...
  - inversion H1.
  - eapply dneqall_union;
    apply d_subst_tv_in_dtyp_lc_dtyp; eauto...
  - eapply dneqall_intersection;
    apply d_subst_tv_in_dtyp_lc_dtyp; eauto...
Qed.


Lemma bind_typ_subst : forall F X E x T1 T2,
  ⊢ F ++ (X, dbind_tvar_empty) :: E ->
  x ~ T1 ∈ (F ++ (X, dbind_tvar_empty) :: E) ->
  E ⊢ T2 ->
  x ~ ({T2 /ᵈ X} T1) ∈ (map (d_subst_tv_in_binding T2 X) F ++ E).
Proof.
  intros. induction F; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (E ⊢ T1).
      { eapply dwf_env_binds_dwf_typ; eauto. inversion H. auto. }
      rewrite d_subst_tv_in_dtyp_fresh_eq; auto.
      eapply d_new_tv_notin_wf_typ; eauto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      apply IHF; auto.
      inversion H; auto.
Qed.


Lemma d_mono_typ_subst_mono_mono : forall T1 T2 X,
  dmono_typ T1 ->
  dmono_typ T2 ->
  dmono_typ ({T2 /ᵈ X} T1).
Proof.
  intros. induction T1; try solve [simpl; eauto].
  - simpl. destruct (X0 == X); auto.
  - simpl. dependent destruction H. auto.
  - inversion H.
  - simpl. dependent destruction H. auto.
  - simpl. dependent destruction H. auto.
Qed.


Lemma d_sub_dwft : forall E T1 T2,
  E ⊢ T1 <: T2 -> ⊢ E /\ E ⊢ T1 /\ E ⊢ T2.
Proof with auto.
  intros.
  induction H; try solve [intuition].
  - split.
    inst_cofinites_by L. intuition... inversion H3. auto.
    split; inst_cofinites_for dwftyp_all; intros; inst_cofinites_with X.
    + eapply fstv_open_tvar; auto.
    + applys* d_wf_typ_subst_tvar_stvar_cons. auto.
    + eapply fstv_open_tvar; auto.
    + applys* d_wf_typ_subst_tvar_stvar_cons. auto.
  - split; try solve [intuition].
    split; try solve [intuition].
    + eapply dwftyp_all with (L:=L `union` ftv_in_dtyp S1 `union` dom E).
      * intros. inst_cofinites_with X. auto.
      * intros. inst_cofinites_with X.
        destruct IHd_sub. auto.
        eapply dwf_typ_open_inv with (X:=X) (S1:=T2); auto.
        -- replace (X ~ dbind_tvar_empty ++ E) with (nil ++ X ~ dbind_tvar_empty ++ E) by auto.
           apply dwf_typ_weakening. simpl. rewrite  d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp.
           ++ simpl. unfold eq_dec. destruct ( EqDec_eq_of_X X X ).
              ** rewrite d_subst_tv_in_dtyp_fresh_eq; intuition.
              ** contradiction.
           ++ eapply dwf_typ_dlc_type; eauto.
           (* ++ auto. *)
Qed.


Lemma dwf_typ_strengthening : forall F E x T b,
    ⊢ E ++ x ~ b ++ F ->
    E ++ x ~ b ++ F ⊢ T ->
    x \notin ftv_in_dtyp T ->
    x \notin fstv_in_dtyp T ->
    E ++ F ⊢ T.
Proof with eauto.
  intros * Hwfenv H. intros.
  dependent induction H; auto.
  - induction E.
    + inversion H. dependent destruction H2.
      simpl in H0. apply notin_singleton_1 in H0. contradiction.
      auto.
    + destruct a. inversion H.
      * dependent destruction H2. auto.
      * simpl. apply dwf_typ_weakening_cons. apply IHE; auto.
        rewrite_env ((a, b0) :: (E ++ x ~ b ++ F)) in Hwfenv. applys* d_wf_env_strenthening_head.
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - induction E.
    + inversion H. dependent destruction H2.
      * simpl in H1. apply notin_singleton_1 in H1. contradiction.
      * auto.
    + destruct a. inversion H.
      * dependent destruction H2. auto.
      * simpl. apply dwf_typ_weakening_cons; auto. apply IHE; auto.
        rewrite_env ((a, b0) :: (E ++ x ~ b ++ F)) in Hwfenv. applys* d_wf_env_strenthening_head.
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - simpl in *. constructor.
    + apply notin_union_1 in H1.
      eauto.
    + apply notin_union_2 in H1.
      eauto.
  - simpl in *.
    apply dwftyp_all with (L:=L `union` singleton x `union` dom E `union` dom F); intros; inst_cofinites_with X.
    + auto.
    + replace (X ~ dbind_tvar_empty ++ E ++ F) with ((X ~ dbind_tvar_empty ++ E)++ F) by auto. eapply H1 with (x:=x) (b:=b); auto.
      * rewrite_env (X ~ dbind_tvar_empty ++ (E ++ (x, b) :: F)). econstructor...
      * rewrite ftv_in_dtyp_open_dtyp_wrt_dtyp_upper; auto.
      * rewrite fstv_in_dtyp_open_dtyp_wrt_dtyp_upper; auto.
  - simpl in *. eauto.
  - simpl in *. eauto.
Qed.

(* Properties of d_wf_env *)
Lemma d_wf_env_subst_tvar_typ : forall E X F T1,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  E ⊢ T1 ->
  ⊢ (map (d_subst_tv_in_binding T1 X) F ++ E).
Proof with eauto using d_wft_typ_subst.
  intros * HE HT.
  induction F; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, b) :: (F ++ X ~ dbind_tvar_empty ++ E)) in HE.
    forwards HE': d_wf_env_strenthening_head HE.
    forwards~ IH: IHF.
    rewrite_env ([(a, d_subst_tv_in_binding T1 X b)]
                   ++ (map (d_subst_tv_in_binding T1 X) F ++ E)).
    forwards: d_wf_env_uniq HE.
    inverts H. destruct b...
    + econstructor...
      applys d_wft_typ_subst...
      inverts~ HE.
Qed.

(* This lemma cannot be used for svar subst because E ⊢ SY does not hold when SY is not in E *)
Lemma d_wf_env_subst_stvar_typ : forall E SX F T1,
  ⊢ F ++ SX ~ dbind_stvar_empty ++ E ->
  E ⊢ T1 ->
  ⊢ (map (d_subst_stv_in_binding T1 SX) F ++ E).
Proof with eauto using d_wft_typ_subst_stvar.
  intros * HE HT.
  induction F; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, b) :: (F ++ SX ~ dbind_stvar_empty ++ E)) in HE.
    forwards HE': d_wf_env_strenthening_head HE.
    forwards~ IH: IHF.
    rewrite_env ([(a, d_subst_stv_in_binding T1 SX b)]
                   ++ (map (d_subst_stv_in_binding T1 SX) F ++ E)).
    forwards: d_wf_env_uniq HE.
    inverts H. destruct b...
    + econstructor...
      applys d_wft_typ_subst_stvar...
      inverts~ HE.
Qed.


Corollary d_wf_env_weaken_stvar : forall E1 E2 SX,
  ⊢ E2 ++ E1 ->
  SX ∉ dom (E2 ++ E1) ->
  ⊢ E2 ++ SX ~ ▪ ++ E1.
Proof with eauto.
  intros * HE HT. induction E2; intros.
  - econstructor...
  - rewrite_env (a :: (E2 ++ SX ~ ▪ ++ E1)). destruct a. destruct b.
    1: rewrite_env ((a, ▫) :: (E2 ++ E1)) in HE.
    2: rewrite_env ((a, ▪) :: (E2 ++ E1)) in HE.
    3: rewrite_env ((a, dbind_typ T) :: (E2 ++ E1)) in HE.
    all: forwards HE': d_wf_env_strenthening_head HE; inverts HE.
    all: econstructor; try solve_notin.
    applys dwf_typ_weakening...
Qed.

Lemma subst_same_stvar_typ_id : forall SX T,
    {dtyp_svar SX /ₛᵈ SX} T = T.
Proof with (try progress case_if); subst; simpl; eauto.
  intros. induction T; simpl...
  all: try rewrite IHT; try rewrite IHT1; try rewrite IHT2...
Qed.

Lemma subst_same_stvar_binding_id : forall SX a,
    d_subst_stv_in_binding (dtyp_svar SX) SX a = a.
Proof with subst; try rewrite subst_same_stvar_typ_id; simpl; eauto.
  intros. destruct a...
  induction* T...
Qed.

Lemma subst_same_stvar_map_id : forall SX F,
    map (d_subst_stv_in_binding (dtyp_svar SX) SX) F = F.
Proof with subst; try rewrite subst_same_stvar_typ_id; simpl; eauto.
  intros. induction F... destruct a...
  rewrite subst_same_stvar_binding_id. rewrite* IHF.
Qed.

Lemma dom_subst_id : forall T SX F,
    dom (map (d_subst_stv_in_binding T SX) F) = dom F.
Proof with simpl; eauto.
  intros *. induction* F.
  - destruct a. destruct b...
    all: rewrite IHF...
Qed.

Lemma d_wf_typ_rename_stvar : forall E F SX T SY,
  E ++ SX ~ ▪ ++ F  ⊢ T  ->
  map (d_subst_stv_in_binding (dtyp_svar SY) SX ) E ++ SY ~ ▪ ++ F ⊢ { dtyp_svar SY /ₛᵈ SX } T.
Proof with try solve_notin; simpl in *; eauto.
  intros * HT.
  case_eq (SX==SY); intros.
  1: { subst. rewrite* subst_same_stvar_map_id. rewrite subst_same_stvar_typ_id... }
  clear H.
  inductions HT...
  - econstructor. induction E...
    all: inverts H; try solve_by_invert...
    + remember (let (x, a0) := a in (x, d_subst_stv_in_binding (dtyp_svar SY) SX a0)).
      remember (map (d_subst_stv_in_binding (dtyp_svar SY) SX) E ++ (SY, ▪) :: F).
      destruct p. applys binds_cons_3.
      applys IHE...
  - case_if... induction E...
    + econstructor. case_eq (SX0==SY); intros; subst...
      inverts* H. exfalso. applys C. inverts~ H1.
    + destruct a. inverts H.
      * inverts H0...
      * forwards: IHE...
        remember (map (d_subst_stv_in_binding (dtyp_svar SY) SX) E ++ (SY, ▪) :: F).
        rewrite_env ([(a, d_subst_stv_in_binding (dtyp_svar SY) SX b)] ++ l).
        applys* dwf_typ_weaken_head.
  - econstructor; intros; inst_cofinites_with X.
    + forwards: fstv_sins_dtyp_subst_stv SX (dtyp_svar SY) H...
      replace (dtyp_var_f X) with ({dtyp_svar SY /ₛᵈ SX} (dtyp_var_f X)) in *.
      rewrite* <- d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp...
      simpl...
    + intros.
      rewrite d_subst_stv_in_dtyp_open_comm.
      forwards: H1 ((X, ▫) :: E)...
      econstructor. solve_notin.
Qed.


Corollary d_wf_env_rename_stvar : forall E SX F SY,
  ⊢ F ++ SX ~ dbind_stvar_empty ++ E ->
  SY ∉ dom (F ++ E) ->
  ⊢ map (d_subst_stv_in_binding (dtyp_svar SY) SX) F ++ SY ~ dbind_stvar_empty ++ E.
Proof with try solve_notin; simpl; eauto.
  intros * HE HT.
  case_eq (SY == SX); intros.
  1: { subst. rewrite* subst_same_stvar_map_id. } clear H.
  rewrite_env ((F ++ SX ~ ▪) ++ E) in HE.
  forwards HE': d_wf_env_weaken_stvar SY HE. { solve_notin. }
  induction F; intros; simpl.
  - inverts~ HE. econstructor...
  - destruct a. destruct b...
    + rewrite_env (((a, ▫) :: (F ++ SX ~ ▪) ++ E)) in HE. inverts~ HE.
      rewrite_env ((a, ▫) :: (F ++ SX ~ ▪) ++ (SY, ▪) :: E) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, ▪) :: (F ++ SX ~ ▪) ++ E)) in HE. inverts~ HE.
      rewrite_env ((a, ▪) :: (F ++ SX ~ ▪) ++ (SY, ▪) :: E) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, dbind_typ T) :: (F ++ SX ~ ▪) ++ E)) in HE. inverts~ HE.
      rewrite_env ((a, dbind_typ T) :: (F ++ SX ~ ▪) ++ (SY, ▪) :: E) in HE'. inverts~ HE'.
      econstructor...
      forwards*: IHF. solve_notin.
      applys d_wf_typ_rename_stvar...
      rewrite_env ((F ++ SX ~ ▪) ++ E)...
Qed.
Lemma d_neq_all_rename: forall T SX SY,
  lc_dtyp T ->
  dneq_all T ->
  dneq_all ({dtyp_svar SY /ₛᵈ SX} T).
Proof with  simpl; eauto using dsubst_stv_lc_dtyp; try solve_by_invert.
  intros. destruct T...
  - case_if; subst*.
  - eapply dneqall_arrow;
      applys dsubst_stv_lc_dtyp...
    all: inverts~ H.
  - econstructor; applys dsubst_stv_lc_dtyp; try inverts~ H...
  - econstructor; applys dsubst_stv_lc_dtyp; try inverts~ H...
Qed.

Lemma d_neq_intersection_rename: forall T SX SY,
  lc_dtyp T ->
  dneq_intersection T ->
  dneq_intersection ({dtyp_svar SY /ₛᵈ SX} T).
Proof with  simpl; eauto using dsubst_stv_lc_dtyp; try solve_by_invert.
  intros. destruct T...
  - case_if; subst*.
  - eapply dneqintersection_arrow;
      applys dsubst_stv_lc_dtyp...
    all: inverts~ H.
  - econstructor.
    forwards*: dsubst_stv_lc_dtyp SX (dtyp_all T) (dtyp_svar SY).
  - econstructor; applys dsubst_stv_lc_dtyp; try inverts~ H...
Qed.


Lemma d_neq_union_rename: forall T SX SY,
  lc_dtyp T ->
  dneq_union T ->
  dneq_union ({dtyp_svar SY /ₛᵈ SX} T).
Proof with  simpl; eauto using dsubst_stv_lc_dtyp; try solve_by_invert.
  intros. destruct T...
  - case_if; subst*.
  - eapply dnequnion_arrow;
      applys dsubst_stv_lc_dtyp...
    all: inverts~ H.
  - econstructor.
    forwards*: dsubst_stv_lc_dtyp SX (dtyp_all T) (dtyp_svar SY).
  - econstructor; applys dsubst_stv_lc_dtyp; try inverts~ H...
Qed.

Lemma rename_mono_typ : forall T SX SY,
    dmono_typ T ->
    {dtyp_svar SY /ₛᵈ SX} T = T.
Proof with simpl in *; eauto.
  intros * HM.
  induction HM...
  all: try rewrite IHHM1; try rewrite IHHM2...
Qed.

#[export] Hint Resolve d_neq_all_rename d_neq_intersection_rename d_neq_union_rename rename_mono_typ : sub.


Lemma dneq_all_lc_dtyp : forall T,
  dneq_all T -> lc_dtyp T.
Proof.
  intros. induction H; eauto.
Qed.

Lemma dneq_intersection_lc_dtyp : forall T,
  dneq_intersection T -> lc_dtyp T.
Proof.
  intros. induction H; eauto.
Qed.


Lemma dneq_union_lc_dtyp : forall T,
  dneq_union T -> lc_dtyp T.
Proof.
  intros. induction H; eauto.
Qed.

#[export] Hint Immediate dneq_all_lc_dtyp dneq_intersection_lc_dtyp dneq_union_lc_dtyp : core.
