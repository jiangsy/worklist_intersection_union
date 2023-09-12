Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import decl.notations.
Require Import ln_utils.

Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.


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
    apply d_subst_tv_in_dtyp_lc_dtyp; auto.
  - simpl. apply dsin_arrow2; auto.
    apply d_subst_tv_in_dtyp_lc_dtyp; auto.
  - simpl. eapply dsin_all with (L:=L `union` singleton Y).
    intros. inst_cofinites_with Y0.
    rewrite dtyp_subst_open_comm; auto.
Qed.

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
Hint Resolve dwf_typ_dwf_typ_s : core.
Hint Resolve dwf_typ_s_dwf_typ : core.

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


Lemma dwf_typ_open_inv : forall E T S X,
  lc_dtyp S ->
  E ⊢ {S /ᵈ X} T ->
  binds X dbind_tvar_empty E ->
  E ⊢ T.
Proof.
  intros. dependent induction H0; auto.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
    - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (X1 == X) in x; subst.
      auto.
      inversion x. subst. auto.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (X0 == X) in x; subst.
      auto.
      inversion x. 
    + inversion x. subst. auto.
  - destruct T; simpl in *; try solve [inversion x].
      destruct (X0 == X) in x.
      subst. auto. inversion x.
    + inversion x. eauto.
  - destruct T; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    + subst. auto.
    + inversion x.
    + inversion x.
      eapply dwftyp_all with (L:=L `union` singleton X `union` ftv_in_dtyp S); intros; 
      inst_cofinites_with X0.
      * rewrite H5 in H2.
        rewrite dtyp_subst_open_comm in H2; auto.
        eapply ftv_sin_dtyp_subst; eauto.
      * eapply H1 with (X:=X) (S:=S); auto.
        -- rewrite H5. rewrite dtyp_subst_open_comm; auto.
  - destruct T; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
  - destruct T; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
Qed.


Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.



Lemma dwf_typ_weakening : forall E1 E2 E3 T, 
  E1 ++ E3 ⊢ T ->
  E1 ++ E2 ++ E3 ⊢ T.
Proof.
  intros.
  dependent induction H; auto.
  - eapply dwftyp_all with (L:=L `union` dom (E1 ++ E2 ++ E3));
    intros; inst_cofinites_with X.
    + auto.
    + replace (X ~ dbind_tvar_empty ++ E1 ++ E2 ++ E3) with ((X ~ dbind_tvar_empty ++ E1) ++ E2 ++ E3) by auto.
    eapply H1; eauto.
Qed.

Corollary dwf_typ_weakening_cons : forall E X b T,
  E ⊢ T ->
  ((X ~ b) ++ E) ⊢ T.
Proof.
  intros.
  replace (X ~ b ++ E) with (nil ++ X ~ b ++ E) by auto.
  now apply dwf_typ_weakening.
Qed.

Lemma dwf_env_binds_dwf_typ : forall E x T,
  ⊢ E ->
  binds x (dbind_typ T) E ->
  E ⊢ T.
Admitted.

Lemma dwft_subst : forall E X T1 T2,
  X ~ dbind_tvar_empty ++ E ⊢ T1 ^ᵈ X ->
  E ⊢ T2 ->
  E ⊢ T1 ^^ᵈ T2.
Admitted.

Hint Constructors d_typing : core.

Lemma d_wft_typ_subst : forall E X F T1 T2,
  F ++ X ~ dbind_tvar_empty ++ E ⊢ T1 ->
  E ⊢ T2 ->
  map (d_subst_tv_in_binding T2 X) F  ++ E ⊢ {T2 /ᵈ X} T1.
Proof.
Admitted.

Lemma d_wf_env_subst_tvar_typ : forall E X F T1,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  E ⊢ T1 ->
  ⊢ (map (d_subst_tv_in_binding T1 X) F ++ E).
Proof.
Admitted.

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
  - simpl. inst_cofinites_by L.
    admit.
Admitted.
    

Lemma dwf_typ_lc_dtyp : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
  intros. induction H; eauto.
Qed.

Hint Resolve d_mono_typ_lc : core.

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

Lemma wft_all_open_wfdtyp_wft : forall E X T1 T2,
  E ⊢ T1 ->
  E ⊢ T2 ->
  E ⊢ {T2 /ᵈ X} T1.
Proof.
  intros E X T1 T2 Hwft1.
  generalize dependent T2.
  dependent induction Hwft1; intros; try solve [simpl; eauto].
  - simpl. destruct (X0 == X); auto.
  - simpl. apply dwftyp_all with (L:=L `union` singleton X); intros.
    inst_cofinites_with X0.
    + rewrite dtyp_subst_open_comm; eauto.
      apply ftv_sin_dtyp_subst_inv; auto.
      eapply dwf_typ_lc_dtyp; eauto.
    + rewrite dtyp_subst_open_comm; eauto.
      eapply H1; auto.
      apply dwf_typ_weakening_cons; eauto.
Qed.

Lemma bind_typ_subst : forall F X E x T1 T2,
  ⊢ F ++ (X, dbind_tvar_empty) :: E ->
  binds x (dbind_typ T1) (F ++ (X, dbind_tvar_empty) :: E) ->
  E ⊢ T2 ->
  binds x (dbind_typ ({T2 /ᵈ X} T1)) (map (d_subst_tv_in_binding T2 X) F ++ E).
Proof.
  intros. induction F; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (E ⊢ T1) by admit.
      rewrite d_subst_tv_in_dtyp_fresh_eq; auto.
      eapply d_new_tv_notin_wf_typ; eauto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      admit.
Admitted.


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


Lemma dsub_dwft : forall E T1 T2,
  E ⊢ T1 <: T2 -> E ⊢ T1 /\ E ⊢ T2.
Proof.
  intros.
  induction H; try solve [intuition].
  - split; eapply dwftyp_all with (L:=L `union` fstv_in_dtyp S1 `union` fstv_in_dtyp T1); intros; inst_cofinites_with X.
    + eapply fstv_open_tvar; auto.
    + apply d_wf_typ_subst_tvar_stvar_cons; intuition.
    + eapply fstv_open_tvar; auto.
    + apply d_wf_typ_subst_tvar_stvar_cons; intuition.
  - split; try solve [intuition].
    + eapply dwftyp_all with (L:=L `union` ftv_in_dtyp S1). 
      * intros. inst_cofinites_with X. auto.
      * intros. inst_cofinites_with X.
        destruct IHd_sub. 
        eapply dwf_typ_open_inv with (X:=X) (S:=T2); auto.
        -- replace (X ~ dbind_tvar_empty ++ E) with (nil ++ X ~ dbind_tvar_empty ++ E) by auto. 
           apply dwf_typ_weakening. simpl. rewrite  d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp.
           ++ simpl. unfold eq_dec. destruct ( EqDec_eq_of_X X X ).
              ** rewrite d_subst_tv_in_dtyp_fresh_eq; auto.
              ** contradiction.
           ++ eapply dwf_typ_dlc_type; eauto.
Qed.