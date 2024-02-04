Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import uni.notations.
Require Import ln_utils.

Hint Constructors d_wf_typ: core.
Hint Constructors d_wf_env: core.
Hint Constructors d_wf_typ_s: core.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.


Lemma subst_same_tvar_eq : forall A X,
  A = {` X /ᵗ X} A.
Proof.
  intros.
  induction A; auto; simpl.
  - destruct (X0==X); subst; auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. rewrite <- IHA. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
Qed.

Lemma typ_subst_open_comm : forall X A T B,
  lc_typ T ->
  X `notin` ftvar_in_typ B ->
  ({T /ᵗ X} A) ^^ᵈ B = {T/ᵗ X} A ^^ᵈ B.
Proof.
  intros.
  rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq B); auto.
Qed.


Lemma typ_subst_open_var : forall X A T,
  lc_typ T ->
  X `notin` ftvar_in_typ A ->
  {T /ᵗ X} A ^ᵈ X = A ^^ᵈ T.
Proof.
  intros.
  rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq A); auto.
  simpl. unfold eq_dec.
  - destruct (EqDec_eq_of_X X X); auto.
    contradiction.
Qed.


Lemma open_typ_wrt_typ_twice : forall n X Y A,
    lc_typ Y ->
    open_typ_wrt_typ_rec n ` X (open_typ_wrt_typ_rec (n+1) Y A)
    = open_typ_wrt_typ_rec n Y (open_typ_wrt_typ_rec n ` X A).
Proof with subst; simpl in *; eauto; try lia.
  introv HL. gen n. induction A; intros...
  all: try congruence.
  - destruct (lt_eq_lt_dec n (n0 + 1)); repeat case_if...
    + remember (lt_eq_lt_dec n n0) as m.
      destruct m... case_if; simpl; try rewrite <- Heqm...
    + remember (lt_eq_lt_dec (n0 + 1) n0) as m; destruct m; repeat case_if...
      remember (lt_eq_lt_dec (n0 + 1 - 1) n0) as m; destruct m; repeat case_if...
      rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ...
      applys degree_typ_wrt_typ_O. applys degree_typ_wrt_typ_of_lc_typ_mutual...
    + remember (lt_eq_lt_dec n n0) as m.
      destruct m... case_if; simpl; try rewrite <- Heqm...
      remember (lt_eq_lt_dec (n - 1) n0) as m.
      destruct m... case_if; simpl; try rewrite <- Heqm...
  - forwards: IHA (S n).
    replace (Datatypes.S (n + 1)) with (Datatypes.S n +1).
    rewrite H. congruence. lia.
Qed.



Lemma typ_open_r_close_l : forall T1 T2 X
  , X `notin` ftvar_in_typ T2
  -> T1 = open_typ_wrt_typ T2 ` X -> close_typ_wrt_typ X T1 = T2.
Proof.
  intros * Fr H.
  assert (close_typ_wrt_typ X T1 = close_typ_wrt_typ X (open_typ_wrt_typ T2 ` X)) by now rewrite H.
  now rewrite close_typ_wrt_typ_open_typ_wrt_typ in H0.
Qed.


Lemma close_typ_notin_rec : forall X A n,
    X `notin` ftvar_in_typ (close_typ_wrt_typ_rec n X A).
Proof.
  intros until A.
  induction A; simpl; intros; auto.
  - destruct (lt_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.


Lemma close_typ_notin : forall X A,
    X `notin` ftvar_in_typ (close_typ_wrt_typ X A).
Proof.
  intros. apply close_typ_notin_rec.
Qed.


Lemma close_exp_notin_rec : forall x e n,
    x `notin` fvar_in_exp (close_exp_wrt_exp_rec n x e)
with close_body_notin_rec : forall x b n,
    x `notin` fvar_in_body (close_body_wrt_exp_rec n x b).
Proof.
  - intros until e. induction e; simpl; intros; auto.
    + destruct (lt_dec n n0); auto.
    + unfold eq_dec. destruct EqDec_eq_of_X; auto.
  - intros until b. induction b; simpl; intros; auto.
Qed.

Lemma close_exp_notin : forall x e,
    x `notin` fvar_in_exp (close_exp_wrt_exp x e)
with close_body_notin : forall x b,
    x `notin` fvar_in_body (close_body_wrt_exp x b).
Proof.
  - intros until e. unfold close_exp_wrt_exp.
    apply close_exp_notin_rec.
  - intros until b. unfold close_body_wrt_exp.
    apply close_body_notin_rec.
Qed.


Lemma close_exp_tvar_notin_rec : forall X e n,
    X `notin` ftvar_in_exp (close_exp_wrt_typ_rec n X e)
with close_body_tvar_notin_rec : forall X b n,
    X `notin` ftvar_in_body (close_body_wrt_typ_rec n X b).
Proof.
  - intros until e. induction e; simpl; intros; auto.
    + apply notin_union; auto.
      apply close_typ_notin_rec.
    + apply notin_union; auto.
      apply close_typ_notin_rec.
  - intros until b. induction b; simpl; intros; auto.
    + apply notin_union; auto.
      apply close_typ_notin_rec.
Qed.

Lemma close_exp_tvar_notin : forall X e,
    X `notin` ftvar_in_exp (close_exp_wrt_typ X e)
with close_body_tvar_notin : forall X b,
    X `notin` ftvar_in_body (close_body_wrt_typ X b).
Proof.
  - intros until e. unfold close_exp_wrt_typ.
    apply close_exp_tvar_notin_rec.
  - intros until b. unfold close_body_wrt_typ.
    apply close_body_tvar_notin_rec.
Qed.


Hint Constructors s_in: core.


Lemma sin_in : forall X T,
  s_in X T ->
  X `in` ftvar_in_typ T.
Proof.
  intros. induction H; simpl; auto.
  - inst_cofinites_by (L `union` singleton X).
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H0.
    apply AtomSetImpl.union_1 in H0; inversion H0; auto.
    + simpl in H1. apply AtomSetImpl.singleton_1 in H1.
      apply notin_union_2 in Fr. subst.
      apply notin_singleton_1 in Fr. contradiction.
Qed.

Lemma lc_typ_subst_inv : forall A X T,
  lc_typ ({T /ᵗ X} A) ->
  lc_typ T ->
  lc_typ A.
Proof.
  intros.
  dependent induction H; auto.
  - destruct A; try solve [inversion x]; auto.
  - destruct A; try solve [inversion x]; auto.
  - destruct A; try solve [inversion x]; auto.
  - destruct A; try solve [inversion x]; auto.
  - destruct A; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct A; try solve [inversion x]; auto.
    inversion x.
    inst_cofinites_by (singleton X).
    eapply lc_typ_all_exists with (X1:=x0). intros.
    specialize (H0 x0 (A ^ᵈ x0) X T). apply H0.
    subst. rewrite <- typ_subst_open_comm; auto.
    auto.
  - destruct A; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct A; try solve [inversion x]; auto.
    inversion x; eauto.
Qed.


Lemma d_mono_typ_d_wf_typ : forall Ψ A,
  d_mono_typ Ψ A -> Ψ ⊢ A.
Proof.
  intros. induction H; auto.
Qed.

Lemma lc_typ_subst : forall A T X,
  lc_typ A ->
  lc_typ T ->
  lc_typ ({ T /ᵗ X } A).
Proof.
  intros. induction H; simpl; auto.
  - destruct (X0 == X); auto.
  - inst_cofinites_by (singleton X) using_name X. eapply lc_typ_all_exists with (X1:=X0).
    replace (({T /ᵗ X} A) ^ᵈ X0) with ({T /ᵗ X} A ^ᵈ X0); eauto.
    rewrite typ_subst_open_comm; auto.
Qed.


Lemma ftv_sin_typ_subst : forall X Y A T,
  lc_typ T ->
  X `notin` ftvar_in_typ T ->
  X <> Y ->
  s_in X ({T /ᵗ Y} A) ->
  s_in X A.
Proof.
  intros. dependent induction H2; simpl; auto.
  - destruct A; simpl; try solve [inversion x].
    inversion x. destruct (X0 == Y).
    + subst. simpl in *.
      apply notin_singleton_1 in H0. contradiction.
    + inversion H3. auto.
  - destruct A; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0.
      eapply IHs_in with (T:=A1) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply s_in__arrow1; inversion x; eauto.
      subst.
      eapply lc_typ_subst_inv; eauto.
  - destruct A; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0. eapply IHs_in with (T:=A2) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply s_in__arrow2; inversion x; eauto.
      subst. eapply lc_typ_subst_inv; eauto.
  - destruct A; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (s_in X (typ_all A0)).
      * eapply s_in__all with (L:=L). intros. inst_cofinites_with Y0.
        auto.
      * apply sin_in in H4. contradiction.
    + inversion x.
    + apply s_in__all with (L:=L `union` singleton Y); intros; inst_cofinites_with Y0. auto.
     inversion x. rewrite H6 in H3.
    eapply H2; eauto. subst. rewrite typ_subst_open_comm; auto.
  - destruct A; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (s_in X (typ_union A1 A2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply s_in__union.
      * eapply IHs_in1 with (T:=T) (Y:=Y); eauto.
      * eapply IHs_in2 with (T:=T) (Y:=Y); eauto.
  - destruct A; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + assert (s_in X (typ_intersection A1 A2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply s_in__intersection.
      * eapply IHs_in1 with (T:=T) (Y:=Y); eauto.
      * eapply IHs_in2 with (T:=T) (Y:=Y); eauto.
Qed.


Lemma ftv_sin_typ_subst_inv : forall X Y T1 S1,
  lc_typ S1 ->
  X <> Y ->
  s_in X T1 ->
  s_in X ({S1 /ᵗ Y} T1).
Proof.
  intros.
  induction H1; try solve [simpl; eauto].
  - simpl. destruct (X == Y).
    + subst. contradiction.
    + auto.
  - simpl. apply s_in__arrow1; auto.
    apply subst_tvar_in_typ_lc_typ; auto.
  - simpl. apply s_in__arrow2; auto.
    apply subst_tvar_in_typ_lc_typ; auto.
  - simpl. eapply s_in__all with (L:=L `union` singleton Y).
    intros. inst_cofinites_with Y0.
    rewrite typ_subst_open_comm; auto.
Qed.
