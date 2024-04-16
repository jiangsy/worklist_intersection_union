Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import uni.notations.
Require Import ltac_utils.


#[export] Hint Constructors d_wf_typ: core.
#[export] Hint Constructors d_wf_env: core.
#[export] Hint Constructors s_in: core.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Lemma subst_tvar_in_typ_refl_eq : forall A X,
  A = {` X ᵗ/ₜ X} A.
Proof.
  intros.
  induction A; auto; simpl.
  - destruct (X0==X); subst; auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. rewrite <- IHA. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
Qed.

Lemma subst_tvar_in_typ_open_typ_wrt_typ_fresh2 : forall X A T B,
  lc_typ T ->
  X `notin` ftvar_in_typ B ->
  ({T ᵗ/ₜ X} A) ᵗ^^ₜ B = {T ᵗ/ₜ X} A ᵗ^^ₜ B.
Proof.
  intros.
  rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq B); auto.
Qed.


Lemma subst_tvar_in_exp_open_exp_wrt_typ_fresh2: forall X e1 e2 A,
  lc_typ A ->
  X `notin` ftvar_in_exp e2 ->
  (subst_tvar_in_exp A X e1) ᵉ^ₑ e2 = subst_tvar_in_exp A X (e1 ᵉ^ₑ e2).
Proof.
  intros. 
  rewrite subst_tvar_in_exp_open_exp_wrt_exp; auto.
  rewrite (subst_tvar_in_exp_fresh_eq e2); auto.
Qed.

Lemma subst_tvar_in_body_open_body_wrt_typ_fresh2 : forall X b A B,
  lc_typ B ->
  X `notin` ftvar_in_typ A ->
  open_body_wrt_typ (subst_tvar_in_body B X b) A = subst_tvar_in_body B X (open_body_wrt_typ b A).
Proof.
  intros.
  rewrite subst_tvar_in_body_open_body_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq A); auto.
Qed.


Lemma ls_binds_split {A : Type} : forall (ls : list (atom * A)) X b,
  binds X b ls ->
  exists ls1 ls2, ls = ls1 ++ (X, b) :: ls2.
Proof.
  intros. induction ls.
  - inversion H.
  - inversion H. subst.
    + exists (@nil (atom * A)). exists ls. auto.
    + apply IHls in H0. destruct H0 as [ls1 [ls2]].
      exists (a :: ls1). exists ls2. simpl. subst. auto.
Qed.

Lemma eq_ls_eq_length : forall {A : Type} (ls1 ls2 : list A),
  ls1 = ls2 -> length ls1 = length ls2.
Proof.
  intros. generalize dependent ls2. induction ls1; intros.
  - inversion H; auto.
  - destruct ls2. inversion H.
    + inversion H; simpl; apply f_equal; eauto.
Qed.

Lemma ls_cons_eq_false : forall {A : Type} (a : A) ls1 ls2,
  a :: ls2 ++ ls1 = ls1 -> False.
Proof.
  intros.
  apply eq_ls_eq_length in H.
  simpl in H.
  rewrite app_length in H. lia.
Qed.

Lemma ls_app_eq_inv {A : Type} : forall (ls1 ls2 ls2' : list A),
  ls2 ++ ls1 = ls2' ++ ls1 ->
  ls2 = ls2'.
Proof.
  intros. generalize dependent ls2'. induction ls2; intros.
  - destruct ls2'; auto.
    simpl in H. inversion H.
    exfalso. eapply ls_cons_eq_false; eauto.
  - destruct ls2'; auto.
    + exfalso. eapply ls_cons_eq_false; eauto.
    + dependent destruction H.
      apply IHls2 in x; subst; auto.
Qed.


Lemma ls_split_det {A : Type} : forall (ls1 ls2 ls'1 ls'2 : list (atom * A)) X b,
  X `notin` dom (ls'1 ++ ls'2) ->
  ls2 ++ (X, b) :: ls1 = ls'2 ++ (X, b) :: ls'1 ->
  ls1 = ls'1 /\ ls2 = ls'2.
Proof.
  intros. generalize dependent ls1. generalize dependent ls'1. generalize dependent ls'2.
  induction ls2; intros.
  - destruct ls'2; simpl in H0.
    + dependent destruction H0; intuition.
    + dependent destruction H0. rewrite dom_app in H. simpl in *. solve_notin_eq X.
  - destruct ls'2; simpl in H0.
    + dependent destruction H0.  rewrite dom_app in H. simpl in *. solve_notin_eq X.
    + dependent destruction H0. eapply IHls2 in x; eauto.
      * dependent destruction x. subst. intuition.
      * destruct p. rewrite dom_app in H. simpl in *.
        rewrite dom_app... destruct_notin; eauto.
Qed.


Lemma binds_remove_mid_diff_bind {A} : forall θ1 θ2 X Y (b1 b2 : A),
  binds X b1 (θ2 ++ (Y, b2) :: θ1) ->
  b1 <> b2 ->
  binds X b1 (θ2 ++ θ1).
Proof.  
  intros. induction θ2; simpl in *; eauto.
  - inversion H. dependent destruction H1.
    + contradiction.
    + auto. 
  - destruct a. inversion H.
    + dependent destruction H1. auto.
    + auto.
Qed.

Lemma binds_weaken_mid {A} : forall θ1 θ2 X Y (b1 b2 : A),
  binds X b1 (θ2 ++ θ1) ->
  binds X b1 (θ2 ++ (Y, b2) :: θ1).
Proof.  
  intros. rewrite_env (θ2 ++ (Y ~ b2) ++ θ1).
  apply binds_weaken. auto.
Qed.

Lemma subst_tvar_in_typ_open_typ_wrt_typ_tvar2 : forall X A T,
  lc_typ T ->
  X `notin` ftvar_in_typ A ->
  {T ᵗ/ₜ X} A ᵗ^ₜ X = A ᵗ^^ₜ T.
Proof.
  intros.
  rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq A); auto.
  simpl. unfold eq_dec.
  - destruct (EqDec_eq_of_X X X); auto.
    contradiction.
Qed.


Lemma open_body_wrt_typ_anno : forall A B e,
  open_body_wrt_typ (body_anno e A) B = body_anno (open_exp_wrt_typ e B) (open_typ_wrt_typ A B).
Proof.
  intros. unfold open_body_wrt_typ. simpl. auto.
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


Lemma close_typ_wrt_typ_notin_rec : forall X A n,
    X `notin` ftvar_in_typ (close_typ_wrt_typ_rec n X A).
Proof.
  intros until A.
  induction A; simpl; intros; auto.
  - destruct (lt_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.


Lemma close_typ_wrt_typ_notin : forall X A,
    X `notin` ftvar_in_typ (close_typ_wrt_typ X A).
Proof.
  intros. apply close_typ_wrt_typ_notin_rec.
Qed.


Lemma close_exp_wrt_exp_notin_rec : forall x e n,
    x `notin` fvar_in_exp (close_exp_wrt_exp_rec n x e)
with close_body_wrt_exp_notin_rec : forall x b n,
    x `notin` fvar_in_body (close_body_wrt_exp_rec n x b).
Proof.
  - intros until e. induction e; simpl; intros; auto.
    + destruct (lt_dec n n0); auto.
    + unfold eq_dec. destruct EqDec_eq_of_X; auto.
  - intros until b. induction b; simpl; intros; auto.
Qed.

Lemma close_exp_wrt_exp_notin : forall x e,
    x `notin` fvar_in_exp (close_exp_wrt_exp x e)
with close_body_wrt_exp_notin : forall x b,
    x `notin` fvar_in_body (close_body_wrt_exp x b).
Proof.
  - intros until e. unfold close_exp_wrt_exp.
    apply close_exp_wrt_exp_notin_rec.
  - intros until b. unfold close_body_wrt_exp.
    apply close_body_wrt_exp_notin_rec.
Qed.


Lemma close_exp_wrt_typ_notin_rec : forall X e n,
    X `notin` ftvar_in_exp (close_exp_wrt_typ_rec n X e)
with close_body_wrt_typ_notin_rec : forall X b n,
    X `notin` ftvar_in_body (close_body_wrt_typ_rec n X b).
Proof.
  - intros until e. induction e; simpl; intros; auto.
    + apply notin_union; auto.
      apply close_typ_wrt_typ_notin_rec.
    + apply notin_union; auto.
      apply close_typ_wrt_typ_notin_rec.
  - intros until b. induction b; simpl; intros; auto.
    + apply notin_union; auto.
      apply close_typ_wrt_typ_notin_rec.
Qed.

Lemma close_exp_wrt_typ_notin : forall X e,
    X `notin` ftvar_in_exp (close_exp_wrt_typ X e)
with close_body_wrt_typ_notin : forall X b,
    X `notin` ftvar_in_body (close_body_wrt_typ X b).
Proof.
  - intros until e. unfold close_exp_wrt_typ.
    apply close_exp_wrt_typ_notin_rec.
  - intros until b. unfold close_body_wrt_typ.
    apply close_body_wrt_typ_notin_rec.
Qed.


Lemma sin_in : forall X T,
  s_in X T ->
  X `in` ftvar_in_typ T.
Proof.
  intros. induction H; simpl; auto.
  - inst_cofinites_by (L `union` singleton X).
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H0.
    apply AtomSetImpl.union_1 in H0; inversion H0; auto.
    + simpl in H1. apply AtomSetImpl.singleton_1 in H1. subst. solve_notin_eq X.
Qed.

Lemma lc_typ_subst_inv : forall A X T,
  lc_typ ({T ᵗ/ₜ X} A) ->
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
    specialize (H0 x0 (A ᵗ^ₜ x0) X T). apply H0.
    subst. rewrite <- subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
    auto.
  - destruct A; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct A; try solve [inversion x]; auto.
    inversion x; eauto.
Qed.


Lemma lc_typ_subst : forall A T X,
  lc_typ A ->
  lc_typ T ->
  lc_typ ({ T ᵗ/ₜ X } A).
Proof.
  intros. induction H; simpl; auto.
  - destruct (X0 == X); auto.
  - inst_cofinites_by (singleton X) using_name X. eapply lc_typ_all_exists with (X1:=X0).
    replace (({T ᵗ/ₜ X} A) ᵗ^ₜ X0) with ({T ᵗ/ₜ X} A ᵗ^ₜ X0); eauto.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
Qed.


Lemma lc_exp_subst_tvar_in_exp : forall e A X,
  lc_exp e ->
  lc_typ A ->
  lc_exp (subst_tvar_in_exp A X e)
with lc_body_subst_tvar_in_body : forall b A X,
  lc_body b ->
  lc_typ A ->
  lc_body (subst_tvar_in_body A X b).
Proof with eauto using lc_typ_subst.
  - intros. clear lc_exp_subst_tvar_in_exp. induction H; simpl...
    + pick fresh x0. apply lc_exp_abs_exists with (x1:=x0). 
      rewrite subst_tvar_in_exp_open_exp_wrt_typ_fresh2...
    + pick fresh X0. apply lc_exp_tabs_exists with (X1:=X0).
      rewrite subst_tvar_in_body_open_body_wrt_typ_fresh2...
  - intros. clear lc_body_subst_tvar_in_body. destruct b. 
      dependent destruction H; simpl...
Qed.


Lemma lc_exp_subst_tvar_in_exp_inv : forall e A X,
  lc_exp (subst_tvar_in_exp A X e) ->
  lc_typ A ->
  lc_exp e
with lc_body_subst_tvar_in_body_inv : forall b A X,
  lc_body (subst_tvar_in_body A X b) ->
  lc_typ A ->
  lc_body b.  
Proof.
  - intros. dependent induction H; auto; try solve [destruct e; try solve [inversion x]; auto].
    + destruct e; try solve [inversion x]; auto.
      inversion x. subst.
      inst_cofinites_by (singleton X) using_name x.
      apply lc_exp_abs_exists with (x1:=x0).
      eapply H0 with (x:=x0) (X:=X); eauto.
      rewrite subst_tvar_in_exp_open_exp_wrt_exp; simpl; auto.
    + destruct e; try solve [inversion x]; auto.
      inversion x. subst.
      constructor; eauto.
    + destruct e; try solve [inversion x]; auto.
      inversion x. subst.
      inst_cofinites_by (singleton X) using_name X.
      apply lc_exp_tabs_exists with (X1:=X0).
      eapply lc_body_subst_tvar_in_body_inv with (X:=X); eauto.
      rewrite subst_tvar_in_body_open_body_wrt_typ; simpl; auto.
      destruct_eq_atom. auto.
    + destruct e; try solve [inversion x]; auto.
      inversion x. subst.
      constructor; eauto. 
      eapply lc_typ_subst_inv; eauto.
    + destruct e; try solve [inversion x]; auto.
      inversion x. subst.
      constructor; eauto.
      eapply lc_typ_subst_inv; eauto.
  - intros. destruct b. dependent destruction H.
    + constructor; eauto.
      eapply lc_typ_subst_inv; eauto.
Qed.

Lemma d_mono_typ_d_wf_typ : forall Ψ A,
  d_mono_typ Ψ A -> Ψ ⊢ A.
Proof.
  intros. induction H; auto.
Qed.


Lemma s_in_subst : forall X Y A T,
  lc_typ T ->
  X `notin` ftvar_in_typ T ->
  X <> Y ->
  s_in X ({T ᵗ/ₜ Y} A) ->
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
    eapply H2; eauto. subst. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
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


Lemma s_in_subst_inv : forall X Y T1 S1,
  lc_typ S1 ->
  X <> Y ->
  s_in X T1 ->
  s_in X ({S1 ᵗ/ₜ Y} T1).
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
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto.
Qed.

Lemma s_in_b_subst_inv : forall X Y b A,
  lc_typ A ->
  X <> Y ->
  s_in_b X b ->
  s_in_b X (subst_tvar_in_body A Y b).
Proof.
  intros. destruct b. dependent destruction H1.
  simpl. constructor.
  - apply lc_exp_subst_tvar_in_exp; auto. 
  - apply s_in_subst_inv; auto.
Qed.


Lemma s_in_lc_typ : forall A X,
  s_in X A ->
  lc_typ A.
Proof.
  intros; induction H; auto.
Qed.


Lemma s_in_rename : forall A X Y,
  s_in X A ->
  s_in Y ({typ_var_f Y ᵗ/ₜ X} A).
Proof.
  intros. induction H; simpl; eauto.
  - destruct_eq_atom; auto.
  - apply s_in__arrow1; auto. apply lc_typ_subst; auto.
  - apply s_in__arrow2; auto. apply lc_typ_subst; auto.
  - apply s_in__all with (L:=L `union` singleton X). intros. inst_cofinites_with Y0. 
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto...
Qed.

Lemma neq_all_rename: forall A X Y,
  neq_all A ->
  neq_all ({typ_var_f Y ᵗ/ₜ X} A).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A...
  - case_if; subst*.
  - eapply neq_all__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor; applys lc_typ_subst; try inverts~ H...
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.


Lemma neq_intersection_rename: forall A X Y,
  neq_intersection A ->
  neq_intersection ({typ_var_f Y ᵗ/ₜ X} A).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A...
  - case_if; subst*.
  - eapply neq_intersection__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor.
    dependent destruction H...
    forwards*: lc_typ_subst (typ_all A) (typ_var_f Y) X.
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.


Lemma neq_union_rename: forall A X Y,
  neq_union A ->
  neq_union ({typ_var_f Y ᵗ/ₜ X} A).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A...
  - case_if; subst*.
  - eapply neq_union__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor.
    dependent destruction H...
    forwards*: lc_typ_subst (typ_all A) (typ_var_f Y) X.
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.

Lemma neq_all_lc_typ : forall A,
  neq_all A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma neq_intersection_lc_typ : forall A,
  neq_intersection A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma neq_union_lc_typ : forall A,
  neq_union A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.


#[export] Hint Resolve neq_all_rename neq_intersection_rename neq_union_rename : core.
#[export] Hint Immediate neq_all_lc_typ neq_intersection_lc_typ neq_union_lc_typ : core.
