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

Lemma typ_subst_open_comm : forall X T1 T2 T3,
  lc_typ T2 ->
  X `notin` ftv_in_typ T3 ->
  ({T2 /ᵈ X} T1) ^^ᵈ T3 = {T2 /ᵈ X} T1 ^^ᵈ T3.
Proof.
  intros.
  rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq T3); auto.
Qed.


Lemma typ_subst_open_var : forall X T1 T2,
  lc_typ T2 ->
  X `notin` ftv_in_typ T1 ->
  {T2 /ᵈ X} T1 ^ᵈ X = T1 ^^ᵈ T2.
Proof.
  intros.
  rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
  rewrite (subst_tvar_in_typ_fresh_eq T1); auto.
  simpl. unfold eq_dec.
  - destruct (EqDec_eq_of_X X X); auto.
    contradiction.
Qed.

Lemma open_typ_wrt_typ_twice : forall n X SY S,
    lc_typ SY ->
    open_typ_wrt_typ_rec n `ᵈ X (open_typ_wrt_typ_rec (n+1) SY S)
    = open_typ_wrt_typ_rec n SY (open_typ_wrt_typ_rec n `ᵈ X S).
Proof with subst; simpl in *; eauto; try lia.
  introv HL. gen n. induction S; intros...
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
  - forwards: IHS (Datatypes.S n).
    replace (Datatypes.S (n + 1)) with (Datatypes.S n +1).
    rewrite H. congruence. lia.
Qed.



Lemma typ_open_r_close_l : forall T1 T2 X
  , X `notin` ftv_in_typ T2
  -> T1 = open_typ_wrt_typ T2 `ᵈ X -> close_typ_wrt_typ X T1 = T2.
Proof.
  intros * Fr H.
  assert (close_typ_wrt_typ X T1 = close_typ_wrt_typ X (open_typ_wrt_typ T2 `ᵈ X)) by now rewrite H.
  now rewrite close_typ_wrt_typ_open_typ_wrt_typ in H0.
Qed.


Lemma close_typ_notin_rec : forall X e n,
    X `notin` ftv_in_typ (close_typ_wrt_typ_rec n X e).
Proof.
  intros until e.
  induction e; simpl; intros; auto.
  - destruct (lt_dec n n0); auto.
  - unfold eq_dec. destruct EqDec_eq_of_X; auto.
Qed.


Lemma close_typ_notin : forall X T,
    X `notin` ftv_in_typ (close_typ_wrt_typ X T).
Proof.
  intros. apply close_typ_notin_rec.
Qed.

Hint Constructors ds_in: core.


Lemma sin_in : forall X T,
  ds_in X T ->
  X `in` ftv_in_typ T.
Proof.
  intros. induction H; simpl; auto.
  - inst_cofinites_by (L `union` singleton X).
    rewrite ftv_in_typ_open_typ_wrt_typ_upper in H0.
    apply AtomSetImpl.union_1 in H0; inversion H0; auto.
    + simpl in H1. apply AtomSetImpl.singleton_1 in H1.
      apply notin_union_2 in Fr. subst.
      apply notin_singleton_1 in Fr. contradiction.
Qed.

Lemma lc_typ_subst_inv : forall A1 X T,
  lc_typ ({T /ᵈ X} A1) ->
  lc_typ T ->
  lc_typ A1.
Proof.
  intros.
  dependent induction H; auto.
  - destruct A1; try solve [inversion x]; auto.
  - destruct A1; try solve [inversion x]; auto.
  - destruct A1; try solve [inversion x]; auto.
  - destruct A1; try solve [inversion x]; auto.
  - destruct A1; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct A1; try solve [inversion x]; auto.
    inversion x.
    inst_cofinites_by (singleton X).
    eapply lc_typ_all_exists with (X1:=x0). intros.
    specialize (H0 x0 (A1 ^ᵈ x0) X T). apply H0.
    subst. rewrite <- typ_subst_open_comm; auto.
    auto.
  - destruct A1; try solve [inversion x]; auto.
    inversion x; eauto.
  - destruct A1; try solve [inversion x]; auto.
    inversion x; eauto.
Qed.


Lemma d_mono_typ_d_wf_typ : forall E A1,
  d_mono_typ E A1 -> E ⊢ A1.
Proof.
  intros. induction H; auto.
Qed.

Lemma lc_typ_subst : forall A1 T X,
  lc_typ A1 ->
  lc_typ T ->
  lc_typ ({ T /ᵈ X } A1).
Proof.
  intros. induction H; simpl; auto.
  - destruct (X0 == X); auto.
  - inst_cofinites_by (singleton X) using_name X. eapply lc_typ_all_exists with (X1:=X0). 
    replace (({T /ᵈ X} A) ^ᵈ X0) with ({T /ᵈ X} A ^ᵈ X0); eauto.
    rewrite typ_subst_open_comm; auto.
Qed.


Lemma ftv_sin_typ_subst : forall X Y T1 S1,
  lc_typ S1 ->
  X `notin` ftv_in_typ S1 ->
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
      eapply IHds_in with (S1:=A1) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply dsin_arrow1; inversion x; eauto.
      subst.
      eapply lc_typ_subst_inv; eauto.
  - destruct T1; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0. eapply IHds_in with (S1:=A2) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply dsin_arrow2; inversion x; eauto.
      subst. eapply lc_typ_subst_inv; eauto.
  - destruct T1; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (typ_all A)).
      * eapply dsin_all with (L:=L). intros. inst_cofinites_with Y0.
        auto.
      * apply sin_in in H4. contradiction.
    + inversion x.
    + apply dsin_all with (L:=L `union` singleton Y); intros; inst_cofinites_with Y0. auto.
     inversion x. rewrite H6 in H3.
    eapply H2; eauto. subst. rewrite typ_subst_open_comm; auto.
  - destruct T1; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (typ_union A1 A2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_union.
      * eapply IHds_in1 with (S1:=S1) (Y:=Y); eauto.
      * eapply IHds_in2 with (S1:=S1) (Y:=Y); eauto.
  - destruct T1; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (typ_intersection A1 A2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_intersection.
      * eapply IHds_in1 with (S1:=S1) (Y:=Y); eauto.
      * eapply IHds_in2 with (S1:=S1) (Y:=Y); eauto.
Qed.


Lemma ftv_sin_typ_subst_inv : forall X Y T1 S1,
  lc_typ S1 ->
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
    apply subst_tvar_in_typ_lc_typ; auto.
  - simpl. apply dsin_arrow2; auto.
    apply subst_tvar_in_typ_lc_typ; auto.
  - simpl. eapply dsin_all with (L:=L `union` singleton Y).
    intros. inst_cofinites_with Y0.
    rewrite typ_subst_open_comm; auto.
Qed.


Lemma d_mono_typ_lc : forall E T,
  d_mono_typ E T -> lc_typ T.
Proof.
  intros; induction H; auto.
Qed.


Lemma d_wf_typ_subst_tvar_stvar : forall E F X T,
  E ++ [(X, dbind_tvar_empty)] ++ F  ⊢ₛ T  ->
  E ++ [(X, dbind_stvar_empty)] ++ F ⊢ₛ T.
Proof.
  intros E F X T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
    + subst. eapply dwftyps_stvar. auto.
    + econstructor.
      induction E.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. eapply dwftyps_stvar. auto.
    induction E.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. constructor.
    + apply IHd_wf_typ_s1; auto.
    + apply IHd_wf_typ_s2; auto.
  - simpl. eapply dwftyps_all with (L:=L);
    intros X1 Hf; inst_cofinites_with X1.
    + auto. 
    + rewrite_env ((X1 ~ ▪ ++ E) ++ (X, ▪) :: F ).
      apply H1; eauto.
  - simpl. constructor.
    + apply IHd_wf_typ_s1; auto.
    + apply IHd_wf_typ_s2; auto.
  - simpl. constructor.
    + apply IHd_wf_typ_s1; auto.
    + apply IHd_wf_typ_s2; auto.
Qed.


Lemma d_wf_typ_subst_stvar_tvar : forall E F X T,
  E ++ [(X, dbind_stvar_empty)] ++ F ⊢ T  ->
  E ++ [(X, dbind_tvar_empty)] ++ F ⊢ T.
Proof.
  intros E F X T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. constructor.
    induction E.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
    + econstructor; auto.
    + apply d_wf_typ__stvar.
      induction E.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. constructor.
    + apply IHd_wf_typ1; auto.
    + apply IHd_wf_typ2; auto.
  - simpl. eapply d_wf_typ__all with (L:=L);
    intros; inst_cofinites_with X.
    + auto.
    + rewrite_env ((X0 ~ ▫ ++ E) ++ (X, ▫) :: F).
      apply H1; eauto.
  - simpl. constructor.
    + apply IHd_wf_typ1; auto.
    + apply IHd_wf_typ2; auto.
  - simpl. constructor.
    + apply IHd_wf_typ1; auto.
    + apply IHd_wf_typ2; auto.
Qed.

Corollary d_wf_typ_subst_stvar_tvar_cons : forall E X T,
  X `notin` ftv_in_typ T ->
  X ~ dbind_tvar_empty ++ E ⊢ₛ T ^ᵈ X ->
  X ~ dbind_stvar_empty ++ E ⊢ₛ T ^ᵈ X.
Proof.
  intros.
  rewrite_env (nil ++ X ~ dbind_stvar_empty ++ E).
  apply d_wf_typ_subst_tvar_stvar.
  auto.
Qed.

Corollary d_wf_typ_subst_tvar_stvar_cons : forall E X T,
  X `notin` ftv_in_typ T ->
  X ~ dbind_stvar_empty ++ E ⊢ T ^ᵈ X ->
  X ~ dbind_tvar_empty ++ E ⊢ T ^ᵈ X.
Proof.
  intros.
  rewrite_env (nil ++ X ~ dbind_tvar_empty ++ E).
  apply d_wf_typ_subst_stvar_tvar; eauto.
Qed.

Lemma dwf_typ_dwf_typ_s : forall E A,
  E ⊢ A -> E ⊢ₛ A.
Proof.
  intros.
  induction H; auto.
  - eapply dwftyps_all with (L:= (L `union` ftv_in_typ A));
    intros; inst_cofinites_with SX.
    + auto.
    + apply d_wf_typ_subst_stvar_tvar_cons; auto.
Qed.

Lemma dwf_typ_s_dwf_typ : forall E A,
  E ⊢ₛ A -> E ⊢ A.
Proof.
  intros. induction H; auto.
  - eapply d_wf_typ__all with (L:= (L `union` ftv_in_typ T1));
    intros; inst_cofinites_with X.
    + auto.
    + eapply d_wf_typ_subst_tvar_stvar_cons; auto.
Qed.

Hint Constructors d_sub : core.
Hint Immediate dwf_typ_dwf_typ_s : core.
Hint Immediate dwf_typ_s_dwf_typ : core.

Lemma dwf_typ_dlc_type : forall E A,
  E ⊢ A -> lc_typ A.
Proof.
  intros; induction H; auto.
Qed.

Lemma dwf_typ_s_dlc_type : forall E A,
  E ⊢ₛ A -> lc_typ A.
Proof.
  intros.
  eapply dwf_typ_dlc_type.
  apply dwf_typ_s_dwf_typ.
  eauto.
Qed.

Hint Resolve dwf_typ_s_dlc_type : core.

Hint Constructors neq_union : Core.
Hint Constructors neq_intersection : Core.


Lemma dwf_typ_open_inv : forall E A1 T1 X,
  lc_typ T1 ->
  E ⊢ {T1 /ᵈ X} A1 ->
  binds X dbind_tvar_empty E ->
  E ⊢ A1.
Proof.
  intros. dependent induction H0; auto.
  - destruct A1; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct A1; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct A1; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct A1; simpl in *; try solve [inversion x].
    + destruct (X1 == X) in x; subst.
      auto.
      inversion x. subst. auto.
  - destruct A1; simpl in *; try solve [inversion x].
    + destruct (X1 == X) in x; subst.
      auto. inversion x. subst. auto.
  - destruct A1; simpl in *; try solve [inversion x].
      destruct (X0 == X) in x.
      subst. auto. inversion x.
    + inversion x. eauto.
  - destruct A1; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    + subst. auto.
    + inversion x.
    + inversion x.
      eapply d_wf_typ__all with (L:=L `union` singleton X `union` ftv_in_typ T1); intros;
      inst_cofinites_with X0.
      * rewrite H5 in H2.
        rewrite typ_subst_open_comm in H2; auto.
        eapply ftv_sin_typ_subst; eauto.
      * eapply H1 with (X:=X) (T1:=T1); auto.
        -- rewrite H5. rewrite typ_subst_open_comm; auto.
  - destruct A1; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
  - destruct A1; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
Qed.


Hint Constructors d_wf_typ: core.
Hint Constructors d_wf_env: core.
Hint Constructors d_wf_typ_s: core.


Lemma dwf_typ_weakening : forall E1 E2 E3 T,
  E3 ++ E1 ⊢ T ->
  (* uniq (E3 ++ E2 ++ E1) -> *)
  E3 ++ E2 ++ E1 ⊢ T.
Proof.
  intros.
  dependent induction H; auto.
  - eapply d_wf_typ__all with (L:=L `union` dom (E3 ++ E2 ++ E1));
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
    + simpl in *. apply IHd_wf_env in H3.
      apply dwf_typ_weakening_cons; auto.
Qed.

(* Lemma dwft_subst : forall E X T1 T2,
  X ~ dbind_tvar_empty ++ E ⊢ T1 ^ᵈ X ->
  E ⊢ T2 ->
  E ⊢ T1 ^^ᵈ T2.
Admitted. *)

Hint Constructors d_typing : core.

(* Lemma d_wft_typ_swap_env : forall F X Y E T ,
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
Qed. *)


Lemma d_wft_typ_subst : forall E X F A1 T2,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  F ++ X ~ dbind_tvar_empty ++ E ⊢ A1 ->
  E ⊢ T2 ->
  map (subst_tvar_in_dbind T2 X) F  ++ E ⊢ {T2 /ᵈ X} A1.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; forwards: d_wf_env_uniq Hwfenv; try solve [simpl; auto]...
  - destruct (X0 == X).
    + subst. simpl. applys* dwf_typ_weaken_head.
      (* solve_uniq. *)
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (subst_tvar_in_dbind T2 X) H1...
      * apply binds_cons_iff in H1. iauto.
  - destruct (X0 == X).
    + apply dwf_typ_weaken_head. auto.
    + eapply d_wf_typ__stvar. 
      forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (subst_tvar_in_dbind T2 X) H1.
      forwards* [(?&?&?)|?]: binds_cons_uniq_1 H1... 
  - simpl. inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_var...
      applys* ftv_sin_typ_subst_inv.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_var...
      replace ((X0, dbind_tvar_empty) :: map (subst_tvar_in_dbind T2 X) F ++ E)
      with (map (subst_tvar_in_dbind T2 X) ((X0, dbind_tvar_empty) :: F) ++ E) by auto.
      apply H1; auto...
      econstructor...
Qed.

Lemma d_wft_all_open : forall E A1 T1,
  ⊢ E ->
  E ⊢ typ_all A1 ->
  E ⊢ T1 ->
  E ⊢ A1 ^^ᵈ T1. 
Proof.
  intros.
  inversion H0.
  inst_cofinites_by (L `union` ftv_in_typ A1 `union` dom E) using_name X.
  rewrite_env (map (subst_tvar_in_dbind T1 X) nil ++ E).
  erewrite <- typ_subst_open_var; eauto.
  apply d_wft_typ_subst; eauto.
  econstructor; auto.
Qed.


Lemma d_wft_typ_subst_stvar : forall E X F A1 T2,
  ⊢ F ++ X ~ dbind_stvar_empty ++ E ->
  F ++ X ~ dbind_stvar_empty ++ E ⊢ A1 ->
  E ⊢ T2 ->
  map (subst_tvar_in_dbind T2 X) F ++ E ⊢ {T2 /ᵈ X} A1.
Proof with simpl in *; try solve_by_invert; eauto using uniq_app_1, uniq_app_2, binds_app_1, binds_app_2.
  intros * Hwfenv Hwft1 Hwft2.
  inductions Hwft1; intros; forwards: d_wf_env_uniq Hwfenv; try solve [simpl; auto]...
  - destruct (X0 == X); subst...
    + apply dwf_typ_weaken_head. auto.
    + eapply d_wf_typ__tvar. 
      forwards* [?|?]: binds_app_1 H. forwards*: binds_map_2 (subst_tvar_in_dbind T2 X) H1.
      forwards* [(?&?&?)|?]: binds_cons_uniq_1 H1... 
  - destruct (X0 == X); subst...
    + subst. simpl. applys* dwf_typ_weaken_head.
      (* solve_uniq. *)
    + forwards* [?|?]: binds_app_1 H.
      * forwards: binds_map_2 (subst_tvar_in_dbind T2 X) H1...
      * apply binds_cons_iff in H1. iauto.
  - simpl. inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_var...
      applys* ftv_sin_typ_subst_inv.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_var...
      replace ((X0, dbind_tvar_empty) :: map (subst_tvar_in_dbind T2 X) F ++ E)
      with (map (subst_tvar_in_dbind T2 X) ((X0, dbind_tvar_empty) :: F) ++ E) by auto.
      apply H1; auto...
      econstructor...
Qed.


Lemma d_new_tv_notin_wf_typ : forall X E A1,
  ⊢ (X, dbind_tvar_empty) :: E ->
  E ⊢ A1 ->
  X `notin` ftv_in_typ A1.
Proof.
  intros; induction H0; auto.
  - simpl. destruct (X0 == X).
    + subst. dependent destruction H.
      simpl in *. exfalso.
      eapply binds_dom_contradiction; eauto.
    + apply notin_singleton; auto.
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
      rewrite ftv_in_typ_open_typ_wrt_typ_lower; auto.
Qed.

Lemma d_wf_typ_lc_typ : forall E T,
  E ⊢ T -> lc_typ T.
Proof.
  intros. induction H; eauto.
Qed.

#[export] Hint Resolve d_mono_typ_lc : core.

Lemma d_mono_typ_neq_all : forall E T,
  d_mono_typ E T -> neq_all T.
Proof.
  intros; induction H; eauto...
Qed.


Lemma d_neq_all_subst_neq_all : forall E A1 X T2,
  lc_typ A1 ->
  d_mono_typ E T2 ->
  neq_all A1 ->
  neq_all ( {T2 /ᵈ X} A1 ).
Proof.
  intros. induction H; simpl; eauto...
  - destruct (X0 == X); auto.
    eapply d_mono_typ_neq_all; eauto.
  - eapply neq_all__arrow;
    apply subst_tvar_in_typ_lc_typ; eauto...
  - inversion H1.
  - eapply neq_all__union;
    apply subst_tvar_in_typ_lc_typ; eauto...
  - eapply neq_all__intersection;
    apply subst_tvar_in_typ_lc_typ; eauto...
Qed.


Lemma bind_typ_subst : forall F X E x T1 T2,
  ⊢ F ++ (X, dbind_tvar_empty) :: E ->
  x ~ T1 ∈ (F ++ (X, dbind_tvar_empty) :: E) ->
  E ⊢ T2 ->
  x ~ ({T2 /ᵈ X} T1) ∈ (map (subst_tvar_in_dbind T2 X) F ++ E).
Proof.
  intros. induction F; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (E ⊢ T1).
      { eapply dwf_env_binds_dwf_typ; eauto. inversion H. auto. }
      rewrite subst_tvar_in_typ_fresh_eq; auto.
      eapply d_new_tv_notin_wf_typ; eauto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      apply IHF; auto.
      inversion H; auto.
Qed.


Lemma d_mono_typ_subst_mono_mono : forall E A1 T1 X,
  d_mono_typ E A1 ->
  d_mono_typ E T1 ->
  d_mono_typ E ({T1 /ᵈ X} A1).
Proof.
  intros. induction A1; try solve [simpl; eauto].
  - simpl. destruct (X0 == X); auto.
  - simpl. dependent destruction H. auto.
  - inversion H.
  - simpl. dependent destruction H. auto.
  - simpl. dependent destruction H. auto.
Qed.


Lemma d_sub_dwft : forall E A1 B1,
  E ⊢ A1 <: B1 -> ⊢ E /\ E ⊢ A1 /\ E ⊢ B1.
Proof with auto.
  intros.
  induction H; try solve [intuition].
  - split.
    inst_cofinites_by L. intuition... inversion H3. auto.
    split; eapply d_wf_typ__all with (L:=L `union` ftv_in_typ A1 `union` ftv_in_typ B1); intros; inst_cofinites_with X; auto...
    eapply d_wf_typ_subst_tvar_stvar_cons; intuition.
    eapply d_wf_typ_subst_tvar_stvar_cons; intuition.
  - split; try solve [intuition].
    split; try solve [intuition].
    + eapply d_wf_typ__all with (L:=L `union` ftv_in_typ A1 `union` dom E).
      * intros. inst_cofinites_with X. auto.
      * intros. inst_cofinites_with X.
        destruct IHd_sub. auto.
        eapply dwf_typ_open_inv with (X:=X) (T1:=T1); auto.
        -- eapply d_mono_typ_lc; eauto.
        -- replace (X ~ dbind_tvar_empty ++ E) with (nil ++ X ~ dbind_tvar_empty ++ E) by auto.
           apply dwf_typ_weakening. simpl. rewrite  subst_tvar_in_typ_open_typ_wrt_typ.
           ++ simpl. unfold eq_dec. destruct ( EqDec_eq_of_X X X ).
              ** rewrite subst_tvar_in_typ_fresh_eq; intuition.
              ** contradiction.
           ++ eapply d_mono_typ_lc; eauto.
           (* ++ auto. *)
Qed.

Lemma d_sub_dwft_0 : forall E A1 B1,
    E ⊢ A1 <: B1 -> ⊢ E.
Proof.
  intros. forwards*: d_sub_dwft H.
Qed.

Lemma d_sub_dwft_1 : forall E A1 B1,
    E ⊢ A1 <: B1 -> E ⊢ A1.
Proof.
  intros. forwards*: d_sub_dwft H.
Qed.

Lemma d_sub_dwft_2 : forall E A1 B1,
    E ⊢ A1 <: B1 -> E ⊢ B1.
Proof.
  intros. forwards*: d_sub_dwft H.
Qed.

Lemma dwf_typ_strengthening : forall F E X T b,
    ⊢ E ++ X ~ b ++ F ->
    E ++ X ~ b ++ F ⊢ T ->
    X \notin ftv_in_typ T ->
    E ++ F ⊢ T.
Proof with eauto.
  intros * Hwfenv H. intros.
  dependent induction H; auto.
  - induction E.
    + inversion H. dependent destruction H1.
      simpl in H0. apply notin_singleton_1 in H0. contradiction.
      auto.
    + destruct a. inversion H.
      * dependent destruction H1. auto.
      * simpl. apply dwf_typ_weakening_cons. apply IHE; auto.
        rewrite_env ((a, d) :: (E ++ X ~ b ++ F)) in Hwfenv. applys* d_wf_env_strenthening_head.
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - induction E.
    + inversion H. dependent destruction H1.
      * simpl in H0. apply notin_singleton_1 in H0. contradiction.
      * auto.
    + destruct a. inversion H.
      * dependent destruction H1. auto.
      * simpl. apply dwf_typ_weakening_cons; auto. apply IHE; auto.
        rewrite_env ((a, d) :: (E ++ X ~ b ++ F)) in Hwfenv. applys* d_wf_env_strenthening_head.
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - simpl in *. constructor.
    + apply notin_union_1 in H1.
      eauto.
    + apply notin_union_2 in H1.
      eauto.
  - simpl in *.
    apply d_wf_typ__all with (L:=L `union` singleton X `union` dom E `union` dom F); intros; inst_cofinites_with X0.
    + auto.
    + replace (X0 ~ dbind_tvar_empty ++ E ++ F) with ((X0 ~ dbind_tvar_empty ++ E)++ F) by auto. eapply H1 with (X:=X) (b:=b); auto.
      * rewrite_env (X0 ~ dbind_tvar_empty ++ (E ++ (X, b) :: F)). econstructor...
      * rewrite ftv_in_typ_open_typ_wrt_typ_upper; auto.
  - simpl in *. eauto.
  - simpl in *. eauto.
Qed.

(* Properties of d_wf_env *)
Lemma d_wf_env_subst_tvar_typ : forall E X F T1,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  E ⊢ T1 ->
  ⊢ (map (subst_tvar_in_dbind T1 X) F ++ E).
Proof with eauto using d_wft_typ_subst.
  intros * HE HT.
  induction F; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, d) :: (F ++ X ~ dbind_tvar_empty ++ E)) in HE.
    forwards HE': d_wf_env_strenthening_head HE.
    forwards~ IH: IHF.
    rewrite_env ([(a, subst_tvar_in_dbind T1 X d)]
                   ++ (map (subst_tvar_in_dbind T1 X) F ++ E)).
    forwards: d_wf_env_uniq HE.
    inverts H. destruct d...
    + econstructor...
      applys d_wft_typ_subst...
      inverts~ HE.
Qed.

(* This lemma cannot be used for svar subst because E ⊢ SY does not hold when SY is not in E *)
Lemma d_wf_env_subst_stvar_typ : forall E X F T1,
  ⊢ F ++ X ~ dbind_stvar_empty ++ E ->
  E ⊢ T1 ->
  ⊢ (map (subst_tvar_in_dbind T1 X) F ++ E).
Proof with eauto using d_wft_typ_subst.
  intros * HE HT.
  induction F; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, d) :: (F ++ X ~ dbind_stvar_empty ++ E)) in HE.
    forwards HE': d_wf_env_strenthening_head HE.
    forwards~ IH: IHF.
    rewrite_env ([(a, subst_tvar_in_dbind T1 X d)]
                   ++ (map (subst_tvar_in_dbind T1 X) F ++ E)).
    forwards: d_wf_env_uniq HE.
    inverts H. destruct d...
    + econstructor...
      applys d_wft_typ_subst_stvar...
      inverts~ HE.
Qed.

(* bookmark for refactoring *)

Corollary d_wf_env_weaken_tvar : forall E1 E2 X,
  ⊢ E2 ++ E1 ->
  X ∉ dom (E2 ++ E1) ->
  ⊢ E2 ++ X ~ ▫ ++ E1.
Proof with eauto.
  intros * HE HT. induction E2; intros.
  - econstructor...
  - rewrite_env (a :: (E2 ++ X ~ ▫ ++ E1)). destruct a. destruct d.
    1: rewrite_env ((a, ▫) :: (E2 ++ E1)) in HE.
    2: rewrite_env ((a, ▪) :: (E2 ++ E1)) in HE.
    3: rewrite_env ((a, dbind_typ A) :: (E2 ++ E1)) in HE.
    all: forwards HE': d_wf_env_strenthening_head HE; inverts HE.
    all: econstructor; try solve_notin.
    applys dwf_typ_weakening...
Qed.

Corollary d_wf_env_weaken_stvar : forall E1 E2 X,
  ⊢ E2 ++ E1 ->
  X ∉ dom (E2 ++ E1) ->
  ⊢ E2 ++ X ~ ▪ ++ E1.
Proof with eauto.
  intros * HE HT. induction E2; intros.
  - econstructor...
  - rewrite_env (a :: (E2 ++ X ~ ▪ ++ E1)). destruct a. destruct d.
    1: rewrite_env ((a, ▫) :: (E2 ++ E1)) in HE.
    2: rewrite_env ((a, ▪) :: (E2 ++ E1)) in HE.
    3: rewrite_env ((a, dbind_typ A) :: (E2 ++ E1)) in HE.
    all: forwards HE': d_wf_env_strenthening_head HE; inverts HE.
    all: econstructor; try solve_notin.
    applys dwf_typ_weakening...
Qed.

Lemma subst_same_tvar_typ_id : forall X T,
    {typ_var_f X /ᵈ X} T = T.
Proof with (try progress case_if); subst; simpl; eauto.
  intros. induction T; simpl...
  all: try rewrite IHT; try rewrite IHT1; try rewrite IHT2...
Qed.

Lemma subst_same_stvar_binding_id : forall X a,
    subst_tvar_in_dbind (typ_var_f X) X a = a.
Proof with subst; try rewrite subst_same_tvar_typ_id; simpl; eauto.
  intros. destruct a...
  induction* A...
Qed.

Lemma subst_same_tvar_map_id : forall X F,
    map (subst_tvar_in_dbind (typ_var_f X) X) F = F.
Proof with subst; try rewrite subst_same_tvar_typ_id; simpl; eauto.
  intros. induction F... destruct a...
  rewrite subst_same_stvar_binding_id. rewrite* IHF.
Qed.

Lemma dom_subst_id : forall T SX F,
    dom (map (subst_tvar_in_dbind T SX) F) = dom F.
Proof with simpl; eauto.
  intros *. induction* F.
  - destruct a. destruct d...
    all: rewrite IHF...
Qed.

Lemma d_wf_typ_rename_stvar : forall E F X Y A1,
  E ++ X ~ ▪ ++ F  ⊢ A1  ->
  map (subst_tvar_in_dbind (typ_var_f Y) X ) E ++ Y ~ ▪ ++ F ⊢ { typ_var_f Y /ᵈ X } A1.
Proof with try solve_notin; simpl in *; eauto.
  intros * HT.
  case_eq (X==Y); intros.
  1: { subst. rewrite* subst_same_tvar_map_id. rewrite subst_same_tvar_typ_id... }
  clear H.
  inductions HT...
  - case_if... induction E...
    all: inverts H; try solve_by_invert...
    + remember (let (x, a0) := a in (x, subst_tvar_in_dbind (typ_var_f Y) X a0)).
      remember (map (subst_tvar_in_dbind (typ_var_f Y) X) E ++ (Y, ▪) :: F).
      destruct p. 
      apply dwf_typ_weakening_cons.
      applys IHE...
  - case_if... induction E...
    + eapply d_wf_typ__stvar. case_eq (X0==Y); intros; subst...
      inverts* H. exfalso. applys C. inverts~ H1.
    + destruct a. inverts H.
      * inverts H0...
      * forwards: IHE...
        remember (map (subst_tvar_in_dbind (typ_var_f Y) X) E ++ (Y, ▪) :: F).
        rewrite_env ([(a, subst_tvar_in_dbind (typ_var_f Y) X d)] ++ l).
        applys* dwf_typ_weaken_head.
  - eapply d_wf_typ__all with (L:=L `union` singleton X); intros; inst_cofinites_with X0.
    + rewrite typ_subst_open_comm; eauto.
      apply ftv_sin_typ_subst_inv; auto.
    + intros.
      rewrite typ_subst_open_comm; eauto.
      rewrite_env (map (subst_tvar_in_dbind `ᵈ Y X) (X0 ~ ▫ ++ E) ++ (Y, ▪) :: F).
      auto.
Qed.


Corollary d_wf_env_rename_stvar : forall E X F Y,
  ⊢ F ++ X ~ dbind_stvar_empty ++ E ->
  Y ∉ dom (F ++ E) ->
  ⊢ map (subst_tvar_in_dbind (typ_var_f Y) X) F ++ Y ~ dbind_stvar_empty ++ E.
Proof with try solve_notin; simpl; eauto.
  intros * HE HT.
  case_eq (Y == X); intros.
  1: { subst. rewrite* subst_same_tvar_map_id. } clear H.
  rewrite_env ((F ++ X ~ ▪) ++ E) in HE.
  forwards HE': d_wf_env_weaken_stvar Y HE. { solve_notin. }
  induction F; intros; simpl.
  - inverts~ HE. econstructor...
  - destruct a. destruct d...
    + rewrite_env (((a, ▫) :: (F ++ X ~ ▪) ++ E)) in HE. inverts~ HE.
      rewrite_env ((a, ▫) :: (F ++ X ~ ▪) ++ (Y, ▪) :: E) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, ▪) :: (F ++ X ~ ▪) ++ E)) in HE. inverts~ HE.
      rewrite_env ((a, ▪) :: (F ++ X ~ ▪) ++ (Y, ▪) :: E) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, dbind_typ A) :: (F ++ X ~ ▪) ++ E)) in HE. inverts~ HE.
      rewrite_env ((a, dbind_typ A) :: (F ++ X ~ ▪) ++ (Y, ▪) :: E) in HE'. inverts~ HE'.
      econstructor...
      forwards*: IHF. solve_notin.
      applys d_wf_typ_rename_stvar...
      rewrite_env ((F ++ X ~ ▪) ++ E)...
Qed.

Lemma d_neq_all_rename: forall A1 X Y,
  lc_typ A1 ->
  neq_all A1 ->
  neq_all ({typ_var_f Y /ᵈ X} A1).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A1...
  - case_if; subst*.
  - eapply neq_all__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor; applys lc_typ_subst; try inverts~ H...
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.

Lemma d_neq_intersection_rename: forall A1 X Y,
  lc_typ A1 ->
  neq_intersection A1 ->
  neq_intersection ({typ_var_f Y /ᵈ X} A1).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A1...
  - case_if; subst*.
  - eapply neq_intersection__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor.
    forwards*: lc_typ_subst (typ_all A1) (typ_var_f Y) X.
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.


Lemma d_neq_union_rename: forall A1 X Y,
  lc_typ A1 ->
  neq_union A1 ->
  neq_union ({typ_var_f Y /ᵈ X} A1).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A1...
  - case_if; subst*.
  - eapply neq_union__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor.
    forwards*: lc_typ_subst (typ_all A1) (typ_var_f Y) X.
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.

(* Lemma rename_mono_typ : forall T SX SY,
    dmono_typ T ->
    {typ_svar SY /ₛᵈ SX} T = T.
Proof with simpl in *; eauto.
  intros * HM.
  induction HM...
  all: try rewrite IHHM1; try rewrite IHHM2...
Qed. *)

#[export] Hint Resolve d_neq_all_rename d_neq_intersection_rename d_neq_union_rename : sub.


Lemma neq_all_lc_typ : forall T,
  neq_all T -> lc_typ T.
Proof.
  intros. induction H; eauto.
Qed.

Lemma dneq_intersection_lc_typ : forall T,
  neq_intersection T -> lc_typ T.
Proof.
  intros. induction H; eauto.
Qed.

Lemma dneq_union_lc_typ : forall T,
  neq_union T -> lc_typ T.
Proof.
  intros. induction H; eauto.
Qed.

#[export] Hint Immediate neq_all_lc_typ dneq_intersection_lc_typ dneq_union_lc_typ : core.


(* Lemma lc_typ_open_stvar_subst_mono : forall S T SY,
    lc_typ (S ^^ᵈ T) -> d_mono_typ T -> lc_typ (S ^ᵈ SY).
Proof with try solve_notin; try solve_by_invert; simpl in *; eauto.
  intros * HD HM.
  inductions HD.
  all: destruct S; destruct T; unfold open_typ_wrt_typ in *; inverts x; subst; simpl in *...
  all: try destruct (lt_eq_lt_dec n 0); try case_if; try solve [inverts~ x].
  all: eauto...
  all: eapply lc_typ_all; intro Y;
      forwards: H Y; unfold open_typ_wrt_typ;
      rewrite open_typ_wrt_typ_twice; rewrite open_typ_wrt_typ_twice in H1;
    try applys H0; try rewrite open_typ_wrt_typ_twice...
Qed.

Lemma ds_in_open_stvar_subst_mono : forall S T SY SZ,
    ds_in SY (S ^^ᵈ T) -> dmono_typ T -> SY ∉ ftv_in_typ T -> ds_in SY (S ^ᵈ SZ).
Proof with try solve_notin; try solve_by_invert; simpl in *; eauto using lc_typ_open_stvar_subst_mono.
  intros * HD HM HN.
  inductions HD.
  all: destruct S; destruct T; unfold open_typ_wrt_typ in *; simpl in *; inverts x; subst;
    try destruct (lt_eq_lt_dec n 0); try case_if; try solve [inverts~ x];
    try solve [inverts H0; solve_notin]...
  all: try solve [inverts H1; inverts HM;
                  try solve [forwards*: IHHD (typ_var_b 0) T4];
                  try solve [forwards*: IHHD (typ_var_b 0) T3]].
  all: try solve [pick fresh Y and apply dsin_all; inst_cofinites_with Y;
                  rewrite open_typ_wrt_typ_twice in H0;
                  forwards*: H0;
                  unfold open_typ_wrt_typ; try rewrite open_typ_wrt_typ_twice; eauto].
  all: try solve [inverts H0; inverts HM;
                  forwards*: IHHD1 (typ_var_b 0) T3;
                  forwards*: IHHD2 (typ_var_b 0) T4].
Qed.


Lemma d_wf_typ_open_stvar_subst_mono : forall E F S T SY, 
    E ++ F ⊢ S ^^ᵈ T -> d_mono_typ (E ++ F) T -> SY ∉ (dom F)
    -> E ++ SY ~ ▫ ++ F ⊢ S ^ᵈ SY.
Proof with try solve_notin; simpl in *; eauto.
  intros * HT HD HN.
  inductions HT...
  all: destruct S; destruct T;
      lazymatch goal with
      | n : nat, Hx: _ = ↑ ?n ^^ᵈ _ |- _ =>
        try solve [
            induction n; unfold open_typ_wrt_typ in *; simpl in *; try solve_by_invert Hx; eauto using d_wf_env_weaken_tvar]
      | n : nat, Hx: _ = ↑ (S ?n) ^^ᵈ _ |- _ =>
        try solve [
            induction n; unfold open_typ_wrt_typ in Hx; simpl in Hx; inverts Hx]
      | Hx:`ᵈ _ = `ᵈ _ ^^ᵈ _ |- _ =>
          try solve [
              unfold open_typ_wrt_typ in *; simpl in *; inverts x;
              rewrite_env (E ++ [(SY, ▫)] ++ F); applys* dwf_typ_weakening;
              eauto using dwf_typ_weakening]
      | Hx: typ_svar _ = typ_svar _ ^^ᵈ _ |- _ =>
          try solve [
              unfold open_typ_wrt_typ in *; simpl in *; inverts x;
              rewrite_env (E ++ [(SY, ▫)] ++ F); applys* dwf_typ_weakening;
              eauto using dwf_typ_weakening]
      | Hx: _ = _ ^^ᵈ _ |- _ =>
          try solve [unfold open_typ_wrt_typ in Hx; simpl in Hx; inverts Hx];
          try solve [unfold open_typ_wrt_typ; simpl; eauto using d_wf_env_weaken_tvar];
          try solve [unfold open_typ_wrt_typ in *; simpl in *; inverts* Hx]
      end.
  all:
    try solve [
    pick fresh SZ and apply dwftyp_all;
      unfold open_typ_wrt_typ in *; rewrite open_typ_wrt_typ_twice in *;
      inverts* x;
      [ (forwards H': H SZ;
       try rewrite open_typ_wrt_typ_twice in H';
       try applys* ds_in_open_stvar_subst_mono H'; eauto) |
        (match goal with
        HD: dmono_typ ?A |- _ => assert (HE:
               open_typ_wrt_typ_rec 0 `ᵈ SZ (open_typ_wrt_typ_rec 1 A S)
               = open_typ_wrt_typ_rec 0 A (open_typ_wrt_typ_rec 0 `ᵈ SZ S) )
          by rewrite* open_typ_wrt_typ_twice;
                                 forwards*: H1 SZ ((SZ, ▫) :: E) F HE
      end) ]
      ].
Qed. 

*)
