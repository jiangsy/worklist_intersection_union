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
  A = {`ᵈ X /ᵗ X} A.
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
    open_typ_wrt_typ_rec n `ᵈ X (open_typ_wrt_typ_rec (n+1) Y A)
    = open_typ_wrt_typ_rec n Y (open_typ_wrt_typ_rec n `ᵈ X A).
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
  -> T1 = open_typ_wrt_typ T2 `ᵈ X -> close_typ_wrt_typ X T1 = T2.
Proof.
  intros * Fr H.
  assert (close_typ_wrt_typ X T1 = close_typ_wrt_typ X (open_typ_wrt_typ T2 `ᵈ X)) by now rewrite H.
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

Hint Constructors ds_in: core.


Lemma sin_in : forall X T,
  ds_in X T ->
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
  ds_in X ({T /ᵗ Y} A) ->
  ds_in X A.
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
      eapply IHds_in with (T:=A1) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply dsin_arrow1; inversion x; eauto.
      subst.
      eapply lc_typ_subst_inv; eauto.
  - destruct A; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + dependent destruction H.
      simpl in H0. eapply IHds_in with (T:=A2) (Y:=Y); auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X Y Y); auto.
      contradiction.
    + inversion x.
    + apply dsin_arrow2; inversion x; eauto.
      subst. eapply lc_typ_subst_inv; eauto.
  - destruct A; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (typ_all A0)).
      * eapply dsin_all with (L:=L). intros. inst_cofinites_with Y0.
        auto.
      * apply sin_in in H4. contradiction.
    + inversion x.
    + apply dsin_all with (L:=L `union` singleton Y); intros; inst_cofinites_with Y0. auto.
     inversion x. rewrite H6 in H3.
    eapply H2; eauto. subst. rewrite typ_subst_open_comm; auto.
  - destruct A; simpl; try solve [inversion x].
  simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (typ_union A1 A2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_union.
      * eapply IHds_in1 with (T:=T) (Y:=Y); eauto.
      * eapply IHds_in2 with (T:=T) (Y:=Y); eauto.
  - destruct A; simpl; try solve [inversion x].
    simpl in *. destruct (X0 == Y); subst.
    + assert (ds_in X (typ_intersection A1 A2)) by auto.
      apply sin_in in H2. contradiction.
    + inversion x.
    + inversion x. apply dsin_intersection.
      * eapply IHds_in1 with (T:=T) (Y:=Y); eauto.
      * eapply IHds_in2 with (T:=T) (Y:=Y); eauto.
Qed.


Lemma ftv_sin_typ_subst_inv : forall X Y T1 S1,
  lc_typ S1 ->
  X <> Y ->
  ds_in X T1 ->
  ds_in X ({S1 /ᵗ Y} T1).
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


Lemma d_mono_typ_lc : forall Ψ T,
  d_mono_typ Ψ T -> lc_typ T.
Proof.
  intros; induction H; auto.
Qed.


Lemma d_wf_typ_subst_tvar_stvar : forall Ψ1 Ψ2 X A,
  Ψ2 ++ [(X, dbind_tvar_empty)]  ++ Ψ1 ⊢ₛ A  ->
  Ψ2 ++ [(X, dbind_stvar_empty)] ++ Ψ1 ⊢ₛ A.
Proof.
  intros Ψ1 Ψ2 X A H.
  dependent induction H; try solve [simpl; auto].
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
    + subst. eapply d_wf_typ_s__stvar. auto.
    + econstructor.
      induction Ψ2.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. eapply d_wf_typ_s__stvar. auto.
    induction Ψ2.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. constructor.
    + apply IHd_wf_typ_s1; auto.
    + apply IHd_wf_typ_s2; auto.
  - simpl. eapply d_wf_typ_s__all with (L:=L);
    intros X1 Hf; inst_cofinites_with X1.
    + auto.
    + rewrite_env ((X1 ~ ▪ ++ Ψ2) ++ (X, ▪) :: Ψ1 ).
      apply H1; eauto.
  - simpl. constructor.
    + apply IHd_wf_typ_s1; auto.
    + apply IHd_wf_typ_s2; auto.
  - simpl. constructor.
    + apply IHd_wf_typ_s1; auto.
    + apply IHd_wf_typ_s2; auto.
Qed.


Lemma d_wf_typ_subst_stvar_tvar : forall Ψ1 Ψ2 X T,
  Ψ2 ++ [(X, dbind_stvar_empty)] ++ Ψ1 ⊢ T  ->
  Ψ2 ++ [(X, dbind_tvar_empty)]  ++ Ψ1 ⊢ T.
Proof.
  intros Ψ1 Ψ2 X T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. constructor.
    induction Ψ2.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
    + econstructor; auto.
    + apply d_wf_typ__stvar.
      induction Ψ2.
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
    + rewrite_env ((X0 ~ ▫ ++ Ψ2) ++ (X, ▫) :: Ψ1).
      apply H1; eauto.
  - simpl. constructor.
    + apply IHd_wf_typ1; auto.
    + apply IHd_wf_typ2; auto.
  - simpl. constructor.
    + apply IHd_wf_typ1; auto.
    + apply IHd_wf_typ2; auto.
Qed.

Corollary d_wf_typ_subst_stvar_tvar_cons : forall Ψ X A,
  X `notin` ftvar_in_typ A ->
  X ~ dbind_tvar_empty ++ Ψ ⊢ₛ A ^ᵈ X ->
  X ~ dbind_stvar_empty ++ Ψ ⊢ₛ A ^ᵈ X.
Proof.
  intros.
  rewrite_env (nil ++ X ~ dbind_stvar_empty ++ Ψ).
  apply d_wf_typ_subst_tvar_stvar.
  auto.
Qed.

Corollary d_wf_typ_subst_tvar_stvar_cons : forall Ψ X T,
  X `notin` ftvar_in_typ T ->
  X ~ dbind_stvar_empty ++ Ψ ⊢ T ^ᵈ X ->
  X ~ dbind_tvar_empty ++ Ψ ⊢ T ^ᵈ X.
Proof.
  intros.
  rewrite_env (nil ++ X ~ dbind_tvar_empty ++ Ψ).
  apply d_wf_typ_subst_stvar_tvar; eauto.
Qed.

Lemma dwf_typ_dwf_typ_s : forall Ψ A,
  Ψ ⊢ A -> Ψ ⊢ₛ A.
Proof.
  intros.
  induction H; auto.
  - eapply d_wf_typ_s__all with (L:= (L `union` ftvar_in_typ A));
    intros; auto.
    + apply d_wf_typ_subst_stvar_tvar_cons; auto.
Qed.

Lemma dwf_typ_s_dwf_typ : forall Ψ A,
  Ψ ⊢ₛ A -> Ψ ⊢ A.
Proof.
  intros. induction H; auto.
  - eapply d_wf_typ__all with (L:= (L `union` ftvar_in_typ A));
    intros; inst_cofinites_with X.
    + auto.
    + eapply d_wf_typ_subst_tvar_stvar_cons; auto.
Qed.

Hint Constructors d_sub : core.
Hint Immediate dwf_typ_dwf_typ_s : core.
Hint Immediate dwf_typ_s_dwf_typ : core.

Lemma dwf_typ_dlc_type : forall Ψ A,
  Ψ ⊢ A -> lc_typ A.
Proof.
  intros; induction H; auto.
Qed.

Lemma dwf_typ_s_dlc_type : forall Ψ A,
  Ψ ⊢ₛ A -> lc_typ A.
Proof.
  intros.
  eapply dwf_typ_dlc_type.
  apply dwf_typ_s_dwf_typ.
  eauto.
Qed.

Hint Resolve dwf_typ_s_dlc_type : core.

Hint Constructors neq_union : Core.
Hint Constructors neq_intersection : Core.


Lemma dwf_typ_open_inv : forall Ψ1 A1 T1 X,
  lc_typ T1 ->
  Ψ1 ⊢ {T1 /ᵗ X} A1 ->
  binds X dbind_tvar_empty Ψ1 ->
  Ψ1 ⊢ A1.
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
      eapply d_wf_typ__all with (L:=L `union` singleton X `union` ftvar_in_typ T1); intros;
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


Lemma dwf_typ_weakening : forall Ψ1 Ψ2 Ψ3 A,
  Ψ3 ++ Ψ1 ⊢ A ->
  (* uniq (E3 ++ Ψ2 ++ Ψ1) -> *)
  Ψ3 ++ Ψ2 ++ Ψ1 ⊢ A.
Proof.
  intros.
  dependent induction H; auto.
  - eapply d_wf_typ__all with (L:=L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1));
    intros; inst_cofinites_with X.
    + auto.
    + rewrite_env ((X ~ dbind_tvar_empty ++ Ψ3) ++ Ψ2 ++ Ψ1).
      eapply H1; eauto.
Qed.

Corollary dwf_typ_weakening_cons : forall Ψ X b A,
  Ψ ⊢ A ->
  (* uniq ((X ~ b) ++ Ψ1) -> *)
  ((X ~ b) ++ Ψ) ⊢ A.
Proof.
  intros.
  replace (X ~ b ++ Ψ) with (nil ++ X ~ b ++ Ψ) by auto.
  apply dwf_typ_weakening; auto.
Qed.

Corollary dwf_typ_weaken_head: forall Ψ1 Ψ2 T,
    Ψ1 ⊢ T ->
  (* uniq (Ψ2 ++ Ψ1) -> *)
  Ψ2 ++ Ψ1 ⊢ T.
Proof.
  intros.
  rewrite_env (nil++Ψ2++Ψ1).
  applys* dwf_typ_weakening.
Qed.

Lemma d_wf_env_uniq: forall Ψ,
  ⊢ Ψ -> uniq Ψ.
Proof.
  intros.
  induction H; auto.
Qed.

Lemma d_wf_env_strenthening : forall Ψ1 X Ψ2,
  ⊢ Ψ2 ++ X ~ dbind_tvar_empty ++ Ψ1 ->
  ⊢ Ψ2 ++ Ψ1.
Abort.
(* Wrong Lemma Ψ2 = (y : X) *)

Lemma d_wf_env_strenthening_head : forall a Ψ,
    ⊢ a :: Ψ -> ⊢ Ψ.
Proof with auto.
  intros * H.
  inverts* H.
Qed.

Hint Resolve d_wf_env_uniq : core.
Hint Resolve dwf_typ_weakening_cons : core.

Lemma dwf_env_binds_dwf_typ : forall Ψ x A,
  ⊢ Ψ ->
  x ~ A ∈ Ψ ->
  Ψ ⊢ A.
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


Hint Constructors d_typing : core.

(* Lemma d_wft_typ_swap_env : forall Ψ2 X Y Ψ1 T ,
    Ψ2 ++ X ~ dbind_tvar_empty ++ Y ~ dbind_tvar_empty ++ Ψ1 ⊢ T ->
    Ψ2 ++ Y ~ dbind_tvar_empty ++ X ~ dbind_tvar_empty ++ Ψ1 ⊢ T.
Proof with eauto.
  intros * HT.
  inductions HT...
  - forwards* [?|?]: binds_app_1 H.
    forwards* [?|?]: binds_app_1 H0.
  - forwards* [?|?]: binds_app_1 H.
    forwards* [?|?]: binds_app_1 H0.
  - pick fresh y and apply dwftyp_all. inst_cofinites_with y.
    applys* H.
    rewrite_env ((y ~ dbind_tvar_empty ++ Ψ2) ++ Y ~ dbind_tvar_empty ++ X ~ dbind_tvar_empty ++ Ψ1 ).
    applys* H1.
Qed. *)


Lemma d_wft_typ_subst : forall Ψ1 X Ψ2 A1 T2,
  ⊢ Ψ2 ++ X ~ dbind_tvar_empty ++ Ψ1 ->
  Ψ2 ++ X ~ dbind_tvar_empty ++ Ψ1 ⊢ A1 ->
  Ψ1 ⊢ T2 ->
  map (subst_tvar_in_dbind T2 X) Ψ2  ++ Ψ1 ⊢ {T2 /ᵗ X} A1.
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
      replace ((X0, dbind_tvar_empty) :: map (subst_tvar_in_dbind T2 X) Ψ2 ++ Ψ1)
      with (map (subst_tvar_in_dbind T2 X) ((X0, dbind_tvar_empty) :: Ψ2) ++ Ψ1) by auto.
      apply H1; auto...
      econstructor...
Qed.

Lemma d_wft_all_open : forall Ψ1 A1 T1,
  ⊢ Ψ1 ->
  Ψ1 ⊢ typ_all A1 ->
  Ψ1 ⊢ T1 ->
  Ψ1 ⊢ A1 ^^ᵈ T1.
Proof.
  intros.
  inversion H0.
  inst_cofinites_by (L `union` ftvar_in_typ A1 `union` dom Ψ1) using_name X.
  rewrite_env (map (subst_tvar_in_dbind T1 X) nil ++ Ψ1).
  erewrite <- typ_subst_open_var; eauto.
  apply d_wft_typ_subst; eauto.
  econstructor; auto.
Qed.


Lemma d_wft_typ_subst_stvar : forall Ψ1 X Ψ2 A1 T2,
  ⊢ Ψ2 ++ X ~ dbind_stvar_empty ++ Ψ1 ->
  Ψ2 ++ X ~ dbind_stvar_empty ++ Ψ1 ⊢ A1 ->
  Ψ1 ⊢ T2 ->
  map (subst_tvar_in_dbind T2 X) Ψ2 ++ Ψ1 ⊢ {T2 /ᵗ X} A1.
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
      replace ((X0, dbind_tvar_empty) :: map (subst_tvar_in_dbind T2 X) Ψ2 ++ Ψ1)
      with (map (subst_tvar_in_dbind T2 X) ((X0, dbind_tvar_empty) :: Ψ2) ++ Ψ1) by auto.
      apply H1; auto...
      econstructor...
Qed.


Lemma d_new_tv_notin_wf_typ : forall X Ψ A,
  ⊢ (X, dbind_tvar_empty) :: Ψ ->
  Ψ ⊢ A ->
  X `notin` ftvar_in_typ A.
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
  - simpl. inst_cofinites_by (L `union` singleton X `union` dom Ψ) using_name X.
    assert (⊢ (X, dbind_tvar_empty) :: X0 ~ dbind_tvar_empty ++ Ψ).
    constructor; auto.
    + constructor; auto. dependent destruction H; auto.
    + simpl. apply notin_add_3; auto.
      dependent destruction H; auto.
    + specialize (H2 H3).
      rewrite ftvar_in_typ_open_typ_wrt_typ_lower; auto.
Qed.

Lemma d_wf_typ_lc_typ : forall Ψ A,
  Ψ ⊢ A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

#[export] Hint Resolve d_mono_typ_lc : core.

Lemma d_mono_typ_neq_all : forall Ψ A,
  d_mono_typ Ψ A -> neq_all A.
Proof.
  intros; induction H; eauto...
Qed.


Lemma d_neq_all_subst_neq_all : forall Ψ A X T,
  lc_typ A ->
  d_mono_typ Ψ T ->
  neq_all A ->
  neq_all ( {T /ᵗ X} A ).
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


Lemma bind_typ_subst : forall Ψ2 X Ψ1 x T1 T2,
  ⊢ Ψ2 ++ (X, dbind_tvar_empty) :: Ψ1 ->
  x ~ T1 ∈ (Ψ2 ++ (X, dbind_tvar_empty) :: Ψ1) ->
  Ψ1 ⊢ T2 ->
  x ~ ({T2 /ᵗ X} T1) ∈ (map (subst_tvar_in_dbind T2 X) Ψ2 ++ Ψ1).
Proof.
  intros. induction Ψ2; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (Ψ1 ⊢ T1).
      { eapply dwf_env_binds_dwf_typ; eauto. inversion H. auto. }
      rewrite subst_tvar_in_typ_fresh_eq; auto.
      eapply d_new_tv_notin_wf_typ; eauto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      apply IHΨ2; auto.
      inversion H; auto.
Qed.


Lemma d_mono_typ_weaken_head: forall Ψ T a,
    d_mono_typ Ψ T -> d_mono_typ (a ++ Ψ) T.
Proof.
  intros. induction* H.
Qed.

Lemma d_mono_typ_weakening : forall Ψ1 Ψ2 Ψ3 A,
  d_mono_typ  (Ψ3 ++ Ψ1) A -> d_mono_typ (Ψ3 ++ Ψ2 ++ Ψ1) A.
Proof.
  intros.
  dependent induction H; auto.
Qed.


Lemma d_mono_typ_subst_mono_mono : forall F Ψ A T X,
  d_mono_typ (F ++ X ~ ▫ ++ Ψ) A ->
  d_mono_typ Ψ T ->
  d_mono_typ (map (subst_tvar_in_dbind T X) F ++ Ψ) ({T /ᵗ X} A).
Proof with eauto using d_mono_typ_weaken_head; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction A; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       inverts H.
       forwards* [?|?]: binds_app_1 H3. forwards*: binds_map_2 (subst_tvar_in_dbind T X) H.
       forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
  }
  all: simpl; dependent destruction H; auto.
Qed.



Lemma binds_two_thing_false : forall X Ψ,
    X ~ ▪ ∈ Ψ -> ⊢ Ψ -> X ~ ▫ ∈ Ψ -> False.
Proof.
  intros.
  forwards: d_wf_env_uniq H0.
  forwards*: binds_unique H H2. inverts H3.
Qed.

Theorem d_sub_mono_stvar_false : forall Ψ A X,
  X ~ ▪ ∈ Ψ ->
  Ψ ⊢ A <: typ_var_f X ->
  d_mono_typ Ψ A ->
  False.
Proof.
  intros.
  induction H1; dependent destruction H0; auto.
  applys* binds_two_thing_false.
Qed.

Lemma d_mono_typ_no_stvar : forall F Ψ A X,
    d_mono_typ (F ++ X ~ ▪ ++ Ψ) A ->
    ⊢ F ++ X ~ ▪ ++ Ψ ->
    X `notin` ftvar_in_typ A.
Proof with eauto using d_mono_typ_weaken_head; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction A; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       - inverts H.
         assert (X ~ ▪ ∈ (F ++ (X, ▪) :: Ψ)) by eauto.
         exfalso. forwards*: binds_two_thing_false X.
  }
  all: simpl; dependent destruction H; auto.
Qed.

Lemma d_mono_typ_drop_stvar : forall F Ψ A X,
    d_mono_typ (F ++ X ~ ▪ ++ Ψ) A ->
    d_mono_typ (F ++ Ψ) A.
Proof with eauto using d_mono_typ_weaken_head; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction A; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       - inverts H. forwards* [?|?]: binds_app_1 H2.
         forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
       - inverts H. forwards* [?|?]: binds_app_1 H2.
         forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
  }
  all: simpl; dependent destruction H; auto.
Qed.

Lemma d_mono_typ_subst_stvar : forall F Ψ A T X,
    d_mono_typ (F ++ X ~ ▪ ++ Ψ) A ->
    ⊢ F ++ X ~ ▪ ++ Ψ ->
    Ψ ⊢ T ->
    d_mono_typ (map (subst_tvar_in_dbind T X) F ++ Ψ) ({T /ᵗ X} A).
Proof with eauto using d_mono_typ_weaken_head; try solve_by_invert; try solve [exfalso; jauto].
  intros. induction A; simpl in *...
  1: { simpl. destruct (X0 == X); subst; auto...
       - inverts H.
         assert (X ~ ▪ ∈ (F ++ (X, ▪) :: Ψ)) by eauto.
         exfalso. forwards*: binds_two_thing_false X.
       - inverts H.
         forwards* [?|?]: binds_app_1 H4... forwards*: binds_map_2 (subst_tvar_in_dbind T X) H.
       forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto...
  }
  all: simpl; dependent destruction H; auto.
Qed.

Lemma d_sub_dwft : forall Ψ A B,
  Ψ ⊢ A <: B -> ⊢ Ψ /\ Ψ ⊢ A /\ Ψ ⊢ B.
Proof with auto.
  intros.
  induction H; try solve [intuition].
  - split.
    inst_cofinites_by L. intuition... inversion H3. auto.
    split; eapply d_wf_typ__all with (L:=L `union` ftvar_in_typ A `union` ftvar_in_typ B); intros; inst_cofinites_with X; auto...
    eapply d_wf_typ_subst_tvar_stvar_cons; intuition.
    eapply d_wf_typ_subst_tvar_stvar_cons; intuition.
  - split; try solve [intuition].
    split; try solve [intuition].
    + eapply d_wf_typ__all with (L:=L `union` ftvar_in_typ A `union` dom Ψ).
      * intros. inst_cofinites_with X. auto.
      * intros. inst_cofinites_with X.
        destruct IHd_sub. auto.
        eapply dwf_typ_open_inv with (X:=X) (T1:=T); auto.
        -- eapply d_mono_typ_lc; eauto.
        -- replace (X ~ dbind_tvar_empty ++ Ψ) with (nil ++ X ~ dbind_tvar_empty ++ Ψ) by auto.
           apply dwf_typ_weakening. simpl. rewrite  subst_tvar_in_typ_open_typ_wrt_typ.
           ++ simpl. unfold eq_dec. destruct ( EqDec_eq_of_X X X ).
              ** rewrite subst_tvar_in_typ_fresh_eq; intuition.
              ** contradiction.
           ++ eapply d_mono_typ_lc; eauto.
           (* ++ auto. *)
Qed.

Lemma d_sub_dwft_0 : forall Ψ A B,
    Ψ ⊢ A <: B -> ⊢ Ψ.
Proof.
  intros. forwards*: d_sub_dwft H.
Qed.

Lemma d_sub_dwft_1 : forall Ψ A B,
    Ψ ⊢ A <: B -> Ψ ⊢ A.
Proof.
  intros. forwards*: d_sub_dwft H.
Qed.

Lemma d_sub_dwft_2 : forall Ψ A B,
    Ψ ⊢ A <: B -> Ψ ⊢ B.
Proof.
  intros. forwards*: d_sub_dwft H.
Qed.

Lemma dwf_typ_strengthening : forall Ψ1 Ψ2 X A b,
    ⊢ Ψ2 ++ X ~ b ++ Ψ1 ->
    Ψ2 ++ X ~ b ++ Ψ1 ⊢ A ->
    X \notin ftvar_in_typ A ->
    Ψ2 ++ Ψ1 ⊢ A.
Proof with eauto.
  intros * Hwfenv H. intros.
  dependent induction H; auto.
  - induction Ψ2.
    + inversion H. dependent destruction H1.
      simpl in H0. apply notin_singleton_1 in H0. contradiction.
      auto.
    + destruct a. inversion H.
      * dependent destruction H1. auto.
      * simpl. apply dwf_typ_weakening_cons. apply IHΨ2; auto.
        rewrite_env ((a, d) :: (Ψ2 ++ X ~ b ++ Ψ1)) in Hwfenv. applys* d_wf_env_strenthening_head.
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - induction Ψ2.
    + inversion H. dependent destruction H1.
      * simpl in H0. apply notin_singleton_1 in H0. contradiction.
      * auto.
    + destruct a. inversion H.
      * dependent destruction H1. auto.
      * simpl. apply dwf_typ_weakening_cons; auto. apply IHΨ2; auto.
        rewrite_env ((a, d) :: (Ψ2 ++ X ~ b ++ Ψ1)) in Hwfenv. applys* d_wf_env_strenthening_head.
        (* forwards: d_wf_env_uniq Hwfenv. solve_uniq. *)
  - simpl in *. constructor.
    + apply notin_union_1 in H1.
      eauto.
    + apply notin_union_2 in H1.
      eauto.
  - simpl in *.
    apply d_wf_typ__all with (L:=L `union` singleton X `union` dom Ψ1 `union` dom Ψ2); intros; inst_cofinites_with X0.
    + auto.
    + replace (X0 ~ dbind_tvar_empty ++ Ψ2 ++ Ψ1) with ((X0 ~ dbind_tvar_empty ++ Ψ2)++ Ψ1) by auto. eapply H1 with (X:=X) (b:=b); auto.
      * rewrite_env (X0 ~ dbind_tvar_empty ++ (Ψ2 ++ (X, b) :: Ψ1)). econstructor...
      * rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
  - simpl in *. eauto.
  - simpl in *. eauto.
Qed.

(* Properties of d_wf_env *)
Lemma d_wf_env_subst_tvar_typ : forall Ψ1 X Ψ2 T,
  ⊢ Ψ2 ++ X ~ dbind_tvar_empty ++ Ψ1 ->
  Ψ1 ⊢ T ->
  ⊢ (map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1).
Proof with eauto using d_wft_typ_subst.
  intros * HE HT.
  induction Ψ2; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, d) :: (Ψ2 ++ X ~ dbind_tvar_empty ++ Ψ1)) in HE.
    forwards HE': d_wf_env_strenthening_head HE.
    forwards~ IH: IHΨ2.
    rewrite_env ([(a, subst_tvar_in_dbind T X d)]
                   ++ (map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1)).
    forwards: d_wf_env_uniq HE.
    inverts H. destruct d...
    + econstructor...
      applys d_wft_typ_subst...
      inverts~ HE.
Qed.

(* This lemma cannot be used for svar subst because Ψ1 ⊢ SY does not hold when SY is not in Ψ1 *)
Lemma d_wf_env_subst_stvar_typ : forall Ψ1 X Ψ2 T,
  ⊢ Ψ2 ++ X ~ dbind_stvar_empty ++ Ψ1 ->
  Ψ1 ⊢ T ->
  ⊢ (map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1).
Proof with eauto using d_wft_typ_subst.
  intros * HE HT.
  induction Ψ2; intros; simpl.
  - inverts~ HE.
  - destruct a. rewrite_env ((a, d) :: (Ψ2 ++ X ~ dbind_stvar_empty ++ Ψ1)) in HE.
    forwards HE': d_wf_env_strenthening_head HE.
    forwards~ IH: IHΨ2.
    rewrite_env ([(a, subst_tvar_in_dbind T X d)]
                   ++ (map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1)).
    forwards: d_wf_env_uniq HE.
    inverts H. destruct d...
    + econstructor...
      applys d_wft_typ_subst_stvar...
      inverts~ HE.
Qed.

(* bookmark for refactoring *)

Corollary d_wf_env_weaken_tvar : forall Ψ1 Ψ2 X,
  ⊢ Ψ2 ++ Ψ1 ->
  X ∉ dom (Ψ2 ++ Ψ1) ->
  ⊢ Ψ2 ++ X ~ ▫ ++ Ψ1.
Proof with eauto.
  intros * HE HT. induction Ψ2; intros.
  - econstructor...
  - rewrite_env (a :: (Ψ2 ++ X ~ ▫ ++ Ψ1)). destruct a. destruct d.
    1: rewrite_env ((a, ▫) :: (Ψ2 ++ Ψ1)) in HE.
    2: rewrite_env ((a, ▪) :: (Ψ2 ++ Ψ1)) in HE.
    3: rewrite_env ((a, dbind_typ A) :: (Ψ2 ++ Ψ1)) in HE.
    all: forwards HE': d_wf_env_strenthening_head HE; inverts HE.
    all: econstructor; try solve_notin.
    applys dwf_typ_weakening...
Qed.

Corollary d_wf_env_weaken_stvar : forall Ψ1 Ψ2 X,
  ⊢ Ψ2 ++ Ψ1 ->
  X ∉ dom (Ψ2 ++ Ψ1) ->
  ⊢ Ψ2 ++ X ~ ▪ ++ Ψ1.
Proof with eauto.
  intros * HE HT. induction Ψ2; intros.
  - econstructor...
  - rewrite_env (a :: (Ψ2 ++ X ~ ▪ ++ Ψ1)). destruct a. destruct d.
    1: rewrite_env ((a, ▫) :: (Ψ2 ++ Ψ1)) in HE.
    2: rewrite_env ((a, ▪) :: (Ψ2 ++ Ψ1)) in HE.
    3: rewrite_env ((a, dbind_typ A) :: (Ψ2 ++ Ψ1)) in HE.
    all: forwards HE': d_wf_env_strenthening_head HE; inverts HE.
    all: econstructor; try solve_notin.
    applys dwf_typ_weakening...
Qed.


Lemma subst_same_tvar_typ_id : forall X T,
    {typ_var_f X /ᵗ X} T = T.
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

Lemma subst_same_tvar_map_id : forall X Ψ,
    map (subst_tvar_in_dbind (typ_var_f X) X) Ψ = Ψ.
Proof with subst; try rewrite subst_same_tvar_typ_id; simpl; eauto.
  intros. induction Ψ... destruct a...
  rewrite subst_same_stvar_binding_id. rewrite* IHΨ.
Qed.

Lemma dom_subst_id : forall T X Ψ,
    dom (map (subst_tvar_in_dbind T X) Ψ) = dom Ψ.
Proof with simpl; eauto.
  intros *. induction* Ψ.
  - destruct a. destruct d...
    all: rewrite IHΨ...
Qed.

Lemma d_wf_typ_rename_stvar : forall Ψ1 Ψ2 X Y A,
  Ψ2 ++ X ~ ▪ ++ Ψ1  ⊢ A  ->
  map (subst_tvar_in_dbind (typ_var_f Y) X ) Ψ2 ++ Y ~ ▪ ++ Ψ1 ⊢ { typ_var_f Y /ᵗ X } A.
Proof with try solve_notin; simpl in *; eauto.
  intros * HT.
  case_eq (X==Y); intros.
  1: { subst. rewrite* subst_same_tvar_map_id. rewrite subst_same_tvar_typ_id... }
  clear H.
  inductions HT...
  - case_if... induction Ψ2...
    all: inverts H; try solve_by_invert...
    + remember (let (x, a0) := a in (x, subst_tvar_in_dbind (typ_var_f Y) X a0)).
      remember (map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ1 ++ (Y, ▪) :: Ψ2).
      destruct p.
      apply dwf_typ_weakening_cons.
      applys IHΨ2...
  - case_if... induction Ψ2...
    + eapply d_wf_typ__stvar. case_eq (X0==Y); intros; subst...
      inverts* H. exfalso. applys C. inverts~ H1.
    + destruct a. inverts H.
      * inverts H0...
      * forwards: IHΨ2...
        remember (map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2 ++ (Y, ▪) :: Ψ1).
        rewrite_env ([(a, subst_tvar_in_dbind (typ_var_f Y) X d)] ++ l).
        applys* dwf_typ_weaken_head.
  - eapply d_wf_typ__all with (L:=L `union` singleton X); intros; inst_cofinites_with X0.
    + rewrite typ_subst_open_comm; eauto.
      apply ftv_sin_typ_subst_inv; auto.
    + intros.
      rewrite typ_subst_open_comm; eauto.
      rewrite_env (map (subst_tvar_in_dbind `ᵈ Y X) (X0 ~ ▫ ++ Ψ2) ++ (Y, ▪) :: Ψ1).
      auto.
Qed.


Corollary d_wf_env_rename_stvar : forall Ψ1 X Ψ2 Y,
  ⊢ Ψ2 ++ X ~ dbind_stvar_empty ++ Ψ1 ->
  Y ∉ dom (Ψ2 ++ Ψ1) ->
  ⊢ map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2 ++ Y ~ dbind_stvar_empty ++ Ψ1.
Proof with try solve_notin; simpl; eauto.
  intros * HE HT.
  case_eq (Y == X); intros.
  1: { subst. rewrite* subst_same_tvar_map_id. } clear H.
  rewrite_env ((Ψ2 ++ X ~ ▪) ++ Ψ1) in HE.
  forwards HE': d_wf_env_weaken_stvar Y HE. { solve_notin. }
  induction Ψ2; intros; simpl.
  - inverts~ HE. econstructor...
  - destruct a. destruct d...
    + rewrite_env (((a, ▫) :: (Ψ2 ++ X ~ ▪) ++ Ψ1)) in HE. inverts~ HE.
      rewrite_env ((a, ▫) :: (Ψ2 ++ X ~ ▪) ++ (Y, ▪) :: Ψ1) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, ▪) :: (Ψ2 ++ X ~ ▪) ++ Ψ1)) in HE. inverts~ HE.
      rewrite_env ((a, ▪) :: (Ψ2 ++ X ~ ▪) ++ (Y, ▪) :: Ψ1) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, dbind_typ A) :: (Ψ2 ++ X ~ ▪) ++ Ψ1)) in HE. inverts~ HE.
      rewrite_env ((a, dbind_typ A) :: (Ψ2 ++ X ~ ▪) ++ (Y, ▪) :: Ψ1) in HE'. inverts~ HE'.
      econstructor...
      forwards*: IHΨ2. solve_notin.
      applys d_wf_typ_rename_stvar...
      rewrite_env ((Ψ2 ++ X ~ ▪) ++ Ψ1)...
Qed.

Lemma d_neq_all_rename: forall A X Y,
  lc_typ A ->
  neq_all A ->
  neq_all ({typ_var_f Y /ᵗ X} A).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A...
  - case_if; subst*.
  - eapply neq_all__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor; applys lc_typ_subst; try inverts~ H...
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.

Lemma d_neq_intersection_rename: forall A X Y,
  lc_typ A ->
  neq_intersection A ->
  neq_intersection ({typ_var_f Y /ᵗ X} A).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A...
  - case_if; subst*.
  - eapply neq_intersection__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor.
    forwards*: lc_typ_subst (typ_all A) (typ_var_f Y) X.
  - econstructor; applys lc_typ_subst; try inverts~ H...
Qed.


Lemma d_neq_union_rename: forall A X Y,
  lc_typ A ->
  neq_union A ->
  neq_union ({typ_var_f Y /ᵗ X} A).
Proof with  simpl; eauto using lc_typ_subst; try solve_by_invert.
  intros. destruct A...
  - case_if; subst*.
  - eapply neq_union__arrow;
      applys lc_typ_subst...
    all: inverts~ H.
  - econstructor.
    forwards*: lc_typ_subst (typ_all A) (typ_var_f Y) X.
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


Lemma neq_all_lc_typ : forall A,
  neq_all A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma dneq_intersection_lc_typ : forall A,
  neq_intersection A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma dneq_union_lc_typ : forall A,
  neq_union A -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

#[export] Hint Immediate neq_all_lc_typ dneq_intersection_lc_typ dneq_union_lc_typ : core.


Lemma lc_typ_open_stvar_subst_mono : forall S Ψ T SY,
    lc_typ (S ^^ᵈ T) -> d_mono_typ Ψ T -> lc_typ (S ^ᵈ SY).
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

Lemma d_mono_typ_for_any_var : forall Y,
  exists E, d_mono_typ E `ᵈ Y.
Proof with eauto.
  intros. exists* (Y ~ ▫ ++ nil).
Qed.

Lemma ds_in_open_stvar_subst_mono : forall S T Ψ SY SZ,
    ds_in SY (S ^^ᵈ T) -> d_mono_typ Ψ T -> SY ∉ ftvar_in_typ T -> ds_in SY (S ^ᵈ SZ).
Proof with try solve_notin; try solve_by_invert; simpl in *; eauto using lc_typ_open_stvar_subst_mono.
  intros * HD HM HN.
  inductions HD.
  all: destruct S; destruct T; unfold open_typ_wrt_typ in *; simpl in *; inverts x; subst;
    try destruct (lt_eq_lt_dec n 0); try case_if; try solve [inverts~ x];
    try solve [inverts H0; solve_notin]...
  all: try solve [inverts H1; inverts HM;
                  try solve [forwards*: IHHD (typ_var_b 0) T1];
                  try solve [forwards*: IHHD (typ_var_b 0) T2]].
  all: try solve [
           pick fresh Y and apply dsin_all; inst_cofinites_with Y;
           rewrite open_typ_wrt_typ_twice in H0;
           [ forwards*: H0 | ];
           unfold open_typ_wrt_typ; try rewrite open_typ_wrt_typ_twice;
           eauto using lc_typ_open_stvar_subst_mono ].
  all: try solve [
           inverts H0; inverts HM;
                  forwards*: IHHD1 (typ_var_b 0) T1;
                  forwards*: IHHD2 (typ_var_b 0) T2 ].
Qed.

Lemma d_wf_typ_open_tvar_subst_mono : forall Ψ1 Ψ2 S T SY,
    Ψ1 ++ Ψ2 ⊢ S ^^ᵈ T -> d_mono_typ (Ψ1 ++ Ψ2) T -> SY ∉ (dom Ψ2)
    -> Ψ1 ++ SY ~ ▫ ++ Ψ2 ⊢ S ^ᵈ SY.
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
              rewrite_env (Ψ1 ++ [(SY, ▫)] ++ Ψ2); applys* dwf_typ_weakening;
              eauto using dwf_typ_weakening]
      (* | Hx: dtyp_svar _ = dtyp_svar _ ^^ᵈ _ |- _ => *)
      (*     try solve [ *)
      (*         unfold open_typ_wrt_typ in *; simpl in *; inverts x; *)
      (*         rewrite_env (Ψ1 ++ [(SY, ▫)] ++ Ψ2); applys* dwf_typ_weakening; *)
      (*         eauto using dwf_typ_weakening] *)
      | Hx: _ = _ ^^ᵈ _ |- _ =>
          try solve [unfold open_typ_wrt_typ in Hx; simpl in x; inverts x];
          try solve [unfold open_typ_wrt_typ; simpl; eauto using d_wf_env_weaken_tvar];
          try solve [unfold open_typ_wrt_typ in *; simpl in *; inverts* x]
      end.
 all: try solve [
    pick fresh SZ and apply d_wf_typ__all;
      unfold open_typ_wrt_typ in *; rewrite open_typ_wrt_typ_twice in *;
      inverts* x;
      [ (forwards H': H SZ;
       try rewrite open_typ_wrt_typ_twice in H';
       try applys* ds_in_open_stvar_subst_mono H'; eauto) |
        (match goal with
        HD: d_mono_typ _ ?A |- _ => assert (HE:
               open_typ_wrt_typ_rec 0 `ᵈ SZ (open_typ_wrt_typ_rec 1 A S)
               = open_typ_wrt_typ_rec 0 A (open_typ_wrt_typ_rec 0 `ᵈ SZ S) )
          by rewrite* open_typ_wrt_typ_twice;
                                    forwards*: H1 SZ ((SZ, ▫) :: Ψ1) Ψ2 HE;
                                    rewrite_env ( SZ ~ ▫ ++ (Ψ1 ++ Ψ2));
                                    eauto using d_mono_typ_weaken_head
      end) ]
      ].
Qed.


Lemma d_wf_typ_bound_typ : forall Ψ1 x Ψ2 A1 B1 B2,
  Ψ2 ++ x ~ dbind_typ B1 ++ Ψ1 ⊢ A1 ->
  Ψ1 ⊢ B2 ->
  Ψ2 ++ x ~ dbind_typ B2 ++ Ψ1 ⊢ A1.
Proof.
  intros.
  dependent induction H; eauto.
  - induction Ψ2; simpl. auto.
    + simpl in H. inversion H. inversion H1.
      eauto.
    + destruct a. destruct d.
      inversion H.
        dependent destruction H1. econstructor; eauto.
        apply dwf_typ_weakening_cons; auto.
      inversion H. inversion H1.
        apply dwf_typ_weakening_cons; auto.
      inversion H. inversion H1.
        apply dwf_typ_weakening_cons; auto.
  - induction Ψ2; simpl. auto.
    + simpl in H. inversion H. inversion H1.
      eauto.
    + destruct a. destruct d.
      inversion H.
        dependent destruction H1.
        apply dwf_typ_weakening_cons; auto.
      inversion H. inversion H1.
        eauto...
        apply dwf_typ_weakening_cons; auto.
      inversion H. inversion H1.
        apply dwf_typ_weakening_cons; auto.
  - eapply d_wf_typ__all with (L:=L); intros; inst_cofinites_with X.
    auto.
    rewrite_env ((X ~ ▫ ++ Ψ2) ++ x ~ dbind_typ B2 ++ Ψ1).
    eapply H1; simpl; eauto.
Qed.

Lemma d_wf_exp_weakening_head : forall (Ψ : denv) (X : atom) (b : dbind) (x : expvar),
    d_wf_exp Ψ (exp_var_f x) → d_wf_exp (X ~ b ++ Ψ) (exp_var_f x).
Proof.
  intros * H. inverts* H.
Qed.

Lemma d_wf_exp_bound_typ : forall Ψ1 x Ψ2 e A1 A2,
  d_wf_exp (Ψ2 ++ x ~ dbind_typ A1 ++ Ψ1) e ->
  Ψ1 ⊢ A2 ->
  d_wf_exp (Ψ2 ++ x ~ dbind_typ A2 ++ Ψ1) e
with d_wf_body_bound_typ : forall Ψ1 x Ψ2 e A1 A2,
  d_wf_body (Ψ2 ++ x ~ dbind_typ A1 ++ Ψ1) e ->
  Ψ1 ⊢ A2 ->
  d_wf_body (Ψ2 ++ x ~ dbind_typ A2 ++ Ψ1) e.
Proof with eauto using d_wf_typ_bound_typ.
  clear d_wf_exp_bound_typ. intros.
  dependent induction H; auto.
  - induction Ψ2; simpl. auto.
    + simpl in H. inversion H. dependent destruction H1.
      now eauto.
      forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto.
    + rewrite_env (a::(Ψ2 ++ x ~ dbind_typ A1 ++ Ψ1)) in H. destruct a.
      forwards[(?&Heq)|?]: binds_cons_1 H; try inverts Heq; subst; eauto.
      forwards*: IHΨ2. applys* d_wf_exp_weakening_head.
  - pick fresh Y and apply d_wf_exp__abs. applys* d_wf_typ_bound_typ.
    inst_cofinites_with Y.
    forwards: H1. rewrite_env ( (Y ~ dbind_typ T ++ Ψ2) ++ x ~ dbind_typ A1 ++ Ψ1)...
    all: eauto.
  - eauto.
  - pick fresh Y and apply d_wf_exp__tabs.
    inst_cofinites_with Y.
    rewrite_env ( (Y ~ ▫ ++ Ψ2) ++ x ~ dbind_typ A1 ++ Ψ1) in H.
    rewrite_env ( (Y ~ ▫ ++ Ψ2) ++ x ~ dbind_typ A2 ++ Ψ1).
    applys* d_wf_body_bound_typ H.
  - econstructor. eapply d_wf_typ_bound_typ; eauto.
    eauto.
  - econstructor. eapply d_wf_typ_bound_typ; eauto.
    eauto.

  - clear d_wf_body_bound_typ. intros.
    inverts H...
Qed.

Lemma d_wf_exp_bound_typ_head : forall Ψ1 x e A1 A2,
  d_wf_exp (x ~ dbind_typ A1 ++ Ψ1) e ->
  Ψ1 ⊢ A2 ->
  d_wf_exp (x ~ dbind_typ A2 ++ Ψ1) e.
Proof.
  intros.
  rewrite_env (nil ++ x ~ dbind_typ A2 ++ Ψ1).
  eapply d_wf_exp_bound_typ; eauto.
Qed.

Lemma d_wf_typ_strengthen_var : forall Ψ1 x Ψ2 A B,
  (Ψ2 ++ x ~ dbind_typ B ++ Ψ1) ⊢ A ->
  (Ψ2 ++ Ψ1) ⊢ A.
Proof with eauto.
  intros.
  dependent induction H; eauto.
  - forwards* [?|?]: binds_app_1 H.
    forwards[(?&Heq)|?]: binds_cons_1 H0; try inverts Heq; subst; eauto.
  - forwards* [?|?]: binds_app_1 H.
    forwards[(?&Heq)|?]: binds_cons_1 H0; try inverts Heq; subst; eauto.
  - pick fresh Y and apply d_wf_typ__all; inst_cofinites_with Y.
    now eauto.
    forwards: H1. rewrite_env ((Y ~ ▫ ++ Ψ2) ++ x ~ dbind_typ B ++ Ψ1)...
    rewrite_env ((Y ~ ▫ ++ Ψ2)++ Ψ1)...
Qed.
