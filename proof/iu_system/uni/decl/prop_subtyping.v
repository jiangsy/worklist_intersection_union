Require Import Coq.Program.Equality.
Require Import Lia.
Require Import LibTactics.

Require Import uni.notations.
Require Import uni.prop_basic.
Require Import ln_utils.

Hint Constructors d_sub : sub.

Lemma dsub_refl' : forall E T,
  ⊢ E -> E ⊢ₛ T -> E ⊢ T <: T.
Proof with auto with sub.
  intros; dependent induction H0; eauto...
  eapply d_sub__all with (L:=L `union` dom E); eauto.
Qed.


Lemma dsub_refl : forall E T,
  ⊢ E -> E ⊢ T -> E ⊢ T <: T.
Proof.
  intros.
  apply dsub_refl'. auto.
  apply dwf_typ_dwf_typ_s.
  auto.
Qed.


Lemma dsub_union_inversion : forall E S1 S2 T1,
  E ⊢ typ_union S1 S2 <: T1 ->
  E ⊢ S1 <: T1 /\ E ⊢ S2 <: T1.
Proof with auto with sub.
  intros.
  dependent induction H; auto...
  - inversion H0. split; econstructor; auto.
  - specialize (IHd_sub1 _ _ (eq_refl _)).
    specialize (IHd_sub2 _ _ (eq_refl _)).
    destruct IHd_sub1. destruct IHd_sub2.
    intuition.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
Qed.


Lemma dsub_intersection_inversion : forall E S1 T1 T2,
  E ⊢ S1 <: typ_intersection T1 T2 ->
  E ⊢ S1 <: T1 /\ E ⊢ S1 <: T2.
Proof with auto with sub.
  intros.
  dependent induction H; auto...
  - inversion H0. split; econstructor; auto.
  - inversion H0.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
  - specialize (IHd_sub1 _ _ (eq_refl _)).
    specialize (IHd_sub2 _ _ (eq_refl _)).
    inversion IHd_sub1.
    destruct IHd_sub2.
    intuition.
Qed.


Theorem dsub_unit_all_false: forall E T,
  E ⊢ typ_all T ->
  E ⊢ typ_unit <: typ_all T ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem dsub_top_all_false: forall E T,
  E ⊢ typ_all T ->
  E ⊢ typ_top <: typ_all T ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem dsub_top_fv_false: forall E X T,
  ds_in X T ->
  E ⊢ typ_top <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.

Theorem dsub_unit_fv_false: forall E X T,
  ds_in X T ->
  E ⊢ typ_unit <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.


Hint Resolve d_wf_typ_lc_typ : subtyping.
Hint Resolve dsub_refl : subtyping.
Hint Resolve d_wft_typ_subst : subtyping.
Hint Resolve d_wft_typ_subst_stvar : subtyping.
Hint Resolve d_wf_env_subst_tvar_typ : subtyping.

Inductive d_sub_tvar_open_inv : typvar -> typ -> Prop :=
| d__stoi__refl : forall X, d_sub_tvar_open_inv X (typ_var_f X)
| d__stoi__union : forall X T1 T2,
    d_sub_tvar_open_inv X T1 ->
    d_sub_tvar_open_inv X T2 ->
    d_sub_tvar_open_inv X (typ_union T1 T2)
| d__stoi__intersection1 : forall X T1 T2,
    d_sub_tvar_open_inv X T1 ->
    d_sub_tvar_open_inv X (typ_intersection T1 T2)
| d__stoi__intersection2 : forall X T1 T2,
    d_sub_tvar_open_inv X T2 ->
    d_sub_tvar_open_inv X (typ_intersection T1 T2).

Lemma d_sub_tvar_open_inv_subst : forall X1 X2 S1 T1,
  d_sub_tvar_open_inv X1 T1 ->
  X1 <> X2 ->
  d_sub_tvar_open_inv X1 ({S1 /ᵗ X2} T1).
Proof.
  intros. induction H.
  - simpl. destruct (X == X2).
    + subst. contradiction.
    + constructor.
  - simpl. econstructor; eauto.
  - simpl. econstructor; eauto.
  - simpl. eapply d__stoi__intersection2. eauto.
Qed.


Lemma d_sub_tvar_open_inv_subst_var : forall X1 X2 T1,
  d_sub_tvar_open_inv X1 T1 ->
  d_sub_tvar_open_inv X2 ({`ᵈ X2 /ᵗ X1} T1).
Proof.
  intros. induction H.
  - simpl. destruct (X == X).
    + constructor.
    + contradiction.
  - simpl. econstructor; eauto.
  - simpl. econstructor; eauto.
  - simpl. eapply d__stoi__intersection2. eauto.
Qed.


Inductive d_sub_tvar_inv : typ -> Prop :=
| d__sti__all : forall L T,
    (forall X, X `notin` L -> d_sub_tvar_open_inv X (T ^ᵈ X)) ->
    d_sub_tvar_inv (typ_all T).



Fixpoint d_typ_order (T : typ) : nat :=
  match T with
  | typ_all T1 => S ( d_typ_order T1 )
  | typ_arrow T1 T2 => d_typ_order T1 + d_typ_order T2
  | typ_intersection T1 T2 => d_typ_order T1 + d_typ_order T2
  | typ_union T1 T2 => d_typ_order T1 + d_typ_order T2
  | _ => 0
  end.

Fixpoint d_typ_size (T : typ) :=
  match T with
  | typ_intersection T1 T2 => 1 + d_typ_size T1 + d_typ_size T2
  | typ_union T1 T2 => 1 + d_typ_size T1 + d_typ_size T2
  | _ => 0
  end.


Lemma d_mono_type_order_0 : forall E T,
  d_mono_typ E T -> d_typ_order T = 0.
Proof.
  intros; induction H; simpl; auto.
  - rewrite IHd_mono_typ1. rewrite IHd_mono_typ2. auto.
  - rewrite IHd_mono_typ1. rewrite IHd_mono_typ2. auto.
  - rewrite IHd_mono_typ1. rewrite IHd_mono_typ2. auto.
Qed.

Lemma d_open_rec_mono_same_order : forall E T1 T2 n,
  d_mono_typ E T2 ->
  d_typ_order (open_typ_wrt_typ_rec n T2 T1) = d_typ_order T1.
Proof.
  induction T1; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; auto. eapply d_mono_type_order_0; eauto.
    + auto.
Qed.

Lemma d_open_rec_tvar_same_order : forall T1 X n,
  d_typ_order (open_typ_wrt_typ_rec n (typ_var_f X) T1) = d_typ_order T1.
Proof.
  induction T1; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; auto.
    + auto.
Qed.

Lemma d_open_mono_same_order : forall E A1 T1,
  d_mono_typ E T1 ->
  d_typ_order (A1 ^^ᵈ T1) = d_typ_order A1.
Proof.
  intros. unfold open_typ_wrt_typ. eapply d_open_rec_mono_same_order; eauto.
Qed.


Lemma d_open_svar_same_order : forall T1 X,
  d_typ_order (T1 ^ᵈ X) = d_typ_order T1.
Proof.
  intros. unfold open_typ_wrt_typ. apply d_open_rec_tvar_same_order; auto.
Qed.


Theorem d_sub_tvar_inv_nested_all_false: forall L1 L2 L3 T1 S1,
  (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_typ_wrt_typ_rec 1 S1 T1 ^ᵈ X)) ->
  (forall X : atom, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 `ᵈ X T1))) ->
  (forall X : atom, X `notin` L3 -> ds_in X (open_typ_wrt_typ_rec 1 S1 T1 ^ᵈ X)) ->
  lc_typ S1 ->
  False.
Proof.
  intros. induction T1; simpl in *.
  - inst_cofinites_by L3. inversion H1.
  - inst_cofinites_by L3. inversion H1.
  - inst_cofinites_by L3. inversion H1.
  - destruct ( lt_eq_lt_dec n 1 ).
    + destruct s. simpl in *. destruct n; simpl in *.
      * inst_cofinites_by L2. dependent destruction H0.
        inst_cofinites_by (L `union` singleton X).
        dependent destruction H0.
        apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
      * inst_cofinites_by L3.
        inversion H1.
      * inst_cofinites_by (L3 `union` ftvar_in_typ S1).
        rewrite open_typ_wrt_typ_lc_typ in H1; auto.
        apply sin_in in H1. apply notin_union_2 in Fr. contradiction.
    + destruct (n - 1).
      * unfold open_typ_wrt_typ in *. simpl in *.
        inst_cofinites_by L2. dependent destruction H0.
        inst_cofinites_by (L `union` singleton X).
        dependent destruction H0.
        apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
      * unfold open_typ_wrt_typ in *. simpl in *.
        inst_cofinites_by L3. inversion H1.
  - inst_cofinites_by (L3 `union` singleton X).
    dependent destruction H1. apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
  - inst_cofinites_by L1. inversion H.
  - inst_cofinites_by L1. inversion H.
  - assert (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X)). {
      intros. inst_cofinites_with X. inversion H; auto.
    }
    assert (forall X : atom, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 `ᵈ X T1_1))).
    { intros. inst_cofinites_with X. dependent destruction H0.
      eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
      inversion H0. auto.
    }
    assert  (forall X : atom, X `notin` L3 -> ds_in X (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X)).
    { intros. inst_cofinites_with X. inversion H1; auto.
    }
    auto.
  - assert ((forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X)) \/
            (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ X))).
    {
      intros.
      inst_cofinites_by (L1 `union` ftvar_in_typ (open_typ_wrt_typ_rec 1 S1 T1_1) `union`
                                    ftvar_in_typ (open_typ_wrt_typ_rec 1 S1 T1_2)).
      dependent destruction H.
      - left. intros. inst_cofinites_with X.
        assert (d_sub_tvar_open_inv x (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ x)) by auto.
        replace (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X) with ({`ᵈ X /ᵗ x}(open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ x)).
        now apply d_sub_tvar_open_inv_subst_var.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
        rewrite (subst_tvar_in_typ_fresh_eq); auto. simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X x x); auto. contradiction.
      - right. intros. inst_cofinites_with X.
        assert (d_sub_tvar_open_inv x (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ x)) by auto.
        replace (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ X) with ({`ᵈ X /ᵗ x}(open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ x)).
        now apply d_sub_tvar_open_inv_subst_var.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
        rewrite (subst_tvar_in_typ_fresh_eq); auto. simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X x x); auto. contradiction.
    }
    inversion H3.
    + assert (forall X : atom, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 `ᵈ X T1_1))).
      { intros. inst_cofinites_with X. dependent destruction H0.
        eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
        inversion H0. auto.
      }
      assert  (forall X, X `notin` L3 -> ds_in X (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X)).
      { intros. inst_cofinites_with X. inversion H1; auto.
      }
      auto.
    + assert (forall X, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 `ᵈ X T1_2))).
      { intros. inst_cofinites_with X. dependent destruction H0.
        eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
        inversion H0. auto.
      }
      assert  (forall X, X `notin` L3 -> ds_in X (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ X)).
      { intros. inst_cofinites_with X. inversion H1; auto.
      }
      auto.
Qed.


Theorem d_sub_tvar_ind_open_inv_complete: forall n1 n2 E S1 T1 X L,
    d_typ_order (T1 ^^ᵈ S1) < n1 ->
    d_typ_size (T1 ^^ᵈ S1) < n2 ->
    E ⊢ T1 ^^ᵈ S1 <: `ᵈ X ->
    (forall X, X `notin` L -> ds_in X (T1 ^ᵈ X)) ->
    d_mono_typ E S1 ->
    d_sub_tvar_inv (typ_all T1).
Proof.
    intro n1. induction n1.
    - intros. inversion H.
    - intros n2. induction n2.
      + intros. inversion H0.
      + intros. dependent destruction H1; rename x into Heq.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- inst_cofinites_by L. inversion Hdsin.
          -- destruct n. simpl in *.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. subst. inversion Hmono.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. inversion Heq.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. inversion Heq.
          -- inst_cofinites_by (L `union` (singleton X0)).
            unfold open_typ_wrt_typ in Hdsin. simpl in Hdsin. dependent destruction Hdsin.
            apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. inversion Heq.
          -- exfalso.
             dependent destruction Heq.
             eapply IHn1 in H6; eauto. inversion H6. auto.
             eapply d_sub_tvar_inv_nested_all_false with (L1:=L `union` L0 `union` L1); eauto...
             erewrite d_open_mono_same_order; eauto... lia.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. inversion Heq.
          -- dependent destruction Heq. apply IHn2 with (L:=L) in H1.
             dependent destruction H1.
             eapply d__sti__all with (L:=L `union` L0); auto.
             intros. inst_cofinites_with X0. eapply d__stoi__intersection1; eauto.
             ++ unfold open_typ_wrt_typ. lia.
             ++ unfold open_typ_wrt_typ. lia.
             ++ intros. inst_cofinites_with X0.  dependent destruction Hdsin. auto.
             ++ auto.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. inversion Heq.
          -- dependent destruction Heq. apply IHn2 with (L:=L) in H1.
             dependent destruction H1.
             eapply d__sti__all with (L:=L `union` L0); auto.
             intros. inst_cofinites_with X0. eapply d__stoi__intersection2; eauto.
             ++ unfold open_typ_wrt_typ. lia.
             ++ unfold open_typ_wrt_typ. lia.
             ++ intros. inst_cofinites_with X0.  dependent destruction Hdsin. auto.
             ++ auto.
        * rename H2 into Hdsin. rename H3 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_typ_wrt_typ in Heq. simpl in Heq. inversion Heq.
          -- dependent destruction Heq.
             eapply IHn2 with (L:=L) in H1_; eauto...
             eapply IHn2 with (L:=L) in H1_0; eauto...
             ++ dependent destruction H1_.
                dependent destruction H1_0.
                eapply d__sti__all with (L:=L `union` L0 `union` L1). intros.
                replace (typ_union T1_1 T1_2 ^ᵈ X0) with (typ_union (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) by auto.
                econstructor; eauto.
              ++ unfold open_typ_wrt_typ. lia.
              ++ unfold open_typ_wrt_typ. lia.
              ++ intros. inst_cofinites_with X0. dependent destruction Hdsin; auto.
              ++ unfold open_typ_wrt_typ. lia.
              ++ unfold open_typ_wrt_typ. lia.
              ++ intros. inst_cofinites_with X0. dependent destruction Hdsin; auto.
Qed.


Lemma d_sub_tvar_inv_subst: forall T1 X S1,
    d_sub_tvar_inv T1 -> lc_typ S1 -> d_sub_tvar_inv ({S1 /ᵗ X} T1).
Proof.
  intros. dependent destruction H.
  simpl.
  eapply d__sti__all with (L:=L `union` singleton X).
  intros.
  rewrite typ_subst_open_comm.
  - apply d_sub_tvar_open_inv_subst; auto.
  - auto.
  - simpl. apply notin_union_2 in H1.
    apply notin_singleton_1' in H1.
    apply notin_singleton. auto.
Qed.


Inductive d_ord_mono : denv -> typ -> Prop :=
| d_ordmono__tvar : forall E X, 
    d_mono_typ E (typ_var_f X) ->
    d_ord_mono E (typ_var_f X)
| d_ordmono__unit : forall E, d_ord_mono E typ_unit
| d_ordmono__arr : forall E T1 T2,
    d_mono_typ E T1 ->
    d_mono_typ E T2 ->
    d_ord_mono E (typ_arrow T1 T2)
.

Lemma d_ord_mono_neq_intersection: forall E T1,
  d_ord_mono E T1 ->
  neq_intersection T1.
Proof.
  intros. induction H; auto.
  econstructor; eapply d_mono_typ_lc; eauto.
Qed.

Lemma d_ord_mono_neq_union: forall E T1,
  d_ord_mono E T1 ->
  neq_union T1.
Proof.
  intros. induction H; auto.
  econstructor; eapply d_mono_typ_lc; eauto.
Qed.

Inductive d_mono_ordiu : denv -> typ -> Prop :=
| d_monoord__base : forall E T1,
    d_ord_mono E T1 ->
    d_mono_ordiu E T1
| d_monoord__union : forall E T1 T2,
    d_mono_ordiu E T1 ->
    d_mono_ordiu E T2 ->
    d_mono_ordiu E (typ_union T1 T2)
| d_monoord__inter : forall E T1 T2,
    d_mono_ordiu E T1 ->
    d_mono_ordiu E T2 ->
    d_mono_ordiu E (typ_intersection T1 T2).


Lemma d_mono_ordiu_complete : forall E T1,
  d_mono_typ E T1 -> d_mono_ordiu E T1.
Proof.
  intros. induction H; try solve [constructor; constructor].
  - econstructor. econstructor. eapply d_mono_typ__tvar; auto.
  - apply d_monoord__base. apply d_ordmono__arr; auto.
  - apply d_monoord__inter; auto.
  - apply d_monoord__union; auto.
Qed.


Lemma d_ord_mono_sound: forall E A1,
  d_ord_mono E A1 -> d_mono_typ E A1.
Proof.
  intros. induction H; auto.
Qed.

Lemma d_mono_ordiu_sound : forall E A1,
  d_mono_ordiu E A1 -> d_mono_typ E A1.
Proof.
  intros. induction H; auto.
  - apply d_ord_mono_sound. auto.
Qed.


Theorem d_sub_tvar_ind_open_subst : forall E F X A1 B1,
  ⊢ F ++ (X ~ dbind_tvar_empty) ++ E ->
  d_sub_tvar_open_inv X A1 ->
  d_mono_typ E B1 ->
  (X ~ dbind_tvar_empty) ++ E ⊢ A1 ->
  E ⊢ B1 ->
  map (subst_tvar_in_dbind B1 X) F ++ E ⊢ ({B1 /ᵗ X} A1) <: B1.
Proof with auto with subtyping.
  intros * Hwfenv H. induction H; intros.
  - simpl. destruct (X == X).
    + apply dsub_refl; auto...
      replace B1 with ({B1 /ᵗ X} `ᵈ X) at 2.
      apply d_wft_typ_subst; auto.
      simpl. destruct (X == X); auto. contradiction.
    + contradiction.
  - simpl. dependent destruction H2. constructor; auto.
  - simpl. dependent destruction H1. constructor; auto.
    apply d_wft_typ_subst; auto.
    apply dwf_typ_weakening with (E3:=nil); auto.
  - simpl. dependent destruction H1. apply d_sub__intersection3; auto.
    apply d_wft_typ_subst; auto.
    apply dwf_typ_weakening with (E3:=nil); auto.
Qed.


(* Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end. *)
Hint Resolve dwf_typ_weakening : weakening.

Theorem d_sub_weakening: forall E F G S1 T1,
  G ++ E ⊢ S1 <: T1 ->
  ⊢ G ++ F ++ E ->
  G ++ F ++ E ⊢ S1 <: T1.
Proof with auto with subtyping weakening.
  intros E F G S1 T1 Hsub Hwf.
  dependent induction Hsub;
    try solve [simpl in *];
    try solve [eapply dwf_typ_weakening with (E2 := F) in H0; auto]; auto.
  - apply d_sub__all with (L :=  L `union` dom (G ++ F ++ E)); intros x Fr; inst_cofinites_with x; auto...
    eapply H2 with (E := E) (G := (x, ▪) :: G); simpl; auto.
    constructor; auto.
  - apply d_sub__alll with (T1 := T1) (L :=  L `union` dom (G ++ F ++ E)); auto...
    admit.
  - apply d_sub__intersection2; eauto...
  - apply d_sub__intersection3; auto...
  - apply d_sub__union1; auto...
  - apply d_sub__union2; auto...
Admitted.


Corollary d_sub_weakening_cons: forall E x b S1 T1,
  E ⊢ S1 <: T1 ->
  ⊢ x ~ b ++ E ->
  x ~ b ++ E ⊢ S1 <: T1.
Proof.
  intros.
  rewrite_env (nil ++ (x ~ b) ++ E).
  eapply d_sub_weakening; eauto.
Qed.

(* Theorem  d_sub_strenthening: forall E F G S1 T1,
  F ++ G ++ E ⊢ S1 <: T1 ->
  F ++ E ⊢ S1 ->
  F ++ E ⊢ T1 ->
  F ++ E ⊢ S1 <: T1.
Proof.
  introv HS HWS HWT.
  remember (F++G++E) as E'.
  induction HS.
  all: auto.
  - forwards~: IHHS1.
    inverts~ HWT. inverts~ HWS.
    forwards~: IHHS2.
    now inversion HWS.
    inverts~ HWS. inverts~ HWT.
  - admit.
  - forwards~: IHHS.
    inverts~ HWS. pick fresh y. applys dwft_subst y H8. solve_notin.
    (* wf for newly introduced mono type T2*)
    admit.
Admitted. *)


Theorem d_sub_tvar_ind_sub_all : forall E A1 B1,
  ⊢ E ->
  d_sub_tvar_inv (typ_all A1) ->
  E ⊢ typ_all A1 ->
  d_mono_typ E B1 ->
  E ⊢ B1 ->
  E ⊢ typ_all A1 <: B1.
Proof.
  intros * Hwfenv H Hwft Hmono Hwft2.
  specialize (d_mono_ordiu_complete _ _ Hmono). intros.
  induction H0.
  - dependent destruction H.
    dependent destruction Hwft.
    eapply d_sub__alll with (L:=L `union` L0) (T1:=T1).
    + eapply d_mono_typ_neq_all; eauto.
    + eapply d_ord_mono_neq_intersection; eauto.
    + eapply d_ord_mono_neq_union; eauto.
    + auto.
    + auto.
    + inst_cofinites_by (L `union` L0 `union` ftvar_in_typ A1 `union` dom E) using_name X.
      apply d_sub_tvar_ind_open_subst with (E:= E) (B1:=T1) (F:=nil) in H; auto.
      * rewrite typ_subst_open_var in H; eauto.
      * simpl. constructor; auto.
  - inversion Hmono. inversion Hwft2. auto.
  - inversion Hmono. inversion Hwft2. auto.
Qed.


Theorem  d_sub_subst_mono : forall E X F A1 B1 T1,
  ⊢ F ++ (X ~ dbind_tvar_empty) ++ E ->
  F ++ (X ~ dbind_tvar_empty) ++ E ⊢ A1 <: B1 ->
  E ⊢ T1 ->
  d_mono_typ E T1 ->
  map (subst_tvar_in_dbind T1 X) F ++ E ⊢ {T1 /ᵗ X} A1 <: {T1 /ᵗ X} B1.
Proof with eauto with subtyping.
  intros E X F A1 B1 T1 Hwfenv Hsub Hwft Hmono.
  dependent induction Hsub; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl; auto...
  - simpl. eapply d_sub__all with (L:=L `union` singleton X `union` dom E `union` dom F); intros X0 Hfr; inst_cofinites_with X.
    + rewrite typ_subst_open_comm; auto...
      admit.
    + rewrite typ_subst_open_comm; auto...
      admit.
    + inst_cofinites_with X0. repeat rewrite typ_subst_open_comm; eauto...
      replace (X0 ~ dbind_stvar_empty ++ map (subst_tvar_in_dbind T1 X) F ++ E) with
      (map (subst_tvar_in_dbind T1 X) (X0 ~ dbind_stvar_empty ++ F) ++ E) by auto.
      eapply H2; auto... simpl. constructor; eauto.
  - destruct B1.
    + eapply d_sub__alll with (L:=L `union` singleton X) (T1:={T1 /ᵗ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
        admit. admit. 
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T1:={T1 /ᵗ X} T0); eauto...
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
        admit. admit.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T1:={T1 /ᵗ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
        admit. admit.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]]. inversion HwftT.
    + simpl.
      apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]].
      apply d_sub_tvar_ind_sub_all.
      -- eapply d_wf_env_subst_tvar_typ; auto.
      -- replace (typ_all ({T1 /ᵗ X} A1)) with ({T1 /ᵗ X} (typ_all A1)) by auto.
         apply d_sub_tvar_inv_subst. eapply d_sub_tvar_ind_open_inv_complete; eauto.
         eapply d_wf_typ_lc_typ; eauto.
      -- replace (typ_all ({T1 /ᵗ X} A1)) with ({T1 /ᵗ X} (typ_all A1))  by auto.
         apply d_wft_typ_subst; auto.
         inst_cofinites_for d_wf_typ__all.
         ++ auto.
         ++ intros. eapply dwf_typ_open_inv with (X:=X1) (T1:=T0); auto.
            admit.
            rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
            simpl. rewrite (subst_tvar_in_typ_fresh_eq); auto.
            unfold eq_dec. destruct (EqDec_eq_of_X X1 X1); auto.
            ** apply dwf_typ_weakening_cons; auto.
            ** contradiction.
            ** admit.
      -- unfold eq_dec. destruct (EqDec_eq_of_X X0 X); auto.
         admit. admit.
      -- replace (if X0 == X then T1 else `ᵈ X0) with ( {T1 /ᵗ X} `ᵈ X0) by auto.
         apply d_wft_typ_subst; auto.
    + apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]]. inversion HwftT.
      eapply d_sub__alll with (L:=L `union` singleton X) (T1:={T1 /ᵗ X} T0); eauto...
      * admit.
      * admit.
      * admit.
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto. admit. admit.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T1:={T1 /ᵗ X} T0); eauto...
      * simpl. dependent destruction H.
      * simpl. dependent destruction H.
      * simpl. dependent destruction H.
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
        admit. admit.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + inversion H1.
    + inversion H0.
Admitted.


Hint Resolve d_wft_typ_subst_stvar : subtyping.
Hint Resolve d_wf_env_subst_stvar_typ : subtyping.
(* Hint Resolve d_subst_stv_lc_typ : lngen. *)

(* Lemma dneq_all_intersection_union_subst_stv : forall T1 T2 X,
  lc_typ T1 -> lc_typ T2 ->
  dneq_all T1 -> dneq_intersection T1 -> dneq_union T1 ->
  (dneq_all ({T2 /ᵗ X} T1) /\
   dneq_intersection ({T2 /ᵗ X} T1) /\
   dneq_union ({T2 /ᵗ X} T1)) \/ T1 = typ_svar X.
Proof with eauto with lngen.
  intros. destruct T1; simpl in *; auto...
  - destruct (X0 == X); subst; auto.
  - dependent destruction H. left. split.
    eauto with lngen...
    constructor; eauto with lngen...
  - inversion H1.
  - inversion H3.
  - inversion H2.
Qed. *)

Theorem d_sub_mono_stvar_false : forall E T1 X,
  X ~ ▪ ∈ E ->
  E ⊢ T1 <: typ_var_f X ->
  d_mono_typ E T1 ->
  False.
Proof.
  intros. 
  induction H1; dependent destruction H0; auto.
  - admit.
Admitted.



Theorem d_sub_open_mono_stvar_false: forall n1 n2 E A1 T1 X L,
    d_typ_order (A1 ^^ᵈ T1) < n1 ->
    d_typ_size (A1 ^^ᵈ T1) < n2 ->
    X ~ ▪ ∈ E ->
    E ⊢ A1 ^^ᵈ T1 <: typ_var_f X ->
    (forall X, X `notin` L -> ds_in X (A1 ^ᵈ X)) ->
    d_mono_typ E T1 ->
    False.
Proof.
  intro n1. induction n1.
  - intros. inversion H.
  - intros n2. induction n2.
    + intros. inversion H0.
    + intros. dependent destruction H2; rename x into Heq.
      * destruct A1; simpl in *; try solve [inversion Heq].
        -- inst_cofinites_by L using_name X. inversion H4.
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in *.
              subst. inversion H5.
           ++ unfold open_typ_wrt_typ in Heq. simpl in *.
              inversion Heq.
      * destruct A1; simpl in *; try solve [inversion Heq].
        -- destruct n.
          ++ unfold open_typ_wrt_typ in Heq. simpl in *.
            subst. dependent destruction H5. admit.
          ++ unfold open_typ_wrt_typ in Heq. simpl in *.
            inversion Heq.
        -- inst_cofinites_by (L `union` singleton X0) using_name X. inversion H4.
           admit.
      * destruct A1; simpl in *; try solve [inversion Heq].
        -- destruct n.
          ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H9.
          ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq.
           eapply IHn1; eauto. erewrite d_open_mono_same_order; eauto. lia.
      * destruct A1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H5.
              eapply d_sub_mono_stvar_false in H2; auto.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H4; auto.
      * destruct A1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H5.
              apply d_sub_mono_stvar_false in H2; auto.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H4; auto.
      * destruct A1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H4.
              apply d_sub_mono_stvar_false in H2_; auto.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H3; auto.
Admitted.

Theorem d_mono_notin_stvar : forall F E T X,
  F ++ (X ~ dbind_stvar_empty) ++ E ⊢ T -> d_mono_typ (F ++ (X ~ dbind_stvar_empty) ++ E) T ->
  X `notin` ftvar_in_typ T.
Proof.
  intros. dependent induction H0; simpl in *; auto.
  - admit.
  - dependent destruction H; auto... apply notin_union; eauto.
  - dependent destruction H; auto... apply notin_union; eauto.
  - dependent destruction H; auto... apply notin_union; eauto.
Admitted.

(* bookmark *)

Theorem d_sub_subst_stvar : forall E X F A1 B1 T1,
  F ++ (X ~ dbind_stvar_empty) ++ E ⊢ A1 <: B1 ->
  E ⊢ T1 ->
  map (subst_tvar_in_dbind T1 X) F ++ E ⊢ {T1 /ᵗ X} A1 <: {T1 /ᵗ X} B1.
Proof with subst; eauto using dwf_typ_weaken_head with subtyping.
  intros. dependent induction H; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl; auto...
  - simpl. inst_cofinites_for d_sub__all; intros X1 Hfr; inst_cofinites_with X1.
    + rewrite typ_subst_open_comm; auto...
      apply ftv_sin_typ_subst_inv; auto...
    + rewrite typ_subst_open_comm; auto...
      apply ftv_sin_typ_subst_inv; auto...
    + repeat rewrite typ_subst_open_comm; eauto...
      rewrite_env (map (subst_tvar_in_dbind T1 X) (X1 ~ ▪ ++ F) ++ E).
      eapply H2; auto...
  - simpl. destruct (dneq_all_intersection_union_subst_stv T1 T2 X) as [[? [? ?]] | ?]; eauto...
    + eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵗ X} T0); eauto...
      * intros. inst_cofinites_with X0. rewrite d_subst_stv_in_typ_open_comm; auto...
        apply fstv_sins_typ_subst_stv; auto...
      * apply d_wft_typ_subst_stvar; auto...
        destruct (d_sub_dwft _ _ _ H5) as [? [? ?]]. auto.
      * rewrite d_subst_stv_in_typ_fresh_eq; auto.
        eapply d_mono_notin_stvar with (F := F) (E := E); auto.
      * rewrite <- d_subst_stv_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub_open_mono_stvar_false in H5; eauto. contradiction.
  - simpl. apply d_sub_intersection2. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub_intersection3. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub_union1. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub_union2. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
Qed.


Inductive d_sub_size : denv -> typ -> typ -> nat -> Prop :=    (* defn d_sub *)
 | d_subs__top : forall (E:denv) (A1:typ) (n:nat),
     d_wf_env E ->
     d_wf_typ E A1 ->
     d_sub_size E A1 typ_top n
 | d_subs__bot : forall (E:denv) (B1:typ) (n:nat),
     d_wf_env E ->
     d_wf_typ E B1 ->
     d_sub_size E typ_bot B1 n
 | d_subs__unit : forall (E:denv) (n:nat),
     d_wf_env E ->
     d_sub_size E typ_unit typ_unit n
 | d_subs__tvar : forall (E:denv) (X:typvar) (n:nat),
     d_wf_env E ->
     d_wf_typ E (typ_var_f X) ->
     d_sub_size E (typ_var_f X) (typ_var_f X) n
 | d_subs__arrow : forall (E:denv) (A1 A2 B1 B2:typ) (n1 n2:nat),
     d_sub_size E B1 A1 n1 ->
     d_sub_size E A2 B2 n2 ->
     d_sub_size E (typ_arrow A1 A2) (typ_arrow B1 B2) (S (n1 + n2))
 | d_subs__all : forall (L:vars) (E:denv) (A1 B1:typ) (n:nat),
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ B1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ dbind_stvar_empty  ++  E )   ( open_typ_wrt_typ A1 (typ_var_f X) )   ( open_typ_wrt_typ B1 (typ_var_f X) )  n )  ->
      d_sub_size E (typ_all A1) (typ_all B1) (S n)
 | d_subs__alll : forall (L:vars) (E:denv) (A1 B1 T1:typ) (n:nat),
     neq_all B1 ->
     neq_intersection B1 ->
     neq_union B1 ->
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
     d_mono_typ E T1 ->
     d_sub_size E  (open_typ_wrt_typ  A1   T1 )  B1 n ->
     d_sub_size E (typ_all A1) B1 (S n)
 | d_subs__intersection1 : forall (E:denv) (A1 B1 B2:typ) (n1 n2:nat),
     d_sub_size E A1 B1 n1 ->
     d_sub_size E A1 B2 n2 ->
     d_sub_size E A1 (typ_intersection B1 B2) (S (n1 + n2))
 | d_subs__intersection2 : forall (E:denv) (A1 A2 B1:typ) (n:nat),
     d_sub_size E A1 B1 n ->
     d_wf_typ E A2 ->
     d_sub_size E (typ_intersection A1 A2) B1 (S n)
 | d_subs__intersection3 : forall (E:denv) (A1 A2 B1:typ) (n:nat),
     d_sub_size E A2 B1 n ->
     d_wf_typ E A1 ->
     d_sub_size E (typ_intersection A1 A2) B1 (S n)
 | d_subs__union1 : forall (E:denv) (A1 B1 B2:typ) (n:nat),
     d_sub_size E A1 B1 n ->
     d_wf_typ E B2 ->
     d_sub_size E A1 (typ_union B1 B2) (S n)
 | d_subs__union2 : forall (E:denv) (A1 B1 B2:typ) (n:nat),
     d_sub_size E A1 B2 n ->
     d_wf_typ E B1 ->
     d_sub_size E A1 (typ_union B1 B2) (S n)
 | d_subs__union3 : forall (E:denv) (A1 A2 B1:typ) (n1 n2:nat),
     d_sub_size E A1 B1 n1 ->
     d_sub_size E A2 B1 n2 ->
     d_sub_size E (typ_union A1 A2) B1 (S (n1 + n2)).


(* Inductive d_sub_size : denv -> typ -> typ -> nat -> Prop :=
 | d_subs__top : forall (E:denv) (S1:typ) (n:nat),
     dwf_env E ->
     dwf_typ E S1 ->
     d_sub_size E S1 typ_top n
 | d_subs__bot : forall (E:denv) (T:typ) (n:nat),
     dwf_env E ->
     dwf_typ E T ->
     d_sub_size E typ_bot T n
 | d_subs__unit : forall (E:denv) (n:nat),
     dwf_env E ->
     d_sub_size E typ_unit typ_unit n
 | d_subs__tvar : forall (E:denv) (X:typvar) (n:nat),
     dwf_env E ->
     dwf_typ E (typ_var_f X) ->
     d_sub_size E (typ_var_f X) (typ_var_f X) n
 | d_subs__stvar : forall (E:denv) (X:stypvar) (n:nat),
     dwf_env E ->
     dwf_typ E (typ_svar X) ->
     d_sub_size E (typ_svar X) (typ_svar X) n
 | d_subs__arrow : forall (E:denv) (S1 S2 T1 T2:typ) (n1 n2:nat),
     d_sub_size E T1 S1 n1 ->
     d_sub_size E S2 T2 n2 ->
     d_sub_size E (typ_arrow S1 S2) (typ_arrow T1 T2) (S (n1 + n2))
 | d_subs__all : forall (L:vars) (E:denv) (S1 T1:typ) (n:nat),
     ( forall X , X \notin L -> ds_in_s X  (open_typ_wrt_typ  S1   (typ_svar X) ) ) ->
     ( forall X , X \notin L -> ds_in_s X  (open_typ_wrt_typ  T1   (typ_svar X) ) ) ->
     ( forall X , X \notin L -> d_sub_size  ( X ~ dbind_stvar_empty  ++  E )   (open_typ_wrt_typ  S1   (typ_svar X) )   (open_typ_wrt_typ  T1  (typ_svar X) ) n) ->
     d_sub_size E (typ_all S1) (typ_all T1) (S n)
 | d_subs__alll : forall (L:vars) (E:denv) (S1 T1 T2:typ) (n:nat),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 ->
     ( forall X , X \notin L -> ds_in X  (open_typ_wrt_typ  S1   (typ_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     d_sub_size E  (open_typ_wrt_typ  S1   T2 )  T1 n ->
     d_sub_size E (typ_all S1) T1 (S n)
 | d_subs__intersection1 : forall (E:denv) (S1 T1 T2:typ) (n1 n2:nat),
     d_sub_size E S1 T1 n1 ->
     d_sub_size E S1 T2 n2 ->
     d_sub_size E S1 (typ_intersection T1 T2) (S (n1 + n2))
 | d_subs__intersection2 : forall (E:denv) (S1 S2 T:typ) (n:nat),
     d_sub_size E S1 T n ->
     dwf_typ E S2 ->
     d_sub_size E (typ_intersection S1 S2) T (S n)
 | d_subs__intersection3 : forall (E:denv) (S1 S2 T:typ) (n:nat),
     d_sub_size E S2 T n ->
     dwf_typ E S1 ->
     d_sub_size E (typ_intersection S1 S2) T (S n)
 | d_subs__union1 : forall (E:denv) (S1 T1 T2:typ) (n:nat),
     d_sub_size E S1 T1 n ->
     dwf_typ E T2 ->
     d_sub_size E S1 (typ_union T1 T2) (S n)
 | d_subs__union2 : forall (E:denv) (S1 T1 T2:typ) (n:nat),
     d_sub_size E S1 T2 n ->
     dwf_typ E T1 ->
     d_sub_size E S1 (typ_union T1 T2) (S n)
 | d_subs__union3 : forall (E:denv) (S1 S2 T:typ) (n1 n2:nat),
     d_sub_size E S1 T n1 ->
     d_sub_size E S2 T n2 ->
     d_sub_size E (typ_union S1 S2) T (S (n1 + n2)). *)

Notation "E ⊢ S1 <: T1 | n" :=
  (d_sub_size E S1 T1 n)
    (at level 65, S1 at next level, T1 at next level, no associativity) : type_scope.

Theorem d_sub_size_sound : forall E A1 B1 n,
    E ⊢ A1 <: B1 | n -> E ⊢ A1 <: B1.
Proof.
  intros. induction H; eauto.
Qed.

Hint Constructors d_sub_size : sub.


Lemma d_sub_size_rename_stvar : forall E F X Y A1 B1 n,
    F ++ X ~ ▪ ++ E ⊢ A1 <: B1 | n ->
      Y ∉ (dom E `union` dom F) ->
      (map (subst_tvar_in_dbind (typ_var_f Y) X) F) ++ Y ~ ▪ ++ E ⊢
        {typ_var_f Y /ᵗ X} A1 <: {typ_var_f Y /ᵗ X} B1 | n.
Proof with (simpl in *; eauto using d_wf_env_subst_tvar_typ with sub).
  intros * HS HN.
  case_eq (Y == X); intros.
  1: { subst. rewrite* subst_same_tvar_map_id.
       repeat rewrite* subst_same_tvar_typ_id. } clear H.

  gen Y.
  inductions HS; intros...
  - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((F ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ E).
    applys d_wf_env_weaken_stvar.
    rewrite_env (F ++ X ~ ▪ ++ E)...
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((F ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ E).
    applys d_wf_env_weaken_stvar.
    rewrite_env (F ++ X ~ ▪ ++ E)...
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((F ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ E).
    applys d_wf_env_weaken_stvar.
    rewrite_env (F ++ X ~ ▪ ++ E)...
    solve_notin.
  (* - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((F ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ E).
    applys d_wf_env_weaken_stvar.
    rewrite_env (F ++ X ~ ▪ ++ E)...
    solve_notin. inverts* H0.
    forwards* [?|?]: binds_app_1 H3.
    2: { forwards* [(?&?)|?]: binds_cons_1 H0. try solve_by_invert. }
    forwards* : binds_map_2 (d_subst_stv_in_binding (typ_svar Y) X) H0. *)
  - case_if; subst...
    + econstructor.
      applys* d_wf_env_rename_stvar...
      forwards: d_wf_typ_rename_stvar H0...
    + econstructor.
      applys* d_wf_env_rename_stvar...
      forwards: d_wf_typ_rename_stvar Y H0...
      case_if in H1...
  - pick fresh SZ and apply d_subs__all. inst_cofinites_with SZ.
    + rewrite typ_subst_open_comm...
      applys~ ftv_sin_typ_subst_inv.
    + rewrite typ_subst_open_comm...
      applys~ ftv_sin_typ_subst_inv.
    + forwards~: H2 SZ E ((SZ, ▪) :: F)...
      repeat rewrite typ_subst_open_comm...
  - admit.
  (* - pick fresh SZ and apply d_subs__alll. 6: apply HS. all: auto...
    + rewrite d_subst_stv_in_typ_open_comm...
      applys fstv_sins_typ_subst_stv...
    + replace T2 with ({typ_svar Y /ᵗ X} T2)...
      forwards: d_wf_typ_rename_stvar Y H3...
    + forwards: IHHS...
      rewrite d_subst_stv_in_typ_open_comm...
      applys* d_mono_notin_stvar. *)
  - applys d_subs__intersection2; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__intersection3; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__union1; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__union2; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
    Unshelve. all: eauto. 
Admitted.

Corollary d_sub_size_rename : forall n X Y D E A B,
    X `notin`  (ftvar_in_typ A `union` ftvar_in_typ B) ->
    Y `notin` ((dom D) `union` (dom E)) ->
    D ++ X ~ ▪ ++ E ⊢ A ^^ᵈ typ_var_f X <: B ^^ᵈ typ_var_f X | n ->
    map (subst_tvar_in_dbind (typ_var_f Y) X) D ++ Y ~ ▪ ++ E ⊢ A ^^ᵈ typ_var_f Y <: B ^^ᵈ typ_var_f Y | n.
Proof with eauto.
  intros.
  forwards: d_sub_size_rename_stvar Y H1. solve_notin.
  rewrite 2 subst_tvar_in_typ_open_typ_wrt_typ in H2...
  simpl in H2. case_if.
  rewrite 2 subst_tvar_in_typ_fresh_eq in H2...
Qed.

Lemma d_sub_size_complete : forall E T1 T2,
  E ⊢ T1 <: T2 -> exists n, E ⊢ T1 <: T2 | n.
Proof with eauto with sub.
  intros. induction H; eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
  - pick fresh X.
    destruct (H2 X) as [n]. solve_notin.
    exists (S n).
    eapply d_subs__all with (L:=L `union` fstv_in_typ S1 `union` fstv_in_typ S1 `union` (dom E)); intros; eauto.
    + rewrite_env (nil ++ X ~ ▪ ++ E). rewrite_env (nil ++ X ~ ▪ ++ E) in H3.
      applys d_sub_size_rename H3; solve_notin.
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
  eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
    Unshelve. all: econstructor.
Qed.

Hint Constructors d_sub_size : trans.


Lemma nat_suc: forall n n1, n >= S n1 ->
  exists n1', n = S n1' /\ n1' >= n1.
Proof.
  intros. induction H.
  - exists n1. split; lia.
  - destruct IHle as [n1' [n2' Hn1n2]].
    exists (S n1'). split; lia.
Qed.

Lemma nat_split: forall n n1 n2, n >= S (n1 + n2) ->
  exists n1' n2', n = S (n1' + n2') /\ n1' >= n1 /\ n2' >= n2.
Proof.
  intros. induction H.
  - exists n1, n2. split; lia.
  - destruct IHle as [n1' [n2' Hn1n2]].
    exists (S n1'), n2'. split; lia.
Qed.


Lemma d_sub_size_more: forall E S1 T1 n,
  E ⊢ S1 <: T1 | n -> forall n', n' >= n -> E ⊢ S1 <: T1 | n'.
Proof with auto with trans.
  intros E S1 T1 n H.
  dependent induction H; intros; auto...
  - apply nat_split in H1.
    destruct H1 as [n1' [n2' [Heq [Hgtn1 Hgtn2]]]].
    rewrite Heq. eauto...
  - apply nat_suc in H3.
    destruct H3 as [n1' [Heq Hgtn1]].
    rewrite Heq. econstructor; eauto...
  - apply nat_suc in H6.
    destruct H6 as [n1' [Heq Hgtn1]].
    rewrite Heq. econstructor; eauto...
  - apply nat_split in H1.
    destruct H1 as [n1' [n2' [Heq [Hgtn1 Hgtn2]]]].
    rewrite Heq. eauto...
  - apply nat_suc in H1.
    destruct H1 as [n1' [Heq Hgtn1]].
    rewrite Heq. eauto...
  - apply nat_suc in H1.
    destruct H1 as [n1' [Heq Hgtn1]].
    rewrite Heq. eauto...
  - apply nat_suc in H1.
    destruct H1 as [n1' [Heq Hgtn1]].
    rewrite Heq. eauto...
  - apply nat_suc in H1.
    destruct H1 as [n1' [Heq Hgtn1]].
    rewrite Heq. eauto...
  - apply nat_split in H1.
    destruct H1 as [n1' [n2' [Heq [Hgtn1 Hgtn2]]]].
    rewrite Heq. eauto...
Qed.


Hint Constructors d_sub : trans.
Hint Extern 1 (?x < ?y) => lia : trans.
Hint Extern 1 (?x <= ?y) => lia : trans.
Hint Extern 1 (?x >= ?y) => lia : trans.
Hint Extern 1 (?x > ?y) => lia : trans.


Lemma d_sub_size_union_inv: forall E S1 S2 T1 n,
  E ⊢ (typ_union S1 S2) <: T1 | n -> E ⊢ S1 <: T1 | n /\ E ⊢ S2 <: T1 | n.
Proof with auto with trans.
  intros.
  dependent induction H.
  - inversion H0. split; auto...
  - specialize (IHd_sub_size1 S1 S2 (eq_refl _)).
    specialize (IHd_sub_size2 S1 S2 (eq_refl _)).
    split; constructor; intuition.
  - specialize (IHd_sub_size S1 S2 (eq_refl _)).
    split; apply d_subs__union1; intuition.
  - specialize (IHd_sub_size S1 S2 (eq_refl _)).
    split; apply d_subs__union2; intuition.
  - split.
    eapply d_sub_size_more; eauto. lia.
    eapply d_sub_size_more; eauto. lia.
Qed.



Theorem d_sub_size_subst_stvar : forall E F X S1 T1 T2 n,
  F ++ (X ~ dbind_stvar_empty) ++ E ⊢ S1 <: T1 | n ->
  E ⊢ T2 ->
  exists n', map (d_subst_stv_in_binding T2 X) F ++ E ⊢ {T2 /ᵗ X} S1 <: {T2 /ᵗ X} T1 | n'.
Proof.
  intros.
  apply d_sub_size_sound in H.
  apply d_sub_subst_stvar with (T2:=T2) in H; auto.
  apply d_sub_size_complete in H. auto.
Qed.

Inductive d_ord : typ -> Prop :=
| d_ord__tvar : forall X, d_ord (typ_var_f X)
| d_ord__stvar : forall X, d_ord (typ_svar X)
| d_ord__bot : d_ord typ_bot
| d_ord__top : d_ord typ_top
| d_ord__unit : d_ord typ_unit
| d_ord__arr : forall T1 T2,
    d_ord (typ_arrow T1 T2)
| d_ord__all : forall T,
    d_ord (typ_all T)
.

Inductive d_wft_ord : typ -> Prop :=
| d_wftord__base : forall T, d_ord T -> d_wft_ord T
| d_wftord__intersection: forall T1 T2,
    d_wft_ord T1 ->
    d_wft_ord T2 ->
    d_wft_ord (typ_intersection T1 T2)
| d_wftord__union: forall T1 T2,
    d_wft_ord T1 ->
    d_wft_ord T2 ->
    d_wft_ord (typ_union T1 T2)
.

Hint Constructors d_ord : wf.
Hint Constructors d_wft_ord : wf.

Lemma d_wft_ord_complete: forall E T,
  E ⊢ T -> d_wft_ord T.
Proof with auto with wf.
  intros. induction H; eauto...
Qed.

Theorem d_sub_mono_bot_false : forall E T1,
  dmono_typ T1 ->
  E ⊢ T1 <: typ_bot ->
  False.
Proof.
  intros. induction H; try solve [(dependent destruction H0); auto].
Qed.



Theorem d_sub_open_mono_bot_false: forall n1 n2 E S1 T1 L,
    d_typ_order (T1 ^^ᵈ S1) < n1 ->
    d_typ_size (T1 ^^ᵈ S1) < n2 ->
    E ⊢ T1 ^^ᵈ S1 <: typ_bot ->
    (forall X, X `notin` L -> ds_in X (T1 ^ᵈ X)) ->
    dmono_typ S1 ->
    False.
Proof.
  intro n1. induction n1.
  - intros. inversion H.
  - intros n2. induction n2.
    + intros. inversion H0.
    + intros. dependent destruction H1; rename x into Heq.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- inst_cofinites_by L. inversion H3.
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H4.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
      * destruct T1; simpl in *; try solve [ inversion Heq].
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H9.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
        -- inversion Heq. subst. eapply IHn1; eauto.
           rewrite d_open_mono_same_order; auto. lia.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H4.
              eapply d_sub_mono_bot_false with (T1:=S0); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H4.
              eapply d_sub_mono_bot_false with (T1:=S2); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
              eapply d_sub_mono_bot_false with (T1:=S0); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H2; auto.
Qed.


Lemma d_sub_dwft_sized : forall E T1 T2 n,
    E ⊢ T1 <: T2 | n -> ⊢ E /\ E ⊢ T1 /\ E ⊢ T2.
Proof.
  intros. applys d_sub_dwft. applys* d_sub_size_sound.
Qed.

Corollary d_sub_dwft_sized_0 : forall E T1 T2 n,
    E ⊢ T1 <: T2 | n -> ⊢ E.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

Corollary d_sub_dwft_sized_1 : forall E T1 T2 n,
    E ⊢ T1 <: T2 | n -> E ⊢ T1.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

Corollary d_sub_dwft_sized_2 : forall E T1 T2 n,
    E ⊢ T1 <: T2 | n -> E ⊢ T2.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

#[local] Hint Resolve d_sub_dwft_sized_0 d_sub_dwft_sized_1 d_sub_dwft_sized_2 : core.

Ltac solve_trans_forall_B_intersection_impl T1 T2:=
  match goal with
   | H1 : ?E ⊢ ?T <: T1 | ?n1 |- _ =>
      match goal with
      | H2 : ?E ⊢ ?T <: T2 | ?n2 |- _ =>
        apply d_sub_size_more with (n':=S(n1+n2)) in H1; auto with trans;
        apply d_sub_size_more with (n':=S(n1+n2)) in H2; auto with trans
      end
   end.

Ltac solve_trans_forall_B_union_impl T1 T2:=
  match goal with
    | H1 : ?E ⊢ ?T <: T1 | ?n1 |- _ =>
      apply d_sub_size_more with (n':=S n1) in H1; auto with trans
    | H2 : ?E ⊢ ?T <: T2 | ?n1 |- _ =>
      apply d_sub_size_more with (n':=S n1) in H2; auto with trans
  end.

Ltac solve_trans_forall_B_iu :=
  match goal with
   | H : ?E ⊢ ?T <: ?C | ?n |- ?E ⊢ ?B <: ?C => match C with
      | typ_intersection ?C1 ?C2 => dependent destruction H; auto with trans; solve_trans_forall_B_intersection_impl C1 C2
      | typ_union ?C1 ?C2 => dependent destruction H; auto with trans; solve_trans_forall_B_union_impl C1 C2
      | _ => idtac
   end
  end.

Ltac solve_trans_forall_B_C :=
   match goal with
   | H : ?E ⊢ ?T <: ?C | ?n |- ?E ⊢ ?B <: ?C => match T with
      (* the following case of B is impossible. solve them separately *)
      | typ_bot => idtac
      | typ_svar _ => idtac
      | typ_all _ => idtac
      | typ_union _ _ => idtac
      | typ_intersection _ _ => idtac
      (* solve the remaining case *)
      | _ => let H1 := fresh H in
             let Hwft1 := fresh "Hwft" in
              apply d_sub_size_sound in H as H1;
              apply d_sub_dwft in H1; destruct H1 as [_ [_ Hwtf1]];
              apply d_wft_ord_complete in Hwtf1; induction Hwtf1; solve_trans_forall_B_iu
   end
  end.

Ltac ord_inv :=
    match goal with
    | H : d_ord (typ_intersection _ _) |- _ => inversion H
    | H : d_ord (typ_union _ _)|- _ => inversion H
   end.


Lemma d_sub_size_transitivity : forall n_d_typ_order n_dsub_size E R1 S1 T1 n1 n2 ,
  d_typ_order S1 < n_d_typ_order ->
  n1 + n2 < n_dsub_size ->
  E ⊢ R1 <: S1 | n1 -> E ⊢ S1 <: T1 | n2 -> E ⊢ R1 <: T1.
Proof with auto with trans.
  induction n_d_typ_order; induction n_dsub_size; intros * Horder Hsize Hsub1 Hsub2.
  - inversion Horder.
  - inversion Horder.
  - inversion Hsize.
  - dependent destruction Hsub1...
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (S1:=typ_top) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=typ_top) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=typ_top) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=typ_top) (n1:=n); eauto...
        auto.
    + apply d_sub_size_sound in Hsub2.
      apply d_sub_dwft in Hsub2; auto.
      eapply d_sub_bot; intuition.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (S1:=typ_unit) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=typ_unit) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=typ_unit) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=typ_unit) (n1:=n); eauto...
        auto.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (S1:=`ᵈ X) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=`ᵈ X) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=`ᵈ X) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=`ᵈ X) (n1:=n); eauto...
        auto.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (S1:=typ_svar X) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=typ_svar X) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=typ_svar X) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=typ_svar X) (n1:=n); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_size_sound in Hsub1_2.
        apply d_sub_dwft in Hsub1_1. apply d_sub_dwft in Hsub1_2. econstructor; intuition.
      * econstructor.
        eapply IHn_dsub_size with (S1:=T0); eauto...
        eapply IHn_dsub_size with (S1:=T2); eauto...
      * econstructor.
        eapply IHn_dsub_size with (S1:=typ_arrow T0 T2) (n1:=S(n1+n0)); eauto...
        eapply IHn_dsub_size with (S1:=typ_arrow T0 T2) (n1:=S(n1+n0)); eauto...
      * apply d_sub_union1.
        eapply IHn_dsub_size with (S1:=typ_arrow T0 T2) (n1:=S(n1+n0)); eauto...
        auto.
      * apply d_sub_union2.
        eapply IHn_dsub_size with (S1:=typ_arrow T0 T2) (n1:=S(n1+n0)); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor...
        pick fresh Y and apply dwftyp_all.
        ** forwards: H Y...
           applys* fstv_open_tvar. solve_notin.
        ** forwards: H1 Y...
           forwards: d_sub_dwft_sized_1 H4.
           rewrite_env (nil ++ Y ~ ▪ ++ E) in H4.
           rewrite_env (nil ++ Y ~ ▪ ++ E) in H5.
           forwards: d_wf_typ_subst_stvar_tvar H5.
           simpl in H6. rewrite d_subst_stv_in_typ_open_typ_wrt_typ in H6.
           simpl in H6. case_if. rewrite* d_subst_stv_in_typ_fresh_eq in H6.
           solve_notin. now eauto.
      * eapply d_sub_all with (L:=L `union` L0 `union` dom E); auto.
        intros. inst_cofinites_with X.
        eapply IHn_d_typ_order with (S1:= T0 ^^ᵈ typ_svar X); eauto...
        -- simpl in *. rewrite d_open_svar_same_order.
           assert ((d_typ_order T0) < n_d_typ_order) by lia. (* lia strangely fails if proving directly *)
           auto.
      * pick fresh Y and apply d_sub_alll. 5: applys H6. all: eauto.
        ** forwards: H Y...
           applys* fstv_open_tvar. solve_notin.
        ** pick fresh X. inst_cofinites_with X.
        replace E with (map (d_subst_stv_in_binding T2 X) nil ++ E) by auto.
        rewrite_env  (nil ++ (X, ▪) :: E) in H1.
        eapply d_sub_size_subst_stvar in H1; eauto.
        destruct H1 as [n' Hsub].
        eapply IHn_d_typ_order with (S1:=T0 ^^ᵈ T2) (n1:=n'); eauto...
        rewrite d_open_mono_same_order; auto. now lia.
        simpl in Hsub. auto. simpl.
        rewrite 2 d_subst_stv_in_typ_open_typ_wrt_typ in Hsub... simpl in Hsub.
        unfold eq_dec in Hsub. destruct (EqDec_eq_of_X X X) in Hsub.
        rewrite (d_subst_stv_in_typ_fresh_eq S1) in Hsub...
        rewrite (d_subst_stv_in_typ_fresh_eq T0) in Hsub...
        contradiction.
      * eapply d_sub_intersection1.
        -- eapply IHn_dsub_size with (S1:=typ_all T0) (n1:=S n) (n2:=n1); eauto...
           econstructor; eauto.
        -- eapply IHn_dsub_size with (S1:=typ_all T0) (n1:=S n) (n2:=n2); eauto...
           econstructor; eauto.
      * eapply d_sub_union1.
        -- eapply IHn_dsub_size with (S1:=typ_all T0) (n1:=S n) (n2:=n0); eauto...
           econstructor; eauto.
        -- auto.
      * eapply d_sub_union2.
        -- eapply IHn_dsub_size with (S1:=typ_all T0) (n1:=S n) (n2:=n0); eauto...
           econstructor; eauto.
        -- auto.
    + simpl in *. assert (E ⊢ T0) as Hwft0 by applys* d_sub_dwft_sized_1.
      dependent destruction Hwft0; solve_trans_forall_B_C.
      (* solve_trans_forall_B_C. *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply dwftyp_all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ E) in HW.
           forwards*: d_wf_typ_open_stvar_subst_mono HW.
        -- eapply d_sub_alll with (T2:=T2); auto.
           eapply d_sub_size_sound; eauto.
      (* forall a. A < bot < C *)
      * apply d_sub_size_sound in Hsub1.
        exfalso. eapply d_sub_open_mono_bot_false; eauto.
      (* forall a. A < top < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply dwftyp_all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ E) in HW.
           forwards*: d_wf_typ_open_stvar_subst_mono HW.
    (* forall a. A < X < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply dwftyp_all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ E) in HW.
           forwards*: d_wf_typ_open_stvar_subst_mono HW.
        -- eapply d_sub_alll with (T2:=T2); eauto...
            apply d_sub_size_sound in Hsub1. auto.
      (* forall a. A < X < C *)
      * apply d_sub_size_sound in Hsub1.
        exfalso. eapply d_sub_open_mono_stvar_false; eauto.
      (* forall a. A < B1 -> B2 < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply dwftyp_all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ E) in HW.
           forwards*: d_wf_typ_open_stvar_subst_mono HW.
        -- assert (E ⊢ T1) by applys* d_sub_dwft_sized_1. assert (E ⊢ T4) by applys* d_sub_dwft_sized_2.
          eapply d_sub_alll with (T2:=T2); eauto...
          eapply IHn_dsub_size with (S1:=typ_arrow T0 T3) (n2:=S(n1+n2)); eauto...
      * inversion H.
      * inversion H1.
      * inversion H0.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_dwft in Hsub1_1.
        intuition.
      * econstructor.
        eapply IHn_dsub_size with (S1:=typ_intersection T0 T2) (n1:=S(n1+n0)); eauto...
        eapply IHn_dsub_size with (S1:=typ_intersection T0 T2) (n1:=S(n1+n0)); eauto...
      * eapply IHn_dsub_size with (S1:=T0); eauto...
      * eapply IHn_dsub_size with (S1:=T2); eauto...
      * apply d_sub_union1...
        eapply IHn_dsub_size with (S1:=typ_intersection T0 T2) (n1:=S(n1+n0)); eauto...
      * apply d_sub_union2...
        eapply IHn_dsub_size with (S1:=typ_intersection T0 T2) (n1:=S(n1+n0)); eauto...
    + simpl in H. apply d_sub_intersection2...
      * eapply IHn_dsub_size with (S1:=T) (n1:=n); eauto...
    + simpl in H. apply d_sub_intersection3...
      * eapply IHn_dsub_size with (S1:=T) (n1:=n); eauto...
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_dsub_size with (S1:=T0) (n2:=n2); eauto... intuition.
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_dsub_size with (S1:=T2) (n2:=n2); eauto... intuition.
    + simpl in Horder. econstructor...
      * eapply IHn_dsub_size with (S1:=T) (n1:=n1); eauto...
      * eapply IHn_dsub_size with (S1:=T) (n1:=n0); eauto...
Qed.


Theorem sub_transitivity : forall E R1 S1 T1,
  E ⊢ R1 <: S1 -> E ⊢ S1 <: T1 -> E ⊢ R1 <: T1.
Proof.
  intros * Hrs Hst.
  apply d_sub_size_complete in Hrs. destruct Hrs as [n1].
  apply d_sub_size_complete in Hst. destruct Hst as [n2].
  eapply d_sub_size_transitivity; eauto.
Qed.
