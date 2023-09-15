Require Import Coq.Program.Equality.
Require Import Lia.
Require Import LibTactics.

Require Import decl.notations.
Require Import decl.prop_basic.
Require Import ln_utils.

Hint Constructors d_sub : sub.

Lemma dsub_refl' : forall E T,
  ⊢ E -> E ⊢ₛ T -> E ⊢ T <: T.
Proof with auto with sub.
  intros; dependent induction H0; eauto...
  eapply d_sub_all with (L:=L `union` dom E); eauto.
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
  E ⊢ dtyp_union S1 S2 <: T1 ->
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
  E ⊢ S1 <: dtyp_intersection T1 T2 ->
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
  E ⊢ dtyp_all T ->
  E ⊢ dtyp_unit <: dtyp_all T ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem dsub_top_all_false: forall E T,
  E ⊢ dtyp_all T ->
  E ⊢ dtyp_top <: dtyp_all T ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem dsub_top_fv_false: forall E X T,
  ds_in X T ->
  E ⊢ dtyp_top <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.

Theorem dsub_unit_fv_false: forall E X T,
  ds_in X T ->
  E ⊢ dtyp_unit <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.


Fixpoint dtyp_order (T : dtyp) : nat :=
  match T with
  | dtyp_arrow T1 T2 => dtyp_order T1 + dtyp_order T2
  | dtyp_all T1 => S (dtyp_order T1)
  | dtyp_intersection T1 T2 => dtyp_order T1 + dtyp_order T2
  | dtyp_union T1 T2 => dtyp_order T1 + dtyp_order T2
  | _ => 0
  end.

Hint Resolve dwf_typ_lc_dtyp : subtyping.
Hint Resolve dsub_refl : subtyping.
Hint Resolve d_wft_typ_subst : subtyping.
Hint Resolve d_wft_typ_subst_stvar : subtyping.
Hint Resolve d_wf_env_subst_tvar_typ : subtyping.

Inductive d_sub_tvar_open_inv : typvar -> dtyp -> Prop :=
| d__stoi__refl : forall X, d_sub_tvar_open_inv X (dtyp_var_f X)
| d__stoi__union : forall X T1 T2,
    d_sub_tvar_open_inv X T1 ->
    d_sub_tvar_open_inv X T2 ->
    d_sub_tvar_open_inv X (dtyp_union T1 T2)
| d__stoi__intersection1 : forall X T1 T2,
    d_sub_tvar_open_inv X T1 ->
    d_sub_tvar_open_inv X (dtyp_intersection T1 T2)
| d__stoi__intersection2 : forall X T1 T2,
    d_sub_tvar_open_inv X T2 ->
    d_sub_tvar_open_inv X (dtyp_intersection T1 T2).

Lemma d_sub_tvar_open_inv_subst : forall X1 X2 S1 T1,
  d_sub_tvar_open_inv X1 T1 ->
  X1 <> X2 ->
  d_sub_tvar_open_inv X1 ({S1 /ᵈ X2} T1).
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
  d_sub_tvar_open_inv X2 ({`ᵈ X2 /ᵈ X1} T1).
Proof.
  intros. induction H.
  - simpl. destruct (X == X).
    + constructor.
    + contradiction.
  - simpl. econstructor; eauto.
  - simpl. econstructor; eauto.
  - simpl. eapply d__stoi__intersection2. eauto.
Qed.


Inductive d_sub_tvar_inv : dtyp -> Prop :=
| d__sti__all : forall L T,
    (forall X, X `notin` L -> d_sub_tvar_open_inv X (T ^ᵈ X)) ->
    d_sub_tvar_inv (dtyp_all T).



Fixpoint d_typ_order (T : dtyp) : nat :=
  match T with
  | dtyp_all T1 => S ( d_typ_order T1 )
  | dtyp_arrow T1 T2 => d_typ_order T1 + d_typ_order T2
  | dtyp_intersection T1 T2 => d_typ_order T1 + d_typ_order T2
  | dtyp_union T1 T2 => d_typ_order T1 + d_typ_order T2
  | _ => 0
  end.

Fixpoint d_typ_size (T : dtyp) :=
  match T with
  | dtyp_intersection T1 T2 => 1 + d_typ_size T1 + d_typ_size T2
  | dtyp_union T1 T2 => 1 + d_typ_size T1 + d_typ_size T2
  | _ => 0
  end.


Lemma dmono_type_order_0 : forall T,
  dmono_typ T -> d_typ_order T = 0.
Proof.
  intros; induction H; simpl; auto.
  - rewrite IHdmono_typ1. rewrite IHdmono_typ2. auto.
  - rewrite IHdmono_typ1. rewrite IHdmono_typ2. auto.
  - rewrite IHdmono_typ1. rewrite IHdmono_typ2. auto.
Qed.

Lemma d_open_rec_mono_same_order : forall T1 T2 n,
  dmono_typ T2 ->
  d_typ_order (open_dtyp_wrt_dtyp_rec n T2 T1) = d_typ_order T1.
Proof.
  induction T1; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; auto. apply dmono_type_order_0; auto.
    + auto.
Qed.


Lemma d_open_mono_same_order : forall T1 T2,
  dmono_typ T2 ->
  d_typ_order (T1 ^^ᵈ T2) = d_typ_order T1.
Proof.
  intros. unfold open_dtyp_wrt_dtyp. apply d_open_rec_mono_same_order; auto.
Qed.



Theorem d_sub_tvar_inv_nested_all_false: forall L1 L2 L3 T1 S1,
  (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_dtyp_wrt_dtyp_rec 1 S1 T1 ^ᵈ X)) ->
  (forall X : atom, X `notin` L2 -> ds_in X (dtyp_all (open_dtyp_wrt_dtyp_rec 1 `ᵈ X T1))) ->
  (forall X : atom, X `notin` L3 -> ds_in X (open_dtyp_wrt_dtyp_rec 1 S1 T1 ^ᵈ X)) ->
  lc_dtyp S1 ->
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
      * inst_cofinites_by (L3 `union` ftv_in_dtyp S1).
        rewrite open_dtyp_wrt_dtyp_lc_dtyp in H1; auto.
        apply sin_in in H1. apply notin_union_2 in Fr. contradiction.
    + destruct (n - 1).
      * unfold open_dtyp_wrt_dtyp in *. simpl in *.
        inst_cofinites_by L2. dependent destruction H0.
        inst_cofinites_by (L `union` singleton X).
        dependent destruction H0.
        apply notin_union_2 in Fr0. apply notin_singleton_1 in Fr0. contradiction.
      * unfold open_dtyp_wrt_dtyp in *. simpl in *.
        inst_cofinites_by L3. inversion H1.
  - inst_cofinites_by (L3 `union` singleton X).
    dependent destruction H1. apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
  - inst_cofinites_by L3. inversion H1.
  - inst_cofinites_by L1. inversion H.
  - inst_cofinites_by L1. inversion H.
  - assert (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ X)). {
      intros. inst_cofinites_with X. inversion H; auto.
    }
    assert (forall X : atom, X `notin` L2 -> ds_in X (dtyp_all (open_dtyp_wrt_dtyp_rec 1 `ᵈ X T1_1))).
    { intros. inst_cofinites_with X. dependent destruction H0.
      eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
      inversion H0. auto.
    }
    assert  (forall X : atom, X `notin` L3 -> ds_in X (open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ X)).
    { intros. inst_cofinites_with X. inversion H1; auto.
    }
    auto.
  - assert ((forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ X)) \/
            (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_dtyp_wrt_dtyp_rec 1 S1 T1_2 ^ᵈ X))).
    {
      intros.
      inst_cofinites_by (L1 `union` ftv_in_dtyp (open_dtyp_wrt_dtyp_rec 1 S1 T1_1) `union`
                                    ftv_in_dtyp (open_dtyp_wrt_dtyp_rec 1 S1 T1_2)).
      dependent destruction H.
      - left. intros. inst_cofinites_with X.
        assert (d_sub_tvar_open_inv x (open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ x)) by auto.
        replace (open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ X) with ({`ᵈ X /ᵈ x}(open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ x)).
        now apply d_sub_tvar_open_inv_subst_var.
        rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
        rewrite (d_subst_tv_in_dtyp_fresh_eq); auto. simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X x x); auto. contradiction.
      - right. intros. inst_cofinites_with X.
        assert (d_sub_tvar_open_inv x (open_dtyp_wrt_dtyp_rec 1 S1 T1_2 ^ᵈ x)) by auto.
        replace (open_dtyp_wrt_dtyp_rec 1 S1 T1_2 ^ᵈ X) with ({`ᵈ X /ᵈ x}(open_dtyp_wrt_dtyp_rec 1 S1 T1_2 ^ᵈ x)).
        now apply d_sub_tvar_open_inv_subst_var.
        rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
        rewrite (d_subst_tv_in_dtyp_fresh_eq); auto. simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X x x); auto. contradiction.
    }
    inversion H3.
    + assert (forall X : atom, X `notin` L2 -> ds_in X (dtyp_all (open_dtyp_wrt_dtyp_rec 1 `ᵈ X T1_1))).
      { intros. inst_cofinites_with X. dependent destruction H0.
        eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
        inversion H0. auto.
      }
      assert  (forall X, X `notin` L3 -> ds_in X (open_dtyp_wrt_dtyp_rec 1 S1 T1_1 ^ᵈ X)).
      { intros. inst_cofinites_with X. inversion H1; auto.
      }
      auto.
    + assert (forall X, X `notin` L2 -> ds_in X (dtyp_all (open_dtyp_wrt_dtyp_rec 1 `ᵈ X T1_2))).
      { intros. inst_cofinites_with X. dependent destruction H0.
        eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
        inversion H0. auto.
      }
      assert  (forall X, X `notin` L3 -> ds_in X (open_dtyp_wrt_dtyp_rec 1 S1 T1_2 ^ᵈ X)).
      { intros. inst_cofinites_with X. inversion H1; auto.
      }
      auto.
Qed.


Theorem d_sub_tvar_ind_open_inv_complete: forall n1 n2 E S1 T1 X L,
    d_typ_order (T1 ^^ᵈ S1) < n1 ->
    d_typ_size (T1 ^^ᵈ S1) < n2 ->
    E ⊢ T1 ^^ᵈ S1 <: `ᵈ X ->
    (forall X, X `notin` L -> ds_in X (T1 ^ᵈ X)) ->
    dmono_typ S1 ->
    d_sub_tvar_inv (dtyp_all T1).
  Proof.
    intro n1. induction n1.
    - intros. inversion H.
    - intros n2. induction n2.
      + intros. inversion H0.
      + intros. dependent destruction H1; rename x into Heq.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- inst_cofinites_by L. inversion Hdsin.
          -- destruct n. simpl in *.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. subst. inversion Hmono.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- inst_cofinites_by (L `union` (singleton X0)).
            unfold open_dtyp_wrt_dtyp in Hdsin. simpl in Hdsin. dependent destruction Hdsin.
            apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
             (* S0 *)
             assert (d_typ_order ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2) < n1). {
               rewrite d_open_mono_same_order. lia. auto.
             }
             assert (d_typ_size ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2) <
                     S (d_typ_size ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2))) by lia.
             assert ( E ⊢ (open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2 <: `ᵈ X).
             { inversion Heq. subst. auto. }
             assert ( forall X : atom, X `notin` L0 -> ds_in X ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^ᵈ X)).
             { inversion Heq. subst. auto. }
             specialize (IHn1 _ E _ _ _ _ H3 H4 H10 H11 H6).
             unfold open_dtyp_wrt_dtyp in H8. simpl in H8.
             dependent destruction IHn1.
             apply d_mono_typ_lc in H9.
             specialize (d_sub_tvar_inv_nested_all_false _ _ _ _ _ H H8 H12 H9).
             intros. inversion H13.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- replace (dtyp_intersection T1_1 T1_2 ^^ᵈ S1) with (dtyp_intersection (T1_1 ^^ᵈ S1) (T1_2 ^^ᵈ S1)) in Heq by auto.
             dependent destruction Heq.
             assert (d_typ_size (T1_1 ^^ᵈ S1) < n2). {
               unfold open_dtyp_wrt_dtyp. lia.
             }
             assert (d_typ_order (T1_1 ^^ᵈ S1) < S n1). {
               unfold open_dtyp_wrt_dtyp. lia.
             }
             assert (forall X, X `notin` L -> ds_in X (T1_1 ^ᵈ X)). {
               intros. inst_cofinites_with X0.
               replace (dtyp_intersection T1_1 T1_2 ^ᵈ X0) with (dtyp_intersection (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) in Hdsin by auto.
               dependent destruction Hdsin.
               auto.
             }
             specialize (IHn2 _ _ _ _ L H4 H3 H1 H5 Hmono).
             dependent destruction IHn2.
             eapply d__sti__all with (L:=L `union` L0). intros.
             replace (dtyp_intersection T1_1 T1_2 ^ᵈ X0) with (dtyp_intersection (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) by auto.
             econstructor; eauto.
        * rename H3 into Hdsin. rename H4 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- replace (dtyp_intersection T1_1 T1_2 ^^ᵈ S1) with (dtyp_intersection (T1_1 ^^ᵈ S1) (T1_2 ^^ᵈ S1)) in Heq by auto.
             dependent destruction Heq.
             assert (d_typ_size (T1_2 ^^ᵈ S1) < n2). {
                unfold open_dtyp_wrt_dtyp. lia.
             }
             assert (d_typ_order (T1_2 ^^ᵈ S1) < S n1). {
                unfold open_dtyp_wrt_dtyp. lia.
             }
             assert (forall X, X `notin` L -> ds_in X (T1_2 ^ᵈ X)). {
              intros. inst_cofinites_with X0.
              replace (dtyp_intersection T1_1 T1_2 ^ᵈ X0) with (dtyp_intersection (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) in Hdsin by auto.
              dependent destruction Hdsin.
              auto.
             }
             specialize (IHn2 _ _ _ _ L H4 H3 H1 H5 Hmono).
             dependent destruction IHn2.
             eapply d__sti__all with (L:=L `union` L0). intros.
             replace (dtyp_intersection T1_1 T1_2 ^ᵈ X0) with (dtyp_intersection (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) by auto.
             eapply d__stoi__intersection2; eauto.
        * rename H2 into Hdsin. rename H3 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- replace (dtyp_union T1_1 T1_2 ^^ᵈ S1) with (dtyp_union (T1_1 ^^ᵈ S1) (T1_2 ^^ᵈ S1)) in Heq by auto.
              dependent destruction Heq.
              assert (d_typ_size (T1_1 ^^ᵈ S1) < n2). {
                  unfold open_dtyp_wrt_dtyp. lia.
              }
              assert (d_typ_order (T1_1 ^^ᵈ S1) < S n1). {
                  unfold open_dtyp_wrt_dtyp. lia.
              }
              assert (forall X, X `notin` L -> ds_in X (T1_1 ^ᵈ X)). {
                intros. inst_cofinites_with X0.
                replace (dtyp_union T1_1 T1_2 ^ᵈ X0) with (dtyp_union (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) in Hdsin by auto.
                dependent destruction Hdsin.
                auto.
              }
              assert (d_typ_size (T1_2 ^^ᵈ S1) < n2). {
                  unfold open_dtyp_wrt_dtyp. lia.
              }
              assert (d_typ_order (T1_2 ^^ᵈ S1) < S n1). {
                  unfold open_dtyp_wrt_dtyp. lia.
              }
              assert (forall X, X `notin` L -> ds_in X (T1_2 ^ᵈ X)). {
                intros. inst_cofinites_with X0.
                replace (dtyp_union T1_1 T1_2 ^ᵈ X0) with (dtyp_union (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) in Hdsin by auto.
                dependent destruction Hdsin.
                auto.
              }
              specialize (IHn2 _ _ _ _ L H2 H1 H1_ H3 Hmono) as IHn2_1.
              specialize (IHn2 _ _ _ _ L H5 H4 H1_0 H6 Hmono) as IHn2_2.
              dependent destruction IHn2_1.
              dependent destruction IHn2_2.
              eapply d__sti__all with (L:=L `union` L0 `union` L1). intros.
              replace (dtyp_union T1_1 T1_2 ^ᵈ X0) with (dtyp_union (T1_1 ^ᵈ X0) (T1_2 ^ᵈ X0)) by auto.
              econstructor; eauto.
Qed.


Lemma d_sub_tvar_inv_subst: forall T1 X S1,
    d_sub_tvar_inv T1 -> lc_dtyp S1 -> d_sub_tvar_inv ({S1 /ᵈ X} T1).
Proof.
  intros. dependent destruction H.
  simpl.
  eapply d__sti__all with (L:=L `union` singleton X).
  intros.
  rewrite dtyp_subst_open_comm.
  - apply d_sub_tvar_open_inv_subst; auto.
  - auto.
  - simpl. apply notin_union_2 in H1.
    apply notin_singleton_1' in H1.
    apply notin_singleton. auto.
Qed.


Inductive d_ord_mono : dtyp -> Prop :=
| d__ordmono__tvar : forall X, d_ord_mono (dtyp_var_f X)
| d__ordmono__unit : d_ord_mono dtyp_unit
| d__ordmono__arr : forall T1 T2,
    dmono_typ T1 ->
    dmono_typ T2 ->
    d_ord_mono (dtyp_arrow T1 T2)
.

Lemma d_ord_mono_neq_intersection: forall T1,
  d_ord_mono T1 ->
  dneq_intersection T1.
Proof.
  intros. induction H; auto.
Qed.

Lemma d_ord_mono_neq_union: forall T1,
  d_ord_mono T1 ->
  dneq_union T1.
Proof.
  intros. induction H; auto.
Qed.

Inductive d_mono_ordiu : dtyp -> Prop :=
| d__monoord__base : forall T1,
    d_ord_mono T1 ->
    d_mono_ordiu T1
| d__monoord__union : forall T1 T2,
    d_mono_ordiu T1 ->
    d_mono_ordiu T2 ->
    d_mono_ordiu (dtyp_union T1 T2)
| d__monoord__inter : forall T1 T2,
    d_mono_ordiu T1 ->
    d_mono_ordiu T2 ->
    d_mono_ordiu (dtyp_intersection T1 T2).


Lemma d_mono_ordiu_complete : forall T1,
  dmono_typ T1 -> d_mono_ordiu T1.
Proof.
  intros. induction H; try solve [constructor; constructor].
  - apply d__monoord__base. apply d__ordmono__arr; auto.
  - apply d__monoord__inter; auto.
  - apply d__monoord__union; auto.
Qed.


Lemma d_ord_mono_sound: forall T1,
  d_ord_mono T1 -> dmono_typ T1.
Proof.
  intros. induction H; auto.
Qed.

Lemma d_mono_ordiu_sound : forall T1,
  d_mono_ordiu T1 -> dmono_typ T1.
Proof.
  intros. induction H; auto.
  - apply d_ord_mono_sound. auto.
Qed.


Theorem d_sub_tvar_ind_open_subst : forall E F X T1 T2,
  ⊢ F ++ (X ~ dbind_tvar_empty) ++ E ->
  d_sub_tvar_open_inv X T1 ->
  dmono_typ T2 ->
  (X ~ dbind_tvar_empty) ++ E ⊢ T1 ->
  E ⊢ T2 ->
  map (d_subst_tv_in_binding T2 X) F ++ E ⊢ ({T2 /ᵈ X} T1) <: T2.
Proof with auto with subtyping.
  intros * Hwfenv H. induction H; intros.
  - simpl. destruct (X == X).
    + apply dsub_refl; auto...
      replace T2 with ({T2 /ᵈ X} `ᵈ X) at 2.
      apply d_wft_typ_subst; auto.
      simpl. destruct (X == X); auto. contradiction.
    + contradiction.
  - simpl. dependent destruction H2. constructor; auto.
  - simpl. dependent destruction H1. constructor; auto.
    apply d_wft_typ_subst; auto.
    apply dwf_typ_weakening with (E3:=nil); auto.
  - simpl. dependent destruction H1. apply d_sub_intersection3; auto.
    apply d_wft_typ_subst; auto.
    apply dwf_typ_weakening with (E3:=nil); auto.
Qed.


Theorem d_sub_weakening: forall E F G S1 T1,
  G ++ E ⊢ S1 <: T1 ->
  ⊢ G ++ F ++ E ->
  G ++ F ++ E ⊢ S1 <: T1.
Proof.
Admitted.


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


Theorem d_sub_tvar_ind_sub_all : forall E T1 T2,
  ⊢ E ->
  d_sub_tvar_inv (dtyp_all T1) ->
  E ⊢ dtyp_all T1 ->
  dmono_typ T2 ->
  E ⊢ T2 ->
  E ⊢ dtyp_all T1 <: T2.
Proof.
  intros * Hwfenv H Hwft Hmono Hwft2.
  specialize (d_mono_ordiu_complete _ Hmono). intros.
  induction H0.
  - dependent destruction H.
    dependent destruction Hwft.
    eapply d_sub_alll with (L:=L `union` L0) (T2:=T0).
    + now apply d_mono_typ_neq_all.
    + now apply d_ord_mono_neq_intersection.
    + now apply d_ord_mono_neq_union.
    + auto.
    + auto.
    + auto.
    + inst_cofinites_by (L `union` L0 `union` ftv_in_dtyp T1 `union` dom E) using_name X.
      apply d_sub_tvar_ind_open_subst with (E:= E) (T2:=T0) (F:=nil) in H.
      rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp in H; auto.
      rewrite d_subst_tv_in_dtyp_fresh_eq in H; auto.
      simpl in H. destruct eq_dec in H. auto.
      contradiction.
      * simpl. constructor; auto.
      * auto.
      * auto.
      * auto.
  - inversion Hmono. inversion Hwft2. auto.
  - inversion Hmono. inversion Hwft2. auto.
Qed.


Theorem  d_sub_subst_mono : forall E X F S1 T1 T2,
  ⊢ F ++ (X ~ dbind_tvar_empty) ++ E ->
  F ++ (X ~ dbind_tvar_empty) ++ E ⊢ S1 <: T1 ->
  E ⊢ T2 ->
  dmono_typ T2 ->
  map (d_subst_tv_in_binding T2 X) F ++ E ⊢ {T2 /ᵈ X} S1 <: {T2 /ᵈ X} T1.
Proof with eauto with subtyping.
  intros E X F S1 T1 T2 Hwfenv Hsub Hwft Hmono.
  dependent induction Hsub; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl; auto...
  - eapply dsub_refl; auto...
  - simpl. eapply d_sub_all with (L:=L `union` singleton X `union` dom E `union` dom F); intros SX Hfr; inst_cofinites_with SX.
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + inst_cofinites_with SX. repeat rewrite dtyp_subst_open_comm; eauto...
      replace (SX ~ dbind_stvar_empty ++ map (d_subst_tv_in_binding T2 X) F ++ E) with
      (map (d_subst_tv_in_binding T2 X) (SX ~ dbind_stvar_empty ++ F) ++ E) by auto.
      eapply H2; auto... simpl. constructor; eauto.
  - destruct T1 eqn:HeqT.
    + eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
    + eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); eauto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
    + eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
    + apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]]. inversion HwftT.
    + simpl.
      apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]].
      apply d_sub_tvar_ind_sub_all.
      -- eapply d_wf_env_subst_tvar_typ; auto.
      -- replace (dtyp_all ({T2 /ᵈ X} S1)) with ({T2 /ᵈ X} (dtyp_all S1)) by auto.
         apply d_sub_tvar_inv_subst. eapply d_sub_tvar_ind_open_inv_complete; eauto.
         eapply dwf_typ_lc_dtyp; eauto.
      -- replace (dtyp_all ({T2 /ᵈ X} S1)) with ({T2 /ᵈ X} (dtyp_all S1)) by auto.
         apply d_wft_typ_subst; auto.
         inst_cofinites_for dwftyp_all.
         ++ auto.
         ++ intros. eapply dwf_typ_open_inv with (X:=X1) (S1:=T0); auto.
            rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
            simpl. rewrite (d_subst_tv_in_dtyp_fresh_eq); auto.
            unfold eq_dec. destruct (EqDec_eq_of_X X1 X1); auto.
            ** apply dwf_typ_weakening_cons; auto.
            ** contradiction.
      -- unfold eq_dec. destruct (EqDec_eq_of_X X0 X); auto.
      -- replace (if X0 == X then T2 else `ᵈ X0) with ( {T2 /ᵈ X} `ᵈ X0) by auto.
         apply d_wft_typ_subst; auto.
    + apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]]. inversion HwftT.
      eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); eauto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
    + eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); eauto...
      * admit.
      * admit.
      * admit.
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
    + inversion H.
    + inversion H1.
    + inversion H0.
Admitted.


Hint Resolve d_wft_typ_subst_stvar : subtyping.

Theorem d_sub_subst_stvar : forall E SX F S1 T1 T2,
  F ++ (SX ~ dbind_stvar_empty) ++ E ⊢ S1 <: T1 ->
  E ⊢ T2 ->
  map (d_subst_stv_in_binding T2 SX) F ++ E ⊢ {T2 /ₛᵈ SX} S1 <: {T2 /ₛᵈ SX} T1.
Proof with subst; eauto using dwf_typ_weaken_head with subtyping.
  (* intros. dependent induction H0; try solve [simpl in *; eauto with subtyping].
  - simpl in *. inverts H0. forwards* [?|?]: binds_app_1 H4.
    + forwards*: binds_map_2 (d_subst_stv_in_binding T2 SX) H0.
    + match goal with
        H: _ ~ ▫ ∈ ((_, _) :: _) |- _ => apply binds_cons_iff in H
      end; intuition eauto; try solve_by_invert.
  - destruct (SX0 == SX); apply dsub_refl...
  - simpl. inst_cofinites_for d_sub_all; intros SX1 Hfr; inst_cofinites_with SX1...
    + case_eq (SX1 == SX); intros; subst; try solve_notin.
      replace (({T2 /ₛᵈ SX} S1) ^^ᵈ dtyp_svar SX1) with ({T2 /ₛᵈ SX} S1 ^^ᵈ dtyp_svar SX1); eauto.
      2: { rewrite* d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp.
           simpl. case_if*. }
      applys* fstv_sins_dtyp_subst_stv_s.
    + case_eq (SX1 == SX); intros; subst; try solve_notin.
      replace (({T2 /ₛᵈ SX} T1) ^^ᵈ dtyp_svar SX1) with ({T2 /ₛᵈ SX} T1 ^^ᵈ dtyp_svar SX1); eauto.
      2: { rewrite* d_subst_stv_in_dtyp_open_dtyp_wrt_dtyp.
           simpl. case_if*. }
      applys* fstv_sins_dtyp_subst_stv_s.
    + inst_cofinites_with SX1. repeat rewrite d_subst_stv_in_dtyp_open_comm; eauto...
      replace (SX1 ~ dbind_stvar_empty ++ map (d_subst_stv_in_binding T2 SX) F ++ E) with
      (map (d_subst_stv_in_binding T2 SX) (SX1 ~ dbind_stvar_empty ++ F) ++ E) by auto.
      eapply H2; auto...
      simpl. constructor. auto. auto.
  (* @chen *)
  - assert (E ⊢ T1) by admit.
    destruct T1; simpl in *.
    + inst_cofinites_for d_sub_alll T2:=(T0). *)
Admitted.


Inductive d_sub_sized : denv -> dtyp -> dtyp -> nat -> Prop :=
 | d__subs__top : forall (E:denv) (S1:dtyp) (n:nat),
     dwf_env E ->
     dwf_typ E S1 ->
     d_sub_sized E S1 dtyp_top n
 | d__subs__bot : forall (E:denv) (T:dtyp) (n:nat),
     dwf_env E ->
     dwf_typ E T ->
     d_sub_sized E dtyp_bot T n
 | d__subs__unit : forall (E:denv) (n:nat),
     dwf_env E ->
     d_sub_sized E dtyp_unit dtyp_unit n
 | d__subs__tvar : forall (E:denv) (X:typvar) (n:nat),
     dwf_env E ->
     dwf_typ E (dtyp_var_f X) ->
     d_sub_sized E (dtyp_var_f X) (dtyp_var_f X) n
 | d__subs__stvar : forall (E:denv) (SX:stypvar) (n:nat),
     dwf_env E ->
     dwf_typ E (dtyp_svar SX) ->
     d_sub_sized E (dtyp_svar SX) (dtyp_svar SX) n
 | d__subs__arrow : forall (E:denv) (S1 S2 T1 T2:dtyp) (n1 n2:nat),
     d_sub_sized E T1 S1 n1 ->
     d_sub_sized E S2 T2 n2 ->
     d_sub_sized E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2) (S (n1 + n2))
 | d__subs__all : forall (L:vars) (E:denv) (S1 T1:dtyp) (n:nat),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> d_sub_sized  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T1  (dtyp_svar SX) ) n) ->
     d_sub_sized E (dtyp_all S1) (dtyp_all T1) (S n)
 | d__subs__alll : forall (L:vars) (E:denv) (S1 T1 T2:dtyp) (n:nat),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 ->
     ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S1   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     d_sub_sized E  (open_dtyp_wrt_dtyp  S1   T2 )  T1 n ->
     d_sub_sized E (dtyp_all S1) T1 (S n)
 | d__subs__intersection1 : forall (E:denv) (S1 T1 T2:dtyp) (n1 n2:nat),
     d_sub_sized E S1 T1 n1 ->
     d_sub_sized E S1 T2 n2 ->
     d_sub_sized E S1 (dtyp_intersection T1 T2) (S (n1 + n2))
 | d__subs__intersection2 : forall (E:denv) (S1 S2 T:dtyp) (n:nat),
     d_sub_sized E S1 T n ->
     dwf_typ E S2 ->
     d_sub_sized E (dtyp_intersection S1 S2) T (S n)
 | d__subs__intersection3 : forall (E:denv) (S1 S2 T:dtyp) (n:nat),
     d_sub_sized E S2 T n ->
     dwf_typ E S1 ->
     d_sub_sized E (dtyp_intersection S1 S2) T (S n)
 | d__subs__union1 : forall (E:denv) (S1 T1 T2:dtyp) (n:nat),
     d_sub_sized E S1 T1 n ->
     dwf_typ E T2 ->
     d_sub_sized E S1 (dtyp_union T1 T2) (S n)
 | d__subs__union2 : forall (E:denv) (S1 T1 T2:dtyp) (n:nat),
     d_sub_sized E S1 T2 n ->
     dwf_typ E T1 ->
     d_sub_sized E S1 (dtyp_union T1 T2) (S n)
 | d__subs__union3 : forall (E:denv) (S1 S2 T:dtyp) (n1 n2:nat),
     d_sub_sized E S1 T n1 ->
     d_sub_sized E S2 T n2 ->
     d_sub_sized E (dtyp_union S1 S2) T (S (n1 + n2)).

Notation "E ⊢ S1 <: T1 | n" :=
  (d_sub_sized E S1 T1 n)
    (at level 65, S1 at next level, T1 at next level, no associativity) : type_scope.

Theorem d_sub_size_sound : forall E S1 T1 n,
    E ⊢ S1 <: T1 | n -> E ⊢ S1 <: T1.
Proof.
  intros. induction H; eauto.
Qed.

Hint Constructors d_sub_sized : sub.

Lemma d_sub_size_complete : forall E T1 T2,
  E ⊢ T1 <: T2 -> exists n, E ⊢ T1 <: T2 | n.
Proof with eauto with sub.
  intros. induction H; eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
  - inst_cofinites_by (L `union` fstv_in_dtyp S1 `union` fstv_in_dtyp S1).
    destruct H2 as [n].
    exists (S n). eapply d__subs__all with (L:=L `union` fstv_in_dtyp S1 `union` fstv_in_dtyp S1); intros.
    + Search (ds_in_s). admit.
    + admit.
    + admit.
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
  eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub as [n]. eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
Admitted.



Hint Constructors d_sub_sized : trans.


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


Lemma d_sub_size_union_inv: forall E S1 S2 T1 n,
  E ⊢ (dtyp_union S1 S2) <: T1 | n -> E ⊢ S1 <: T1 | n /\ E ⊢ S2 <: T1 | n.
Proof with auto with trans.
  intros.
  dependent induction H.
  - inversion H0. split; auto...
  - specialize (IHd_sub_sized1 S1 S2 (eq_refl _)).
    specialize (IHd_sub_sized2 S1 S2 (eq_refl _)).
    split; constructor; intuition.
  - specialize (IHd_sub_sized S1 S2 (eq_refl _)).
    split; apply d__subs__union1; intuition.
  - specialize (IHd_sub_sized S1 S2 (eq_refl _)).
    split; apply d__subs__union2; intuition.
  - split.
    eapply d_sub_size_more; eauto. lia.
    eapply d_sub_size_more; eauto. lia.
Qed.



Theorem d_sub_size_subst_stvar : forall E F SX S1 T1 T2 n,
  F ++ (SX ~ dbind_stvar_empty) ++ E ⊢ S1 <: T1 | n ->
  E ⊢ T2 ->
  dmono_typ T2 ->
  exists n', map (d_subst_stv_in_binding T2 SX) F ++ E ⊢ {T2 /ₛᵈ SX} S1 <: {T2 /ₛᵈ SX} T1 | n'.
Proof.
  intros.
  apply d_sub_size_sound in H.
  apply d_sub_subst_stvar with (T2:=T2) in H; auto.
  apply d_sub_size_complete in H. auto.
Qed.

Inductive d_ord : dtyp -> Prop :=
| d__ord__tvar : forall X, d_ord (dtyp_var_f X)
| d__ord__stvar : forall SX, d_ord (dtyp_svar SX)
| d__ord__bot : d_ord dtyp_bot
| d__ord__top : d_ord dtyp_top
| d__ord__unit : d_ord dtyp_unit
| d__ord__arr : forall T1 T2,
    d_ord (dtyp_arrow T1 T2)
| d__ord__all : forall T,
    d_ord (dtyp_all T)
.

Inductive d_wft_ord : dtyp -> Prop :=
| d__wftord__base : forall T, d_ord T -> d_wft_ord T
| d__wftord__intersection: forall T1 T2,
    d_wft_ord T1 ->
    d_wft_ord T2 ->
    d_wft_ord (dtyp_intersection T1 T2)
| d__wftord__union: forall T1 T2,
    d_wft_ord T1 ->
    d_wft_ord T2 ->
    d_wft_ord (dtyp_union T1 T2)
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
  E ⊢ T1 <: dtyp_bot ->
  False.
Proof.
  intros. induction H; try solve [(dependent destruction H0); auto].
Qed.



Theorem d_sub_open_mono_bot_false: forall n1 n2 E S1 T1 L,
    d_typ_order (T1 ^^ᵈ S1) < n1 ->
    d_typ_size (T1 ^^ᵈ S1) < n2 ->
    E ⊢ T1 ^^ᵈ S1 <: dtyp_bot ->
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
            ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
                subst. inversion H4.
            ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
                inversion Heq.
      * destruct T1; simpl in *; try solve [ inversion Heq].
        -- destruct n.
            ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
                subst. inversion H9.
            ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
                inversion Heq.
        -- inversion Heq. subst. eapply IHn1; eauto.
           rewrite d_open_mono_same_order; auto. lia.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
              subst. dependent destruction H4.
              eapply d_sub_mono_bot_false with (T1:=S0); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_dtyp_wrt_dtyp. lia.
           ++ unfold open_dtyp_wrt_dtyp. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
              subst. dependent destruction H4.
              eapply d_sub_mono_bot_false with (T1:=S2); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_dtyp_wrt_dtyp. lia.
           ++ unfold open_dtyp_wrt_dtyp. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
              subst. dependent destruction H3.
              eapply d_sub_mono_bot_false with (T1:=S0); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_dtyp_wrt_dtyp. lia.
           ++ unfold open_dtyp_wrt_dtyp. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H2; auto.
Qed.


Theorem d_sub_mono_stvar_false : forall E T1 SX,
  dmono_typ T1 ->
  E ⊢ T1 <: dtyp_svar SX ->
  False.
Proof.
  intros. induction H; try solve [(dependent destruction H0); auto].
Qed.


Theorem d_sub_open_mono_stvar_false: forall n1 n2 E S1 T1 SX L,
    d_typ_order (T1 ^^ᵈ S1) < n1 ->
    d_typ_size (T1 ^^ᵈ S1) < n2 ->
    E ⊢ T1 ^^ᵈ S1 <: dtyp_svar SX ->
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
        -- inst_cofinites_by L using_name X. inversion H3.
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
              subst. inversion H4.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
              inversion Heq.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
          ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
            subst. inversion H4.
          ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in *.
            inversion Heq.
        -- inst_cofinites_by L using_name X. inversion H3.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
          ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
              subst. dependent destruction H9.
          ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq.
           eapply IHn1; eauto. rewrite d_open_mono_same_order; auto. lia.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in H, H0, Heq. simpl in *.
              subst. dependent destruction H4.
              apply d_sub_mono_stvar_false in H1; auto.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
              inversion Heq.
        -- dependent destruction Heq. unfold open_dtyp_wrt_dtyp in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in H, H0, Heq. simpl in *.
              subst. dependent destruction H4.
              apply d_sub_mono_stvar_false in H1; auto.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_dtyp_wrt_dtyp in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct T1; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_dtyp_wrt_dtyp in H, H0, Heq. simpl in *.
              subst. dependent destruction H3.
              apply d_sub_mono_stvar_false in H1_; auto.
           ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_dtyp_wrt_dtyp in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X. dependent destruction H2; auto.
Qed.


Lemma d_sub_sized_transitivity : forall n_dtyp_order n_dsub_size E R1 S1 T1 n1 n2 ,
  dtyp_order S1 < n_dtyp_order ->
  n1 + n2 < n_dsub_size ->
  E ⊢ R1 <: S1 | n1 -> E ⊢ S1 <: T1 | n2 -> E ⊢ R1 <: T1.
Proof with auto with trans.
  induction n_dtyp_order; induction n_dsub_size; intros * Horder Hsize Hsub1 Hsub2.
  - inversion Horder.
  - inversion Horder.
  - inversion Hsize.
  - dependent destruction Hsub1...
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (S1:=dtyp_top) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=dtyp_top) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=dtyp_top) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=dtyp_top) (n1:=n); eauto...
        auto.
    + apply d_sub_size_sound in Hsub2.
      apply d_sub_dwft in Hsub2; auto.
      eapply d_sub_bot; intuition.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (S1:=dtyp_unit) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=dtyp_unit) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=dtyp_unit) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=dtyp_unit) (n1:=n); eauto...
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
        eapply IHn_dsub_size with (S1:=dtyp_svar SX) (n1:=n2); eauto...
        eapply IHn_dsub_size with (S1:=dtyp_svar SX) (n1:=n1); eauto...
      * simpl in H. eapply d_sub_union1.
        eapply IHn_dsub_size with (S1:=dtyp_svar SX) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub_union2.
        eapply IHn_dsub_size with (S1:=dtyp_svar SX) (n1:=n); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_size_sound in Hsub1_2.
        apply d_sub_dwft in Hsub1_1. apply d_sub_dwft in Hsub1_2. econstructor; intuition.
      * econstructor.
        eapply IHn_dsub_size with (S1:=T0); eauto...
        eapply IHn_dsub_size with (S1:=T2); eauto...
      * econstructor.
        eapply IHn_dsub_size with (S1:=dtyp_arrow T0 T2) (n1:=S(n1+n0)); eauto...
        eapply IHn_dsub_size with (S1:=dtyp_arrow T0 T2) (n1:=S(n1+n0)); eauto...
      * apply d_sub_union1.
        eapply IHn_dsub_size with (S1:=dtyp_arrow T0 T2) (n1:=S(n1+n0)); eauto...
        auto.
      * apply d_sub_union2.
        eapply IHn_dsub_size with (S1:=dtyp_arrow T0 T2) (n1:=S(n1+n0)); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor...
        admit. (*wft*)
      * eapply d_sub_all with (L:=L `union` L0 `union` dom E); auto.
        intros. inst_cofinites_with SX.
        eapply IHn_dtyp_order with (S1:= T0 ^^ᵈ dtyp_svar SX); eauto...
        -- admit. (* order *)
      * eapply d_sub_alll with (T2:=T2); eauto.
        admit. (* ds_in *)
        inst_cofinites_by (L `union` fstv_in_dtyp S1 `union` fstv_in_dtyp T0) using_name SX.
        replace (S1 ^^ᵈ T2) with ({T2 /ₛᵈ SX} S1 ^^ᵈ dtyp_svar SX) by admit.
        replace E with (map (d_subst_stv_in_binding T2 SX) nil ++ E) by auto.
        specialize (d_sub_size_subst_stvar E nil SX (S1 ^^ᵈ dtyp_svar SX) (T0 ^^ᵈ dtyp_svar SX) T2 n H1 H6 H7).
        intros. destruct H8 as [n' Hsub].
        eapply IHn_dtyp_order with (S1:=T0 ^^ᵈ T2) (n1:=n'); eauto...
        admit. (*order*)
        replace (T0 ^^ᵈ T2) with ({T2 /ₛᵈ SX} T0 ^^ᵈ dtyp_svar SX) by admit.
        eauto.
      * eapply d_sub_intersection1.
        -- eapply IHn_dsub_size with (S1:=dtyp_all T0) (n1:=S n) (n2:=n1); eauto...
           econstructor; eauto.
        -- eapply IHn_dsub_size with (S1:=dtyp_all T0) (n1:=S n) (n2:=n2); eauto...
           econstructor; eauto.
      * eapply d_sub_union1.
        -- eapply IHn_dsub_size with (S1:=dtyp_all T0) (n1:=S n) (n2:=n0); eauto...
           econstructor; eauto.
        -- auto.
      * eapply d_sub_union2.
        -- eapply IHn_dsub_size with (S1:=dtyp_all T0) (n1:=S n) (n2:=n0); eauto...
           econstructor; eauto.
        -- auto.
    + simpl in *. assert (E ⊢ T0) as Hwft0 by admit. dependent destruction Hwft0.
      * apply d_sub_size_sound in Hsub2 as Hdsub.
        apply d_sub_dwft in Hdsub. destruct Hdsub as [_ [_ Hwft1]]. 
        apply d_wft_ord_complete in Hwft1. induction Hwft1.
        -- dependent destruction Hsub2; auto...
           ++ econstructor... admit.
           ++ eapply d_sub_alll with (T2:=T2); auto.
              eapply d_sub_size_sound; eauto.
           ++ inversion H5.
           ++ inversion H6.
           ++ inversion H6.
        -- dependent destruction Hsub2; auto...
           apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_1.
           apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_2.
           specialize (IHHwft1_1 Hsub2_1).
           specialize (IHHwft1_2 Hsub2_2).
           auto... lia. lia.
        -- dependent destruction Hsub2; auto...
           ++ apply d_sub_size_more with (n':=S n0) in Hsub2.
              specialize (IHHwft1_1 Hsub2). auto. lia.
           ++ apply d_sub_size_more with (n':=S n0) in Hsub2.
              specialize (IHHwft1_2 Hsub2). auto. lia.
    (* forall a. A < bot < C *)
      * admit.
      (* forall a. A < top < C *)
      * apply d_sub_size_sound in Hsub2 as Hdsub.
        apply d_sub_dwft in Hdsub. destruct Hdsub as [_ [_ Hwft1]]. 
        apply d_wft_ord_complete in Hwft1. induction Hwft1.
        -- dependent destruction Hsub2; auto...
          ++ econstructor... admit.
          ++ inversion H5.
          ++ inversion H6.
          ++ inversion H6.
        -- dependent destruction Hsub2; auto...
          apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_1.
          apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_2.
          specialize (IHHwft1_1 Hsub2_1).
          specialize (IHHwft1_2 Hsub2_2).
          auto... lia. lia.
        -- dependent destruction Hsub2; auto...
          ++ apply d_sub_size_more with (n':=S n0) in Hsub2.
              specialize (IHHwft1_1 Hsub2). auto. lia.
          ++ apply d_sub_size_more with (n':=S n0) in Hsub2.
              specialize (IHHwft1_2 Hsub2). auto. lia.
    (* forall a. A < X < C *)
      * apply d_sub_size_sound in Hsub2 as Hdsub...
        apply d_sub_dwft in Hdsub. destruct Hdsub as [_ [_ Hwft1]]. 
        apply d_wft_ord_complete in Hwft1. induction Hwft1.
        -- dependent destruction Hsub2; auto...
          ++ econstructor... admit.
          ++ eapply d_sub_alll with (T2:=T2); eauto...
              apply d_sub_size_sound in Hsub1. auto.
          ++ inversion H6.
          ++ inversion H7.
          ++ inversion H7.
        -- dependent destruction Hsub2; auto...
          apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_1...
          apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_2...
          lia. lia.
        -- dependent destruction Hsub2; auto...
          ++ apply d_sub_size_more with (n':=S n0) in Hsub2...
          ++ apply d_sub_size_more with (n':=S n0) in Hsub2...
      (* forall a. A < SX < C *)
      * apply d_sub_size_sound in Hsub1.
        eapply d_sub_open_mono_stvar_false in Hsub1 as Contra; eauto.
        inversion Contra.
      (* forall a. A < B1 -> B2 < C *)
      * apply d_sub_size_sound in Hsub2 as Hdsub...
        apply d_sub_dwft in Hdsub. destruct Hdsub as [_ [_ Hwft1]]. 
        apply d_wft_ord_complete in Hwft1. induction Hwft1.
        -- dependent destruction Hsub2; auto...
           ++ econstructor... admit.
           ++ eapply d_sub_alll with (T2:=T2); eauto...
              assert (E ⊢ T1) by admit. assert (E ⊢ T4) by admit.
              constructor; eauto...
              admit. admit.
             eapply IHn_dsub_size with (S1:=dtyp_arrow T0 T3) (n2:=S(n1+n2)); eauto...
          ++ inversion H5.
          ++ inversion H6.
          ++ inversion H6.
        -- dependent destruction Hsub2; auto...
           apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_1...
           apply d_sub_size_more with (n':=S(n1+n2)) in Hsub2_2...
           lia. lia.
        -- dependent destruction Hsub2; auto...
           ++ apply d_sub_size_more with (n':=S n0) in Hsub2...
           ++ apply d_sub_size_more with (n':=S n0) in Hsub2...
      * inversion H.
      * inversion H1.
      * inversion H0.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_dwft in Hsub1_1.
        intuition. 
      * econstructor.
        eapply IHn_dsub_size with (S1:=dtyp_intersection T0 T2) (n1:=S(n1+n0)); eauto...
        eapply IHn_dsub_size with (S1:=dtyp_intersection T0 T2) (n1:=S(n1+n0)); eauto...
      * eapply IHn_dsub_size with (S1:=T0); eauto...
      * eapply IHn_dsub_size with (S1:=T2); eauto...
      * apply d_sub_union1.
        eapply IHn_dsub_size with (S1:=dtyp_intersection T0 T2) (n1:=S(n1+n0)); eauto...
        auto.
      * apply d_sub_union2.
        eapply IHn_dsub_size with (S1:=dtyp_intersection T0 T2) (n1:=S(n1+n0)); eauto...
        auto.
    + simpl in H. apply d_sub_intersection2.
      * eapply IHn_dsub_size with (S1:=T) (n1:=n); eauto...
      * auto.
    + simpl in H. apply d_sub_intersection3.
      * eapply IHn_dsub_size with (S1:=T) (n1:=n); eauto...
      * auto.
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_dsub_size with (S1:=T0) (n2:=n2); eauto... intuition.
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_dsub_size with (S1:=T2) (n2:=n2); eauto... intuition.
    + simpl in Horder. econstructor.
      * eapply IHn_dsub_size with (S1:=T) (n1:=n1); eauto...
      * eapply IHn_dsub_size with (S1:=T) (n1:=n0); eauto...
Admitted.


Theorem sub_transitivity : forall E R1 S1 T1,
  E ⊢ R1 <: S1 -> E ⊢ S1 <: T1 -> E ⊢ R1 <: T1.
Proof.
  intros * Hrs Hst.
  apply d_sub_size_complete in Hrs. destruct Hrs as [n1].
  apply d_sub_size_complete in Hst. destruct Hst as [n2].
  eapply d_sub_sized_transitivity; eauto.
Qed.
