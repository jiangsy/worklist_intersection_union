Require Import Coq.Program.Equality.
Require Import Lia.
Require Import LibTactics.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import ln_utils.

Hint Constructors d_sub : sub.

Lemma dsub_refl' : forall Ψ A,
  ⊢ Ψ -> Ψ ⊢ₛ A -> Ψ ⊢ A <: A.
Proof with auto with sub.
  intros; dependent induction H0; eauto...
  eapply d_sub__all with (L:=L `union` dom Ψ); eauto.
Qed.


Lemma dsub_refl : forall Ψ T,
  ⊢ Ψ -> Ψ ⊢ T -> Ψ ⊢ T <: T.
Proof.
  intros.
  apply dsub_refl'. auto.
  apply dwf_typ_dwf_typ_s.
  auto.
Qed.


Lemma dsub_union_inversion : forall Ψ S1 S2 T1,
  Ψ ⊢ typ_union S1 S2 <: T1 ->
  Ψ ⊢ S1 <: T1 /\ Ψ ⊢ S2 <: T1.
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


Lemma dsub_intersection_inversion : forall Ψ S1 T1 T2,
  Ψ ⊢ S1 <: typ_intersection T1 T2 ->
  Ψ ⊢ S1 <: T1 /\ Ψ ⊢ S1 <: T2.
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


Theorem dsub_unit_all_false: forall Ψ T,
  Ψ ⊢ typ_all T ->
  Ψ ⊢ typ_unit <: typ_all T ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem dsub_top_all_false: forall Ψ T,
  Ψ ⊢ typ_all T ->
  Ψ ⊢ typ_top <: typ_all T ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem dsub_top_fv_false: forall Ψ X T,
  ds_in X T ->
  Ψ ⊢ typ_top <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.

Theorem dsub_unit_fv_false: forall Ψ X T,
  ds_in X T ->
  Ψ ⊢ typ_unit <: T ->
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
  d_sub_tvar_open_inv X2 ({` X2 /ᵗ X1} T1).
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


Lemma d_mono_type_order_0 : forall Ψ A,
  d_mono_typ Ψ A -> d_typ_order A = 0.
Proof.
  intros; induction H; simpl; auto.
  - rewrite IHd_mono_typ1. rewrite IHd_mono_typ2. auto.
  - rewrite IHd_mono_typ1. rewrite IHd_mono_typ2. auto.
  - rewrite IHd_mono_typ1. rewrite IHd_mono_typ2. auto.
Qed.

Lemma d_open_rec_mono_same_order : forall Ψ T1 T2 n,
  d_mono_typ Ψ T2 ->
  d_typ_order (open_typ_wrt_typ_rec n T2 T1) = d_typ_order T1.
Proof.
  induction T1; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; auto. eapply d_mono_type_order_0; eauto.
    + auto.
Qed.

Lemma d_open_rec_tvar_same_order : forall A X n,
  d_typ_order (open_typ_wrt_typ_rec n (typ_var_f X) A) = d_typ_order A.
Proof.
  induction A; simpl; intros; auto.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; auto.
    + auto.
Qed.

Lemma d_open_mono_same_order : forall Ψ A T,
  d_mono_typ Ψ T ->
  d_typ_order (A ^^ᵈ T) = d_typ_order A.
Proof.
  intros. unfold open_typ_wrt_typ. eapply d_open_rec_mono_same_order; eauto.
Qed.


Lemma d_open_svar_same_order : forall A X,
  d_typ_order (A ^ᵈ X) = d_typ_order A.
Proof.
  intros. unfold open_typ_wrt_typ. apply d_open_rec_tvar_same_order; auto.
Qed.


Theorem d_sub_tvar_inv_nested_all_false: forall L1 L2 L3 T1 S1,
  (forall X : atom, X `notin` L1 -> d_sub_tvar_open_inv X (open_typ_wrt_typ_rec 1 S1 T1 ^ᵈ X)) ->
  (forall X : atom, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 ` X T1))) ->
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
    assert (forall X : atom, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 ` X T1_1))).
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
        replace (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X) with ({` X /ᵗ x}(open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ x)).
        now apply d_sub_tvar_open_inv_subst_var.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
        rewrite (subst_tvar_in_typ_fresh_eq); auto. simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X x x); auto. contradiction.
      - right. intros. inst_cofinites_with X.
        assert (d_sub_tvar_open_inv x (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ x)) by auto.
        replace (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ X) with ({` X /ᵗ x}(open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ x)).
        now apply d_sub_tvar_open_inv_subst_var.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ; auto.
        rewrite (subst_tvar_in_typ_fresh_eq); auto. simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X x x); auto. contradiction.
    }
    inversion H3.
    + assert (forall X : atom, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 ` X T1_1))).
      { intros. inst_cofinites_with X. dependent destruction H0.
        eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
        inversion H0. auto.
      }
      assert  (forall X, X `notin` L3 -> ds_in X (open_typ_wrt_typ_rec 1 S1 T1_1 ^ᵈ X)).
      { intros. inst_cofinites_with X. inversion H1; auto.
      }
      auto.
    + assert (forall X, X `notin` L2 -> ds_in X (typ_all (open_typ_wrt_typ_rec 1 ` X T1_2))).
      { intros. inst_cofinites_with X. dependent destruction H0.
        eapply dsin_all with (L:=L). intros. inst_cofinites_with Y.
        inversion H0. auto.
      }
      assert  (forall X, X `notin` L3 -> ds_in X (open_typ_wrt_typ_rec 1 S1 T1_2 ^ᵈ X)).
      { intros. inst_cofinites_with X. inversion H1; auto.
      }
      auto.
Qed.


Theorem d_sub_tvar_ind_open_inv_complete: forall n1 n2 Ψ S1 T1 X L,
    d_typ_order (T1 ^^ᵈ S1) < n1 ->
    d_typ_size (T1 ^^ᵈ S1) < n2 ->
    Ψ ⊢ T1 ^^ᵈ S1 <: ` X ->
    (forall X, X `notin` L -> ds_in X (T1 ^ᵈ X)) ->
    d_mono_typ Ψ S1 ->
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


Lemma d_sub_tvar_inv_subst: forall A X T,
    d_sub_tvar_inv A -> lc_typ T -> d_sub_tvar_inv ({T /ᵗ X} A).
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
| d_ordmono__tvar : forall Ψ X,
    d_mono_typ Ψ (typ_var_f X) ->
    d_ord_mono Ψ (typ_var_f X)
| d_ordmono__unit : forall Ψ, d_ord_mono Ψ typ_unit
| d_ordmono__arr : forall Ψ T1 T2,
    d_mono_typ Ψ T1 ->
    d_mono_typ Ψ T2 ->
    d_ord_mono Ψ (typ_arrow T1 T2)
.

Lemma d_ord_mono_neq_intersection: forall Ψ T1,
  d_ord_mono Ψ T1 ->
  neq_intersection T1.
Proof.
  intros. induction H; auto.
  econstructor; eapply d_mono_typ_lc; eauto.
Qed.

Lemma d_ord_mono_neq_union: forall Ψ T1,
  d_ord_mono Ψ T1 ->
  neq_union T1.
Proof.
  intros. induction H; auto.
  econstructor; eapply d_mono_typ_lc; eauto.
Qed.

Inductive d_mono_ordiu : denv -> typ -> Prop :=
| d_monoord__base : forall Ψ T1,
    d_ord_mono Ψ T1 ->
    d_mono_ordiu Ψ T1
| d_monoord__union : forall Ψ T1 T2,
    d_mono_ordiu Ψ T1 ->
    d_mono_ordiu Ψ T2 ->
    d_mono_ordiu Ψ (typ_union T1 T2)
| d_monoord__inter : forall Ψ T1 T2,
    d_mono_ordiu Ψ T1 ->
    d_mono_ordiu Ψ T2 ->
    d_mono_ordiu Ψ (typ_intersection T1 T2).


Lemma d_mono_ordiu_complete : forall Ψ T1,
  d_mono_typ Ψ T1 -> d_mono_ordiu Ψ T1.
Proof.
  intros. induction H; try solve [constructor; constructor].
  - econstructor. econstructor. eapply d_mono_typ__tvar; auto.
  - apply d_monoord__base. apply d_ordmono__arr; auto.
  - apply d_monoord__inter; auto.
  - apply d_monoord__union; auto.
Qed.


Lemma d_ord_mono_sound: forall Ψ A1,
  d_ord_mono Ψ A1 -> d_mono_typ Ψ A1.
Proof.
  intros. induction H; auto.
Qed.

Lemma d_mono_ordiu_sound : forall Ψ A1,
  d_mono_ordiu Ψ A1 -> d_mono_typ Ψ A1.
Proof.
  intros. induction H; auto.
  - apply d_ord_mono_sound. auto.
Qed.


Theorem d_sub_tvar_ind_open_subst : forall Ψ F X A B,
  ⊢ F ++ (X ~ dbind_tvar_empty) ++ Ψ ->
  d_sub_tvar_open_inv X A ->
  d_mono_typ Ψ B ->
  (X ~ dbind_tvar_empty) ++ Ψ ⊢ A ->
  Ψ ⊢ B ->
  map (subst_tvar_in_dbind B X) F ++ Ψ ⊢ ({B /ᵗ X} A) <: B.
Proof with auto with subtyping.
  intros * Hwfenv H. induction H; intros.
  - simpl. destruct (X == X).
    + apply dsub_refl; auto...
      replace B with ({B /ᵗ X} ` X) at 2.
      apply d_wft_typ_subst; auto.
      simpl. destruct (X == X); auto. contradiction.
    + contradiction.
  - simpl. dependent destruction H2. constructor; auto.
  - simpl. dependent destruction H1. constructor; auto.
    apply d_wft_typ_subst; auto.
    apply dwf_typ_weakening with (Ψ3:=nil); auto.
  - simpl. dependent destruction H1. apply d_sub__intersection3; auto.
    apply d_wft_typ_subst; auto.
    apply dwf_typ_weakening with (Ψ3:=nil); auto.
Qed.


(* Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end. *)
Hint Resolve dwf_typ_weakening : weakening.

Theorem d_sub_weakening: forall Ψ1 Ψ2 Ψ3 A B,
  Ψ3 ++ Ψ1 ⊢ A <: B ->
  ⊢ Ψ3 ++ Ψ2 ++ Ψ1 ->
  Ψ3 ++ Ψ2 ++ Ψ1 ⊢ A <: B.
Proof with auto with subtyping weakening.
  intros Ψ1 Ψ2 Ψ3 A B Hsub Hwf.
  dependent induction Hsub;
    try solve [simpl in *];
    try solve [eapply dwf_typ_weakening with (Ψ2 := Ψ2) in H0; auto]; auto.
  - apply d_sub__all with (L :=  L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1)); intros x Fr; inst_cofinites_with x; auto...
    eapply H2 with (Ψ1 := Ψ1) (Ψ3 := (x, ▪) :: Ψ3); simpl; auto.
    constructor; auto.
  - apply d_sub__alll with (T := T) (L :=  L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1)); auto...
    eauto using d_mono_typ_weakening.
  - apply d_sub__intersection2; eauto...
  - apply d_sub__intersection3; auto...
  - apply d_sub__union1; auto...
  - apply d_sub__union2; auto...
Qed.


Corollary d_sub_weakening_cons: forall Ψ x b A B,
  Ψ ⊢ A <: B ->
  ⊢ x ~ b ++ Ψ ->
  x ~ b ++ Ψ ⊢ A <: B.
Proof.
  intros.
  rewrite_env (nil ++ (x ~ b) ++ Ψ).
  eapply d_sub_weakening; eauto.
Qed.

(* Theorem  d_sub_strenthening: forall Ψ F G S1 T1,
  F ++ G ++ Ψ ⊢ S1 <: T1 ->
  F ++ Ψ ⊢ S1 ->
  F ++ Ψ ⊢ T1 ->
  F ++ Ψ ⊢ S1 <: T1.
Proof.
  introv HS HWS HWT.
  remember (F++G++Ψ) as Ψ'.
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


Theorem d_sub_tvar_ind_sub_all : forall Ψ A B,
  ⊢ Ψ ->
  d_sub_tvar_inv (typ_all A) ->
  Ψ ⊢ typ_all A ->
  d_mono_typ Ψ B ->
  Ψ ⊢ B ->
  Ψ ⊢ typ_all A <: B.
Proof.
  intros * Hwfenv H Hwft Hmono Hwft2.
  specialize (d_mono_ordiu_complete _ _ Hmono). intros.
  induction H0.
  - dependent destruction H.
    dependent destruction Hwft.
    eapply d_sub__alll with (L:=L `union` L0) (T:=T1).
    + eapply d_mono_typ_neq_all; eauto.
    + eapply d_ord_mono_neq_intersection; eauto.
    + eapply d_ord_mono_neq_union; eauto.
    + auto.
    + auto.
    + inst_cofinites_by (L `union` L0 `union` ftvar_in_typ A `union` dom Ψ) using_name X.
      apply d_sub_tvar_ind_open_subst with (Ψ:= Ψ) (B:=T1) (F:=nil) in H; auto.
      * rewrite typ_subst_open_var in H; eauto.
      * simpl. constructor; auto.
  - inversion Hmono. inversion Hwft2. auto.
  - inversion Hmono. inversion Hwft2. auto.
Qed.


Theorem  d_sub_subst_mono : forall Ψ1 X Ψ2 A B T,
  ⊢ Ψ2 ++ (X ~ dbind_tvar_empty) ++ Ψ1 ->
  Ψ2 ++ (X ~ dbind_tvar_empty) ++ Ψ1 ⊢ A <: B ->
  Ψ1 ⊢ T ->
  d_mono_typ Ψ1 T ->
  map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1 ⊢ {T /ᵗ X} A <: {T /ᵗ X} B.
Proof with eauto with subtyping.
  intros Ψ X F A1 B1 T1 Hwfenv Hsub Hwft Hmono.
  dependent induction Hsub; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl; auto...
  - simpl. eapply d_sub__all with (L:=L `union` singleton X `union` dom Ψ `union` dom F); intros X0 Hfr; inst_cofinites_with X.
    + rewrite typ_subst_open_comm; auto...
      applys* ftv_sin_typ_subst_inv.
    + rewrite typ_subst_open_comm; auto...
      applys* ftv_sin_typ_subst_inv.
    + inst_cofinites_with X0. repeat rewrite typ_subst_open_comm; eauto...
      replace (X0 ~ dbind_stvar_empty ++ map (subst_tvar_in_dbind T1 X) F ++ Ψ) with
      (map (subst_tvar_in_dbind T1 X) (X0 ~ dbind_stvar_empty ++ F) ++ Ψ) by auto.
      eapply H2; auto... simpl. constructor; eauto.
  - destruct B.
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={T1 /ᵗ X} T); auto...
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={T1 /ᵗ X} T); eauto...
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={T1 /ᵗ X} T); auto...
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]]. inversion HwftT.
    + simpl. case_if.
      2: { eapply d_sub__alll with (L:=L `union` singleton X) (T:={T1 /ᵗ X} T); auto...
           * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
             apply ftv_sin_typ_subst_inv; auto...
           * apply d_mono_typ_subst_mono_mono; auto.
           * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
             forwards*: IHHsub. simpl in H4. case_if*.
      }
      apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]].
      apply d_sub_tvar_ind_sub_all.
      -- eapply d_wf_env_subst_tvar_typ; auto.
      -- replace (typ_all ({T1 /ᵗ X} A)) with ({T1 /ᵗ X} (typ_all A)) by auto.
         apply d_sub_tvar_inv_subst. eapply d_sub_tvar_ind_open_inv_complete; eauto.
         eapply d_wf_typ_lc_typ; eauto.
      -- replace (typ_all ({T1 /ᵗ X} A)) with ({T1 /ᵗ X} (typ_all A))  by auto.
         apply d_wft_typ_subst; auto.
         inst_cofinites_for d_wf_typ__all.
         ++ auto.
         ++ intros. eapply dwf_typ_open_inv with (X:=X1) (T1:=T); eauto.
            rewrite subst_tvar_in_typ_open_typ_wrt_typ; eauto.
            simpl. rewrite (subst_tvar_in_typ_fresh_eq); eauto.
            unfold eq_dec. destruct (EqDec_eq_of_X X1 X1); eauto.
            ** apply dwf_typ_weakening_cons; auto.
            ** contradiction.
      -- unfold eq_dec. destruct (EqDec_eq_of_X X0 X); eauto.
         ++ applys* d_mono_typ_weaken_head.
         ++ contradiction.
      -- applys* dwf_typ_weaken_head.
    + apply d_sub_dwft in Hsub as Hwft1. destruct Hwft1 as [_ [HwftS HwftT]]. inversion HwftT.
      eapply d_sub__alll with (L:=L `union` singleton X) (T:={T1 /ᵗ X} T); eauto...
      1-3: simpl; econstructor; applys* lc_typ_subst.
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={T1 /ᵗ X} T); eauto...
      * simpl. dependent destruction H.
      * simpl. dependent destruction H.
      * simpl. dependent destruction H.
      * intros. inst_cofinites_with X0. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto...
    + inversion H1.
    + inversion H0.
Qed.

Hint Resolve d_wft_typ_subst_stvar : subtyping.
Hint Resolve d_wf_env_subst_stvar_typ : subtyping.
(* Hint Resolve d_subst_stv_lc_typ : lngen. *)

Lemma dneq_all_intersection_union_subst_stv : forall T1 T2 X,
  lc_typ T1 -> lc_typ T2 ->
  neq_all T1 -> neq_intersection T1 -> neq_union T1 ->
  (neq_all ({T2 /ᵗ X} T1) /\
   neq_intersection ({T2 /ᵗ X} T1) /\
   neq_union ({T2 /ᵗ X} T1)) \/ T1 = ` X.
Proof with eauto with lngen.
  intros. destruct T1; simpl in *; auto...
  - destruct (X0 == X); subst; auto.
  - dependent destruction H. left. split.
    eauto with lngen...
    constructor; eauto with lngen...
  - inversion H1.
  - inversion H3.
  - inversion H2.
Qed.

Theorem d_sub_open_mono_stvar_false: forall n1 n2 Ψ A T X L,
    d_typ_order (A ^^ᵈ T) < n1 ->
    d_typ_size (A ^^ᵈ T) < n2 ->
    X ~ ▪ ∈ Ψ ->
    Ψ ⊢ A ^^ᵈ T <: typ_var_f X ->
    (forall X, X `notin` L -> ds_in X (A ^ᵈ X)) ->
    d_mono_typ Ψ T ->
    False.
Proof.
  intro n1. induction n1.
  - intros. inversion H.
  - intros n2. induction n2.
    + intros. inversion H0.
    + intros. dependent destruction H2; rename x into Heq.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- inst_cofinites_by L using_name X. inversion H4.
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in *.
              subst. inversion H5.
           ++ unfold open_typ_wrt_typ in Heq. simpl in *.
              inversion Heq.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
          ++ unfold open_typ_wrt_typ in Heq. simpl in *.
            subst. dependent destruction H5. applys* binds_two_thing_false X.
          ++ unfold open_typ_wrt_typ in Heq. simpl in *.
            inversion Heq.
        -- inst_cofinites_by (L `union` singleton X0) using_name X. inversion H4.
           subst. solve_notin.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
          ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H9.
          ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq.
           eapply IHn1; eauto. erewrite d_open_mono_same_order; eauto. lia.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H5.
              eapply d_sub_mono_stvar_false in H2; auto.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H4; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H5.
              apply d_sub_mono_stvar_false in H2; auto.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H4; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H4.
              apply d_sub_mono_stvar_false in H2_; auto.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H3; auto.
Qed.

Theorem d_mono_notin_stvar : forall Ψ2 Ψ1 A X,
  Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1 ⊢ A ->
  d_mono_typ (Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1) A ->
  ⊢ (Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1) ->
  X `notin` ftvar_in_typ A.
Proof.
  intros. dependent induction H0; simpl in *; auto.
  - case_eq (X0 == X); intros; subst*; try solve_notin.
    assert (X ~ ▪ ∈ (Ψ2 ++ (X, ▪) :: Ψ1)) by eauto.
    exfalso. forwards*: binds_two_thing_false X.
  - dependent destruction H; auto... apply notin_union; eauto.
  - dependent destruction H; auto... apply notin_union; eauto.
  - dependent destruction H; auto... apply notin_union; eauto.
Qed.

(* bookmark *)

Theorem d_sub_subst_stvar : forall Ψ1 X Ψ2 A B T,
  Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1 ⊢ A <: B ->
  Ψ1 ⊢ T ->
  map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1 ⊢ {T /ᵗ X} A <: {T /ᵗ X} B.
Proof with subst; eauto using dwf_typ_weaken_head with subtyping.
  intros. dependent induction H; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl; auto...
  - simpl. inst_cofinites_for d_sub__all; intros X1 Hfr; inst_cofinites_with X1.
    + rewrite typ_subst_open_comm; auto...
      apply ftv_sin_typ_subst_inv; auto...
    + rewrite typ_subst_open_comm; auto...
      apply ftv_sin_typ_subst_inv; auto...
    + repeat rewrite typ_subst_open_comm; eauto...
      rewrite_env (map (subst_tvar_in_dbind T X) (X1 ~ ▪ ++ Ψ2) ++ Ψ1).
      eapply H2; auto...
  - simpl. destruct (dneq_all_intersection_union_subst_stv B T X) as [[? [? ?]] | ?]; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={T /ᵗ X} T0); auto...
      * intros. rewrite typ_subst_open_comm; auto...
        apply ftv_sin_typ_subst_inv; auto...
      * applys* d_mono_typ_subst_stvar... eauto using d_sub_dwft_0.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto using dwf_typ_dlc_type.
    + eapply d_sub_open_mono_stvar_false in H3; eauto. contradiction.
  - simpl. apply d_sub__intersection2. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__intersection3. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__union1. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__union2. eauto with subtyping.
    apply d_wft_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
Qed.


Inductive d_sub_size : denv -> typ -> typ -> nat -> Prop :=    (* defn d_sub *)
 | d_subs__top : forall (Ψ:denv) (A1:typ) (n:nat),
     d_wf_env Ψ ->
     d_wf_typ Ψ A1 ->
     d_sub_size Ψ A1 typ_top n
 | d_subs__bot : forall (Ψ:denv) (B1:typ) (n:nat),
     d_wf_env Ψ ->
     d_wf_typ Ψ B1 ->
     d_sub_size Ψ typ_bot B1 n
 | d_subs__unit : forall (Ψ:denv) (n:nat),
     d_wf_env Ψ ->
     d_sub_size Ψ typ_unit typ_unit n
 | d_subs__tvar : forall (Ψ:denv) (X:typvar) (n:nat),
     d_wf_env Ψ ->
     d_wf_typ Ψ (typ_var_f X) ->
     d_sub_size Ψ (typ_var_f X) (typ_var_f X) n
 | d_subs__arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ) (n1 n2:nat),
     d_sub_size Ψ B1 A1 n1 ->
     d_sub_size Ψ A2 B2 n2 ->
     d_sub_size Ψ (typ_arrow A1 A2) (typ_arrow B1 B2) (S (n1 + n2))
 | d_subs__all : forall (L:vars) (Ψ:denv) (A1 B1:typ) (n:nat),
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ B1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A1 (typ_var_f X) )   ( open_typ_wrt_typ B1 (typ_var_f X) )  n )  ->
      d_sub_size Ψ (typ_all A1) (typ_all B1) (S n)
 | d_subs__alll : forall (L:vars) (Ψ:denv) (A1 B1 T1:typ) (n:nat),
     neq_all B1 ->
     neq_intersection B1 ->
     neq_union B1 ->
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
     d_mono_typ Ψ T1 ->
     d_sub_size Ψ  (open_typ_wrt_typ  A1   T1 )  B1 n ->
     d_sub_size Ψ (typ_all A1) B1 (S n)
 | d_subs__intersection1 : forall (Ψ:denv) (A1 B1 B2:typ) (n1 n2:nat),
     d_sub_size Ψ A1 B1 n1 ->
     d_sub_size Ψ A1 B2 n2 ->
     d_sub_size Ψ A1 (typ_intersection B1 B2) (S (n1 + n2))
 | d_subs__intersection2 : forall (Ψ:denv) (A1 A2 B1:typ) (n:nat),
     d_sub_size Ψ A1 B1 n ->
     d_wf_typ Ψ A2 ->
     d_sub_size Ψ (typ_intersection A1 A2) B1 (S n)
 | d_subs__intersection3 : forall (Ψ:denv) (A1 A2 B1:typ) (n:nat),
     d_sub_size Ψ A2 B1 n ->
     d_wf_typ Ψ A1 ->
     d_sub_size Ψ (typ_intersection A1 A2) B1 (S n)
 | d_subs__union1 : forall (Ψ:denv) (A1 B1 B2:typ) (n:nat),
     d_sub_size Ψ A1 B1 n ->
     d_wf_typ Ψ B2 ->
     d_sub_size Ψ A1 (typ_union B1 B2) (S n)
 | d_subs__union2 : forall (Ψ:denv) (A1 B1 B2:typ) (n:nat),
     d_sub_size Ψ A1 B2 n ->
     d_wf_typ Ψ B1 ->
     d_sub_size Ψ A1 (typ_union B1 B2) (S n)
 | d_subs__union3 : forall (Ψ:denv) (A1 A2 B1:typ) (n1 n2:nat),
     d_sub_size Ψ A1 B1 n1 ->
     d_sub_size Ψ A2 B1 n2 ->
     d_sub_size Ψ (typ_union A1 A2) B1 (S (n1 + n2)).
     
Notation "Ψ ⊢ S1 <: T1 | n" :=
  (d_sub_size Ψ S1 T1 n)
    (at level 65, S1 at next level, T1 at next level, no associativity) : type_scope.

Theorem d_sub_size_sound : forall Ψ A1 B1 n,
    Ψ ⊢ A1 <: B1 | n -> Ψ ⊢ A1 <: B1.
Proof.
  intros. induction H; eauto.
Qed.

Hint Constructors d_sub_size : sub.

Lemma d_sub_dwft_sized : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> ⊢ Ψ /\ Ψ ⊢ A /\ Ψ ⊢ B.
Proof.
  intros. applys d_sub_dwft. applys* d_sub_size_sound.
Qed.

Corollary d_sub_dwft_sized_0 : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> ⊢ Ψ.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

Corollary d_sub_dwft_sized_1 : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> Ψ ⊢ A.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

Corollary d_sub_dwft_sized_2 : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> Ψ ⊢ B.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

#[local] Hint Resolve d_sub_dwft_sized_0 d_sub_dwft_sized_1 d_sub_dwft_sized_2 : core.


Lemma d_sub_size_rename_stvar : forall Ψ1 Ψ2 X Y A B n,
  Ψ2 ++ X ~ ▪ ++ Ψ1 ⊢ A <: B | n ->
      Y ∉ (dom Ψ1 `union` dom Ψ2) ->
      (map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2) ++ Y ~ ▪ ++ Ψ1 ⊢
        {typ_var_f Y /ᵗ X} A <: {typ_var_f Y /ᵗ X} B | n.
Proof with (simpl in *; eauto using d_wf_env_subst_tvar_typ with sub).
  intros * HS HN.
  case_eq (Y == X); intros.
  1: { subst. rewrite* subst_same_tvar_map_id.
       repeat rewrite* subst_same_tvar_typ_id. } clear H.

  gen Y.
  inductions HS; intros...
  - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((Ψ2 ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ▪ ++ Ψ1)...
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((Ψ2 ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ▪ ++ Ψ1)...
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((Ψ2 ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ▪ ++ Ψ1)...
    solve_notin.
  (* - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((F ++ (X, ▪) :: nil ) ++ [(Y, ▪)] ++ Ψ).
    applys d_wf_env_weaken_stvar.
    rewrite_env (F ++ X ~ ▪ ++ Ψ)...
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
    + forwards~: H2 SZ Ψ1 ((SZ, ▪) :: Ψ2)...
      repeat rewrite typ_subst_open_comm...
  - pick fresh SZ and apply d_subs__alll.
    6: forwards* H4: IHHS;
    rewrite subst_tvar_in_typ_open_typ_wrt_typ in H4; eauto using dwf_typ_dlc_type.
    1-3: auto...
    + rewrite typ_subst_open_comm...
      applys~ ftv_sin_typ_subst_inv.
    + applys d_mono_typ_subst_stvar.
      * rewrite_env ((Ψ2 ++ X ~ ▪) ++ Y ~ ▪ ++ Ψ1).
        applys* d_mono_typ_weakening. rewrite_env (Ψ2 ++ (X, ▪) :: Ψ1)...
      * rewrite_env ((Ψ2 ++ X ~ ▪) ++ Y ~ ▪ ++ Ψ1).
        applys d_wf_env_weaken_stvar.
        forwards: d_sub_dwft_sized_0 HS. rewrite_env (Ψ2 ++ (X, ▪) :: Ψ1)...
        solve_notin.
      * now eauto.
  - applys d_subs__intersection2; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__intersection3; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__union1; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__union2; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
    Unshelve. all: eauto.
Qed.

Corollary d_sub_size_rename : forall n X Y Ψ1 Ψ2 A B,
    X `notin`  (ftvar_in_typ A `union` ftvar_in_typ B) ->
    Y `notin` ((dom Ψ1) `union` (dom Ψ2)) ->
    Ψ2 ++ X ~ ▪ ++ Ψ1 ⊢ A ^^ᵈ typ_var_f X <: B ^^ᵈ typ_var_f X | n ->
    map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2 ++ Y ~ ▪ ++ Ψ1 ⊢ A ^^ᵈ typ_var_f Y <: B ^^ᵈ typ_var_f Y | n.
Proof with eauto.
  intros.
  forwards: d_sub_size_rename_stvar Y H1. solve_notin.
  rewrite 2 subst_tvar_in_typ_open_typ_wrt_typ in H2...
  simpl in H2. case_if.
  rewrite 2 subst_tvar_in_typ_fresh_eq in H2...
Qed.

Lemma d_sub_size_complete : forall Ψ A B,
  Ψ ⊢ A <: B -> exists n, Ψ ⊢ A <: B | n.
Proof with eauto with sub.
  intros. induction H; eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
  - pick fresh X.
    destruct (H2 X) as [n]. solve_notin.
    exists (S n).
    eapply d_subs__all with (L:=L `union` ftvar_in_typ A `union` ftvar_in_typ B `union` (dom Ψ)); intros; eauto.
    + rewrite_env (nil ++ X0 ~ ▪ ++ Ψ). rewrite_env (nil ++ X ~ ▪ ++ Ψ) in H3.
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


Lemma d_sub_size_more: forall Ψ A B n,
  Ψ ⊢ A <: B | n -> forall n', n' >= n -> Ψ ⊢ A <: B | n'.
Proof with auto with trans.
  intros Ψ S1 T1 n H.
  dependent induction H; intros; auto...
  - apply nat_split in H1.
    destruct H1 as [n1' [n2' [Heq [Hgtn1 Hgtn2]]]].
    rewrite Heq. eauto...
  - apply nat_suc in H3.
    destruct H3 as [n1' [Heq Hgtn1]].
    rewrite Heq. econstructor; eauto...
  - apply nat_suc in H5.
    destruct H5 as [n1' [Heq Hgtn1]].
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


Lemma d_sub_size_union_inv: forall Ψ A1 A2 B n,
  Ψ ⊢ (typ_union A1 A2) <: B | n -> Ψ ⊢ A1 <: B | n /\ Ψ ⊢ A2 <: B | n.
Proof with auto with trans.
  intros.
  dependent induction H.
  - inversion H0. split; auto...
  - specialize (IHd_sub_size1 A1 A2 (eq_refl _)).
    specialize (IHd_sub_size2 A1 A2 (eq_refl _)).
    split; constructor; intuition.
  - specialize (IHd_sub_size A1 A2 (eq_refl _)).
    split; apply d_subs__union1; intuition.
  - specialize (IHd_sub_size A1 A2 (eq_refl _)).
    split; apply d_subs__union2; intuition.
  - split.
    eapply d_sub_size_more; eauto. lia.
    eapply d_sub_size_more; eauto. lia.
Qed.



Theorem d_sub_size_subst_stvar : forall Ψ1 Ψ2 X A B T n,
  Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1 ⊢ A <: B | n ->
  Ψ1 ⊢ T ->
  exists n', map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1 ⊢ {T /ᵗ X} A <: {T /ᵗ X} B | n'.
Proof.
  intros.
  apply d_sub_size_sound in H.
  apply d_sub_subst_stvar with (T:=T) in H; auto.
  apply d_sub_size_complete in H. auto.
Qed.

Inductive d_ord : typ -> Prop :=
| d_ord__tvar : forall X, d_ord (typ_var_f X)
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

Lemma d_wft_ord_complete: forall Ψ A,
  Ψ ⊢ A -> d_wft_ord A.
Proof with auto with wf.
  intros. induction H; eauto...
Qed.

Theorem d_sub_mono_bot_false : forall Ψ A,
  d_mono_typ Ψ A ->
  Ψ ⊢ A <: typ_bot ->
  False.
Proof.
  intros. induction H; try solve [(dependent destruction H0); auto].
Qed.



Theorem d_sub_open_mono_bot_false: forall n1 n2 Ψ A T L,
    d_typ_order (A ^^ᵈ T) < n1 ->
    d_typ_size (A ^^ᵈ T) < n2 ->
    Ψ ⊢ A ^^ᵈ T <: typ_bot ->
    (forall X, X `notin` L -> ds_in X (A ^ᵈ X)) ->
    d_mono_typ Ψ T ->
    False.
Proof.
  intro n1. induction n1.
  - intros. inversion H.
  - intros n2. induction n2.
    + intros. inversion H0.
    + intros. dependent destruction H1; rename x into Heq.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- inst_cofinites_by L. inversion H3.
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H4.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
      * destruct A; simpl in *; try solve [ inversion Heq].
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H8.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
        -- inversion Heq. subst. eapply IHn1; eauto.
           erewrite d_open_mono_same_order; eauto. lia.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H4.
              eapply d_sub_mono_bot_false with (A:=A1); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H4.
              eapply d_sub_mono_bot_false with (A:=A2); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
              eapply d_sub_mono_bot_false with (A:=A1); eauto.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H2; auto.
Qed.



Ltac solve_trans_forall_B_intersection_impl T1 T2:=
  match goal with
   | H1 : ?Ψ ⊢ ?T <: T1 | ?n1 |- _ =>
      match goal with
      | H2 : ?Ψ ⊢ ?T <: T2 | ?n2 |- _ =>
        apply d_sub_size_more with (n':=S(n1+n2)) in H1; auto with trans;
        apply d_sub_size_more with (n':=S(n1+n2)) in H2; auto with trans
      end
   end.

Ltac solve_trans_forall_B_union_impl T1 T2:=
  match goal with
    | H1 : ?Ψ ⊢ ?T <: T1 | ?n1 |- _ =>
      apply d_sub_size_more with (n':=S n1) in H1; auto with trans
    | H2 : ?Ψ ⊢ ?T <: T2 | ?n1 |- _ =>
      apply d_sub_size_more with (n':=S n1) in H2; auto with trans
  end.

Ltac solve_trans_forall_B_iu :=
  match goal with
   | H : ?Ψ ⊢ ?T <: ?C | ?n |- ?Ψ ⊢ ?B <: ?D => match D with
      | typ_intersection ?D1 ?D2 => dependent destruction H; auto with trans; solve_trans_forall_B_intersection_impl D1 D2
      | typ_union ?D1 ?D2 => dependent destruction H; auto with trans; solve_trans_forall_B_union_impl D1 D2
      | _ => idtac
   end
  end.

Ltac solve_trans_forall_B_C :=
   match goal with
   | H : ?Ψ ⊢ ?T <: ?C | ?n |- ?Ψ ⊢ ?B <: ?C => match T with
      (* the following case of B is impossible. solve them separately *)
      | typ_bot => idtac
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


Lemma d_sub_size_transitivity : forall n_d_typ_order n_dsub_size Ψ A B C n1 n2 ,
  d_typ_order B < n_d_typ_order ->
  n1 + n2 < n_dsub_size ->
  Ψ ⊢ A <: B | n1 -> Ψ ⊢ B <: C | n2 -> Ψ ⊢ A <: C.
Proof with auto with trans.
  induction n_d_typ_order; induction n_dsub_size; intros * Horder Hsize Hsub1 Hsub2.
  - inversion Horder.
  - inversion Horder.
  - inversion Hsize.
  - dependent destruction Hsub1...
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (B:=typ_top) (n1:=n2); eauto...
        eapply IHn_dsub_size with (B:=typ_top) (n1:=n1); eauto...
      * simpl in H. eapply d_sub__union1.
        eapply IHn_dsub_size with (B:=typ_top) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub__union2.
        eapply IHn_dsub_size with (B:=typ_top) (n1:=n); eauto...
        auto.
    + apply d_sub_size_sound in Hsub2.
      apply d_sub_dwft in Hsub2; auto.
      eapply d_sub__bot; intuition.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (B:=typ_unit) (n1:=n2); eauto...
        eapply IHn_dsub_size with (B:=typ_unit) (n1:=n1); eauto...
      * simpl in H. eapply d_sub__union1.
        eapply IHn_dsub_size with (B:=typ_unit) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub__union2.
        eapply IHn_dsub_size with (B:=typ_unit) (n1:=n); eauto...
        auto.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_dsub_size with (B:=` X) (n1:=n2); eauto...
        eapply IHn_dsub_size with (B:=` X) (n1:=n1); eauto...
      * simpl in H. eapply d_sub__union1.
        eapply IHn_dsub_size with (B:=` X) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub__union2.
        eapply IHn_dsub_size with (B:=` X) (n1:=n); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_size_sound in Hsub1_2.
        apply d_sub_dwft in Hsub1_1. apply d_sub_dwft in Hsub1_2. econstructor; intuition.
      * econstructor.
        eapply IHn_dsub_size with (B:=B1); eauto...
        eapply IHn_dsub_size with (B:=B2); eauto...
      * econstructor.
        eapply IHn_dsub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
        eapply IHn_dsub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
      * apply d_sub__union1.
        eapply IHn_dsub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
        auto.
      * apply d_sub__union2.
        eapply IHn_dsub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor...
        pick fresh Y and apply d_wf_typ__all.
        ** forwards: H Y...
        ** forwards: H1 Y...
           forwards: d_sub_dwft_sized_1 H4.
           rewrite_env (nil ++ Y ~ ▪ ++ Ψ) in H4.
           rewrite_env (nil ++ Y ~ ▪ ++ Ψ) in H5.
           forwards: d_wf_typ_subst_stvar_tvar H5.
           simpl in H6. auto.
      * eapply d_sub__all with (L:=L `union` L0 `union` dom Ψ); auto.
        intros. inst_cofinites_with X.
        eapply IHn_d_typ_order with (B:= B1 ^ᵈ X); eauto...
        -- simpl in *. rewrite d_open_svar_same_order...
      * pick fresh Y and apply d_sub__alll. 5: applys H6. all: eauto.
        ** pick fresh X. inst_cofinites_with X.
        replace Ψ with (map (subst_tvar_in_dbind T1 X) nil ++ Ψ) by auto.
        rewrite_env  (nil ++ (X, ▪) :: Ψ) in H1.
        eapply d_sub_size_subst_stvar with (T:=T1) in H1; simpl; eauto.
        destruct H1 as [n' Hsub].
        eapply IHn_d_typ_order with (B:=B1 ^^ᵈ T1) (n1:=n'); eauto...
        erewrite d_open_mono_same_order; eauto. now lia.
        simpl in Hsub. auto. simpl.
        rewrite 2 subst_tvar_in_typ_open_typ_wrt_typ in Hsub... simpl in Hsub.
        unfold eq_dec in Hsub. destruct (EqDec_eq_of_X X X) in Hsub.
        rewrite (subst_tvar_in_typ_fresh_eq A1) in Hsub...
        rewrite (subst_tvar_in_typ_fresh_eq B1) in Hsub...
        contradiction.
        all: eauto using d_mono_typ_lc, d_mono_typ_d_wf_typ.
      * eapply d_sub__intersection1.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n1); eauto...
           econstructor; eauto.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n2); eauto...
           econstructor; eauto.
      * eapply d_sub__union1.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n0); eauto...
           econstructor; eauto.
        -- auto.
      * eapply d_sub__union2.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n0); eauto...
           econstructor; eauto.
        -- auto.
    + simpl in *. assert (Ψ ⊢ B1) as Hwft1 by applys* d_sub_dwft_sized_1.
      dependent destruction Hwft1; solve_trans_forall_B_C.
      (* solve_trans_forall_B_C. *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ ▫ ++ Ψ).
           applys* d_wf_typ_open_tvar_subst_mono.
        -- eapply d_sub__alll with (T:=T1); auto.
           eapply d_sub_size_sound; eauto.
      (* forall a. A < bot < C *)
      * apply d_sub_size_sound in Hsub1.
        exfalso. eapply d_sub_open_mono_bot_false; eauto.
      (* forall a. A < top < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ ▫ ++ Ψ).
           applys* d_wf_typ_open_tvar_subst_mono.
      (* forall a. A < X < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ ▫ ++ Ψ).
           applys* d_wf_typ_open_tvar_subst_mono.
        -- eapply d_sub__alll with (T:=T1); eauto...
            apply d_sub_size_sound in Hsub1. auto.
      (* forall a. A < X < C *)
      * apply d_sub_size_sound in Hsub1.
        exfalso. eapply d_sub_open_mono_stvar_false; eauto.
      (* forall a. A < B1 -> B2 < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ ▫ ++ Ψ).
           applys* d_wf_typ_open_tvar_subst_mono.
        -- assert (Ψ ⊢ B1) by applys* d_sub_dwft_sized_1. assert (Ψ ⊢ B2) by applys* d_sub_dwft_sized_2.
          eapply d_sub__alll with (T:=T1); eauto...
          eapply IHn_dsub_size with (B:=typ_arrow A0 A2) (n2:=S(n1+n2)); eauto...
      * inversion H.
      * inversion H1.
      * inversion H0.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_dwft in Hsub1_1.
        intuition.
      * econstructor.
        eapply IHn_dsub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
        eapply IHn_dsub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
      * eapply IHn_dsub_size with (B:=B1); eauto...
      * eapply IHn_dsub_size with (B:=B2); eauto...
      * apply d_sub__union1...
        eapply IHn_dsub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
      * apply d_sub__union2...
        eapply IHn_dsub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
    + simpl in H. apply d_sub__intersection2...
      * eapply IHn_dsub_size with (B:=B1) (n1:=n); eauto...
    + simpl in H. apply d_sub__intersection3...
      * eapply IHn_dsub_size with (B:=B1) (n1:=n); eauto...
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_dsub_size with (B:=B1) (n2:=n2); eauto... intuition.
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_dsub_size with (B:=B2) (n2:=n2); eauto... intuition.
    + simpl in Horder. econstructor...
      * eapply IHn_dsub_size with (B:=B1) (n1:=n1); eauto...
      * eapply IHn_dsub_size with (B:=B1) (n1:=n0); eauto...
Qed.


Theorem sub_transitivity : forall Ψ A B C,
  Ψ ⊢ A <: B -> Ψ ⊢ B <: C -> Ψ ⊢ A <: C.
Proof.
  intros * Hab Hbc.
  apply d_sub_size_complete in Hab. destruct Hab as [n1].
  apply d_sub_size_complete in Hbc. destruct Hbc as [n2].
  eapply d_sub_size_transitivity; eauto.
Qed.
