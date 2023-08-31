Require Import Coq.Program.Equality.
Require Import Lia.

Require Import decl.notations.
Require Import decl.prop_basic.
Require Import ln_utils.

Hint Constructors d_sub : sub.

Lemma dsub_refl' : forall E T, 
  E ⊢ₛ T -> E ⊢ T <: T.
Proof with auto with sub.
  intros; dependent induction H; eauto...
Qed. 


Lemma dsub_refl : forall E T, 
  E ⊢ T -> E ⊢ T <: T.
Proof.
  intros.
  apply dsub_refl'.
  apply dwf_typ_dwf_typ_s.
  auto.
Qed.


(* forall a. forall b. b -> a <: forall a. a -> int *)
(* is a counter example *)


Lemma dsub_union_inversion : forall E S1 S2 T1, 
  E ⊢ dtyp_union S1 S2 <: T1 -> 
  E ⊢ S1 <: T1 /\ E ⊢ S2 <: T1.
Proof with auto with sub.
  intros.
  dependent induction H; auto...
  - inversion H. split; econstructor; auto.
  - specialize (IHd_sub1 _ _ (eq_refl _)).
    specialize (IHd_sub2 _ _ (eq_refl _)).
    destruct IHd_sub1. destruct IHd_sub2.
    intuition.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
Qed.


(* Lemma dsub_intersection_inversion : forall E S1 T1 T2, 
  E ⊢ S1 <: dtyp_intersection T1 T2 -> 
  E ⊢ S1 <: T1 /\ E ⊢ S1 <: T2.
Proof with auto with sub.
  intros.
  dependent induction H; auto...
  - inversion H. split; econstructor; auto.
  - specialize (IHd_sub _ _ (eq_refl _)).
    inversion IHd_sub. 
    split; eapply dsub_open_mono_inversion; eauto.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
  - specialize (IHd_sub _ _ (eq_refl _)).
    intuition.
  - specialize (IHd_sub1 _ _ (eq_refl _)).
    specialize (IHd_sub2 _ _ (eq_refl _)).
    inversion IHd_sub1.    
    destruct IHd_sub2.
    intuition.
Qed. *)


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


Theorem d_sub_tvar_inv_nested_all_false: forall L1 L2 L3 T1 S1,
  (∀ X : atom, X ∉ L1 → d_sub_tvar_open_inv X (open_dtyp_wrt_dtyp_rec 1 S1 T1 ^ᵈ X)) ->
  (∀ X : atom, X ∉ L2 → ds_in X (dtyp_all (open_dtyp_wrt_dtyp_rec 1 `ᵈ X T1))) ->
  (∀ X : atom, X ∉ L3 → ds_in X (open_dtyp_wrt_dtyp_rec 1 S1 T1 ^ᵈ X)) ->
  False.
Proof.
  intros. induction T1; simpl in *.
  - admit.
  - admit.
  - admit.
  - destruct ( lt_eq_lt_dec n 1 ).
    + destruct s. simpl in *. destruct n; simpl in *.
      * admit.
      * admit.
      * admit.
    + destruct (n - 1). 
      * unfold open_dtyp_wrt_dtyp in *. simpl in *. admit.
      * unfold open_dtyp_wrt_dtyp in *. simpl in *. admit.
  - admit.
  - admit.
  - inst_cofinites_by L1. inversion H.
  - inst_cofinites_by L1. inversion H.
  - admit.
  - admit.
Admitted.
     

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
        * rename H2 into Hdsin. rename H3 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- inst_cofinites_by L. inversion Hdsin.
          -- destruct n. simpl in *.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. subst. inversion Hmono.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
        * rename H2 into Hdsin. rename H3 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- inst_cofinites_by (L `union` (singleton X0)).
            unfold open_dtyp_wrt_dtyp in Hdsin. simpl in Hdsin. dependent destruction Hdsin.
            apply notin_union_2 in Fr. apply notin_singleton_1 in Fr. contradiction.
        * rename H2 into Hdsin. rename H3 into Hmono. destruct T1; simpl in *; try solve [inversion Heq].
          -- destruct n. simpl in *.
             ++ eapply d__sti__all with (L:=L). intros. constructor.
             ++ unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. inversion Heq.
          -- unfold open_dtyp_wrt_dtyp in Heq. simpl in Heq. 
             (* S0 *)
             assert (d_typ_order ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2) < n1) by admit.
             assert (d_typ_size ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2) < 
                     S (d_typ_size ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2))) by lia.
             assert ( E ⊢ (open_dtyp_wrt_dtyp_rec 1 S1 T1) ^^ᵈ T2 <: `ᵈ X).
             { inversion Heq. subst. auto. }
             assert ( ∀ X : atom, X ∉ L0 → ds_in X ((open_dtyp_wrt_dtyp_rec 1 S1 T1) ^ᵈ X)). 
             { inversion Heq. subst. auto. }
             specialize (IHn1 _ E _ _ _ _ H2 H3 H10 H11 H6).
             unfold open_dtyp_wrt_dtyp in H8. simpl in H8.
             dependent destruction IHn1.
             specialize (d_sub_tvar_inv_nested_all_false _ _ _ _ _ H H8 H12).
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
             assert (forall X, X ∉ L → ds_in X (T1_1 ^ᵈ X)). {
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
             assert (forall X, X ∉ L → ds_in X (T1_2 ^ᵈ X)). {
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
              assert (forall X, X ∉ L → ds_in X (T1_1 ^ᵈ X)). {
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
              assert (forall X, X ∉ L → ds_in X (T1_2 ^ᵈ X)). {
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
Admitted.


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


Inductive ord_mono_iu : dtyp -> Prop :=
| ordmonoiu_var : forall X, ord_mono_iu (dtyp_var_f X)
| ordmonoiu_unit : ord_mono_iu dtyp_unit
| ordmonoiu_arr : forall T1 T2, 
    dmono_typ T1 -> 
    dmono_typ T2 -> 
    ord_mono_iu (dtyp_arrow T1 T2)
.

Lemma ord_mono_iu_neq_intersection: forall T1,
  ord_mono_iu T1 ->
  dneq_intersection T1.
Proof.
  intros. induction H; auto.
Qed.

Lemma ord_mono_iu_neq_union: forall T1,
  ord_mono_iu T1 ->
  dneq_union T1.
Proof.
  intros. induction H; auto.
Qed.

Inductive dmono_typ_ordiu : dtyp -> Prop :=
| dmonoord_base : forall T1, 
    ord_mono_iu T1 ->
    dmono_typ_ordiu T1
| dmonoord_union : forall T1 T2, 
    dmono_typ_ordiu T1 ->
    dmono_typ_ordiu T2 -> 
    dmono_typ_ordiu (dtyp_union T1 T2)
| dmonoord_inter : forall T1 T2, 
    dmono_typ_ordiu T1 ->
    dmono_typ_ordiu T2 -> 
    dmono_typ_ordiu (dtyp_intersection T1 T2).


Lemma dmono_typ_ordiu_complete : forall T1, 
  dmono_typ T1 -> dmono_typ_ordiu T1.
Proof.
  intros. induction H; try solve [constructor; constructor].
  - apply dmonoord_base. apply ordmonoiu_arr; auto.
  - apply dmonoord_inter; auto.
  - apply dmonoord_union; auto.
Qed.


Lemma ord_mono_iu_sound: forall T1,
  ord_mono_iu T1 -> dmono_typ T1.
Proof.
  intros. induction H; auto.
Qed.

Lemma dmono_typ_ordiu_sound : forall T1,
  dmono_typ_ordiu T1 -> dmono_typ T1.
Proof.
  intros. induction H; auto.
  - apply ord_mono_iu_sound. auto.
Qed.

Theorem d_sub_tvar_ind_open_subst : forall E X T1 T2,
  d_sub_tvar_open_inv X T1 ->
  dmono_typ T2 ->
  E ⊢ T1 ->
  E ⊢ T2 ->
  E ⊢ ({T2 /ᵈ X} T1) <: T2.
Proof.
  intros. induction H.
  - simpl. constructor; auto.
  - simpl. unfold eq_dec.
    destruct (EqDec_eq_of_X X X). 
    apply dsub_refl; auto.
    contradiction.
  - simpl. dependent destruction H1. constructor; auto. 
  - simpl. dependent destruction H1. constructor; auto.
    apply wft_all_open_wfdtyp_wft; auto. 
  - simpl. dependent destruction H1. apply d_sub_intersection3; auto.
    apply wft_all_open_wfdtyp_wft; auto.
Qed.


Theorem d_sub_tvar_ind_sub_all : forall E T1 T2,
  d_sub_tvar_inv (dtyp_all T1) ->
  E ⊢ dtyp_all T1 ->
  dmono_typ T2 ->
  E ⊢ T2 ->
  E ⊢ dtyp_all T1 <: T2.
Proof.
  intros. 
  specialize (dmono_typ_ordiu_complete _ H1). intros.
  induction H3.
  - dependent destruction H0. 
    dependent destruction H.
    eapply d_sub_alll with (L:=L `union` L0) (T2:=T0).
    + now apply d_mono_typ_neq_all.
    + now apply ord_mono_iu_neq_intersection.
    + now apply ord_mono_iu_neq_union.
    + auto. 
    + auto.
    + auto.
    + inst_cofinites_by (L `union` L0 `union` ftv_in_dtyp T1).
      apply d_sub_tvar_ind_open_subst with (E:= (x ~ dbind_tvar_empty) ++ E) (T2:=T0) in H.
      rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp in H; auto.
      rewrite d_subst_tv_in_dtyp_fresh_eq in H; auto.
      simpl in H. destruct eq_dec in H. auto.
      (* d_sub_strenthening *)
      admit.
      contradiction.
      auto.
      inst_cofinites_with x; auto.
      apply dwf_typ_weakening_cons; auto.
  - inversion H1. inversion H2. auto.
  - inversion H1. inversion H2. auto.
Admitted.

Theorem  d_sub_subst_mono : forall E X F S1 T1 T2,
  F ++ (X ~ dbind_tvar_empty) ++ E ⊢ S1 <: T1 ->
  E ⊢ T2 -> 
  dmono_typ T2 ->
  map (d_subst_tv_in_binding T2 X) F ++ E ⊢ {T2 /ᵈ X} S1 <: {T2 /ᵈ X} T1.
Proof with eauto with subtyping.
  intros. 
  dependent induction H; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl. auto...
  - eapply dsub_refl. auto...
  - simpl. eapply d_sub_all with (L:=L); intros SX Hfr; inst_cofinites_with SX.
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + inst_cofinites_with SX. repeat rewrite dtyp_subst_open_comm; eauto...
      replace (SX ~ dbind_stvar_empty ++ map (d_subst_tv_in_binding T2 X) F ++ E) with 
      (map (d_subst_tv_in_binding T2 X) (SX ~ dbind_stvar_empty ++ F) ++ E) by auto.
      eapply H2; auto...
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
    + apply dsub_dwft in H5 as Hwft. destruct Hwft as [HwftS HwftT]. inversion HwftT.
    + simpl.
      specialize (dsub_dwft _ _ _ H5) as Hwft. destruct Hwft.
      apply d_sub_tvar_ind_sub_all.
      -- replace (dtyp_all ({T2 /ᵈ X} S1)) with ({T2 /ᵈ X} (dtyp_all S1)) by auto.
         apply d_sub_tvar_inv_subst. eapply d_sub_tvar_ind_open_inv_complete; eauto.
         eapply dwf_typ_lc_dtyp; eauto.
      -- replace (dtyp_all ({T2 /ᵈ X} S1)) with ({T2 /ᵈ X} (dtyp_all S1)) by auto. 
         apply d_wft_typ_subst; auto. 
         eapply dwftyp_all with (L:=L `union` ftv_in_dtyp S1).
         auto. 
         ++ intros. eapply dwf_typ_open_inv with (X:=X1) (S:=T0); auto.
            rewrite d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
            simpl. rewrite (d_subst_tv_in_dtyp_fresh_eq); auto.
            unfold eq_dec. destruct (EqDec_eq_of_X X1 X1); auto.
            ** apply dwf_typ_weakening_cons; auto.
            ** contradiction.
      -- unfold eq_dec. destruct (EqDec_eq_of_X X0 X); auto. 
      -- replace (if X0 == X then T2 else `ᵈ X0) with ( {T2 /ᵈ X} `ᵈ X0) by auto.
         apply d_wft_typ_subst; auto.
    + eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...  
    + apply dsub_dwft in H5 as Hwft. destruct Hwft as [HwftS HwftT]. inversion HwftT.
      eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); eauto...
      * apply d_neq_all_subst_neq_all; auto...
      * simpl. constructor; apply d_subst_tv_in_dtyp_lc_dtyp; auto...
      * simpl. constructor; apply d_subst_tv_in_dtyp_lc_dtyp; auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * apply d_mono_typ_subst_mono_mono; auto.
      * rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...  
    + inversion H. 
    + inversion H1.
    + inversion H0.
Qed.

(* Theorem  d_sub_subst : forall E SX F S1 T1 T2,
  F ++ (SX ~ dbind_stvar_empty) ++ E ⊢ S1 <: T1 ->
  E ⊢ T2 -> 
  map (d_subst_tv_in_binding T2 SX) F ++ E ⊢ {T2 /ᵈ SX} S1 <: {T2 /ᵈ SX} T1.
Proof with eauto with subtyping.
  intros. dependent induction H; try solve [simpl in *; eauto with subtyping].
  - simpl. constructor. apply d_wft_typ_subst. admit. auto.
  - simpl. auto... admit.
  - eapply dsub_refl. auto...
  - eapply dsub_refl. auto...
  - simpl. eapply d_sub_all with (L:=L); intros SX Hfr; inst_cofinites_with SX.
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + inst_cofinites_with SX. repeat rewrite dtyp_subst_open_comm; eauto...
      replace (SX ~ dbind_stvar_empty ++ map (d_subst_tv_in_binding T2 X) F ++ E) with 
      (map (d_subst_tv_in_binding T2 X) (SX ~ dbind_stvar_empty ++ F) ++ E) by auto.
      eapply H2; auto...
  - simpl. eapply d_sub_alll with (L:=L `union` singleton X) (T2:={T2 /ᵈ X} T0); eauto...
    + eapply d_neq_all_subst_neq_all; eauto...
      eapply dwf_typ_dlc_type. eapply dsub_dwft. eauto.
    + intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
      apply ftv_sin_dtyp_subst_inv; auto...
    + apply d_mono_typ_subst_mono_mono; auto.
    + rewrite <- d_subst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
Qed. *)



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


Inductive dsub_sized : denv -> dtyp -> dtyp -> nat -> Prop :=   
 | dsubsized_top : forall (E:denv) (S:dtyp) (n:nat),
     dwf_typ E S ->
     dsub_sized E S dtyp_top n
 | dsubsized_bot : forall (E:denv) (T:dtyp) (n:nat),
     dwf_typ E T ->
     dsub_sized E dtyp_bot T n
 | dsubsized_unit : forall (E:denv) (n:nat),
     dsub_sized E dtyp_unit dtyp_unit n
 | dsubsized_tvar : forall (E:denv) (X:typvar) (n:nat),
     dwf_typ E (dtyp_var_f X) ->
     dsub_sized E (dtyp_var_f X) (dtyp_var_f X) n
 | dsubsized_stvar : forall (E:denv) (SX:stypvar) (n:nat),
     dwf_typ E (dtyp_svar SX) ->
     dsub_sized E (dtyp_svar SX) (dtyp_svar SX) n
 | dsubsized_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp) (n1 n2:nat),
     dsub_sized E T1 S1 n1 ->
     dsub_sized E S2 T2 n2 ->
     dsub_sized E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2) (S (n1 + n2))
 | dsubsized_all : forall (L:vars) (E:denv) (S1 T:dtyp) (n:nat),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> dsub_sized  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) n) ->
     dsub_sized E (dtyp_all S1) (dtyp_all T) (S n)
 | dsubsized_alll : forall (L:vars) (E:denv) (S1 T1 T2:dtyp) (n:nat),
     dneq_all T1 ->
     ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S1   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     dsub_sized E  (open_dtyp_wrt_dtyp  S1   T2 )  T1 n ->
     dsub_sized E (dtyp_all S1) T1 (S n)
 | dsubsized_intersection1 : forall (E:denv) (S1 T1 T2:dtyp) (n1 n2:nat),
     dsub_sized E S1 T1 n1 ->
     dsub_sized E S1 T2 n2 ->
     dsub_sized E S1 (dtyp_intersection T1 T2) (S (n1 + n2))
 | dsubsized_intersection2 : forall (E:denv) (S1 S2 T:dtyp) (n:nat),
     dsub_sized E S1 T n ->
     dwf_typ E S2 ->
     dsub_sized E (dtyp_intersection S1 S2) T (S n)
 | dsubsized_intersection3 : forall (E:denv) (S1 S2 T:dtyp) (n:nat),
     dsub_sized E S2 T n ->
     dwf_typ E S1 ->
     dsub_sized E (dtyp_intersection S1 S2) T (S n)
 | dsubsized_union1 : forall (E:denv) (S1 T1 T2:dtyp) (n:nat),
     dsub_sized E S1 T1 n ->
     dwf_typ E T2 ->
     dsub_sized E S1 (dtyp_union T1 T2) (S n)
 | dsubsized_union2 : forall (E:denv) (S1 T1 T2:dtyp) (n:nat),
     dsub_sized E S1 T2 n ->
     dwf_typ E T1 ->
     dsub_sized E S1 (dtyp_union T1 T2) (S n)
 | dsubsized_union3 : forall (E:denv) (S1 S2 T:dtyp) (n1 n2:nat),
     dsub_sized E S1 T n1 ->
     dsub_sized E S2 T n2 ->
     dsub_sized E (dtyp_union S1 S2) T (S (n1 + n2)).


Theorem dsub_sized_wrt_dsub_sound : forall E S1 T1 n,
  dsub_sized E S1 T1 n -> E ⊢ S1 <: T1.
Proof.
  intros. induction H; eauto.
Qed.

Hint Constructors dsub_sized : sub.

Lemma dsub_sized_subst : forall F SX1 E S1 T1 n SX2 ,
  dsub_sized (F ++ (SX1 ~ dbind_stvar_empty) ++ E) S1 T1 n ->
  dsub_sized (map (d_subst_stv_in_binding (dtyp_svar SX2) SX1) F ++ (SX2 ~ dbind_tvar_empty) ++ E) 
    (d_subst_stv_in_dtyp (dtyp_svar SX2) SX1 S1)  (d_subst_stv_in_dtyp (dtyp_svar SX2) SX1 T1) n.
Proof with eauto with sub.
  intros. dependent induction H; try solve [simpl; eauto with sub].
  - simpl. constructor. admit.
  - simpl. constructor. admit.
  - simpl. constructor. admit.
  - admit.
  - simpl. constructor.
    + eapply IHdsub_sized1; auto.
    + eapply IHdsub_sized2; auto.
  - admit.
  - admit.
  - simpl. constructor.
    + eapply IHdsub_sized1; auto.
    + eapply IHdsub_sized2; auto.
  - simpl. apply dsubsized_intersection2.
    + eapply IHdsub_sized; auto.
    + admit.
  - simpl. apply dsubsized_intersection3.
    + eapply IHdsub_sized; auto.
    + admit.
Admitted.

(* Theorem sized_var_substitution : forall G1 G2 x x' A B n,
  G1 , x  ,, G2 ⊢ A <: B | n ->
  ⊢ G1, x' ,, G2 ->
  G1 , x' ,, G2 ⊢ [`ᵈ x' /ᵈ x] A <: [`ᵈ x' /ᵈ x] B | n. *)


Lemma dsub_sized_wrt_dub_complete : forall E T1 T2,
  E ⊢ T1 <: T2 -> exists n, dsub_sized E T1 T2 n.
Proof with eauto with sub.
  intros. induction H; eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
  - inst_cofinites_by L. destruct H2 as [n].
    exists (S n). eapply dsubsized_all with (L:=L); intros.
    + admit.
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


(* 


Lemma open_mono_order : forall A t,
  ld_mono_type t -> type_order (A ^^ᵈ t) = type_order A.
Proof.
  intros.
  eapply open_mono_order_rec; auto.  
Qed.



Hint Constructors sized_ld_sub: trans.

Lemma sized_ld_sub_to_ld_sub : forall G t1 t2 n,
  G ⊢ t1 <: t2 | n -> G ⊢ t1 <: t2.
Proof.
  intros. induction H; eauto.
Qed.


Lemma sized_ld_sub_weakening : forall G1 G2 G3 t1 t2 n,
  G1 ,, G3 ⊢ t1 <: t2 | n -> ⊢ G1 ,, G2 ,, G3 ->
  G1 ,, G2 ,, G3 ⊢ t1 <: t2 | n.
Proof with auto with trans.
  intros.
  dependent induction H; auto...
  - constructor; auto. eapply ld_in_context_weakenning; auto.
  - eapply sls_intersection_l1. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_intersection_l2. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_union_r1. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_union_r2. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_foralll with (t:=t); auto.
    eapply ld_wf_mtype_weakening; auto.
  - eapply sls_forallr with (L:=L `union`  ld_ctx_dom (G1,, G2,, G3)). intros.
    inst_cofinites_with x. replace (G1,, G2,, G3, x ) with (G1,, G2,, (G3, x)) by auto.
    eapply H0; auto. simpl. constructor; auto.
Qed.


Corollary sized_ld_sub_weakening_cons : forall G x t1 t2 n,
  G ⊢ t1 <: t2 | n -> x `notin` ld_ctx_dom G -> G , x ⊢ t1 <: t2 | n.
Proof.
  intros.
  replace (G , x) with (G ,, (ld_ctx_cons ld_ctx_nil x) ,, ld_ctx_nil) by auto.
  eapply sized_ld_sub_weakening; auto.
  simpl. constructor; auto.
  apply sized_ld_sub_to_ld_sub in H. apply ld_sub_wf_ctx in H. auto.
Qed.


Lemma context_cons_app_eq : forall G1 G2 x,
  G1, x ,, G2 = G1 ,, (ld_ctx_nil, x ,, G2).
Proof.
  intros. induction G2; auto.
  simpl. rewrite IHG2. auto.
Qed.

Theorem ld_wf_ctx_middle : forall G1 G2 x x',
  x <> x' -> ⊢ G1, x,, G2 -> ⊢ G1, x',, G2 -> ⊢ G1, x', x,, G2.
Proof.
  intros. induction G2; simpl in *.
  - constructor. auto. simpl. apply notin_add_3. auto.
    dependent destruction H0. auto.
  - dependent destruction H0. dependent destruction H2. constructor. auto.
    clear H0. clear H2. clear IHG2.
    induction G2; simpl in *.
    + apply notin_add_3. specialize (notin_add_1 _ _ _ H1). auto.
      apply notin_add_3. specialize (notin_add_1 _ _ _ H1). auto.  specialize (notin_add_1 _ _ _ H3). auto.
    + apply notin_add_3.
      apply notin_add_1 in H1. auto.
      apply notin_add_2 in H1. apply notin_add_2 in H3. auto.
Qed.


Theorem sized_var_substitution : forall G1 G2 x x' A B n,
  G1 , x  ,, G2 ⊢ A <: B | n ->
  ⊢ G1, x' ,, G2 ->
  G1 , x' ,, G2 ⊢ [`ᵈ x' /ᵈ x] A <: [`ᵈ x' /ᵈ x] B | n.
Proof.
  intros.
  dependent induction H.
  - simpl. destruct (x0 == x). 
    + subst. constructor; auto. clear H1. clear H0. clear H. induction G2.
      * simpl. constructor.
      * simpl. constructor. eauto.
    + constructor.
      * auto.
      * eapply ld_in_context_other in H0; eauto.
        replace (G1,x',,G2) with (G1,,(ld_ctx_nil, x'),,G2) by auto. apply ld_in_context_weakenning. auto.
  - simpl. constructor. auto. 
  - simpl. constructor; eauto.
  - simpl. constructor; eauto.
  - simpl. apply sls_intersection_l1; auto.
    now apply ld_wf_type_subst_var.
  - simpl. apply sls_intersection_l2; auto. 
    now apply ld_wf_type_subst_var.
  - simpl. apply sls_union_r1; auto. 
    now apply ld_wf_type_subst_var.
  - simpl. apply sls_union_r2; auto. 
    now apply ld_wf_type_subst_var.
  - simpl. apply sls_union_l; auto. 
  - simpl. eapply sls_foralll with (t:=[`ᵈ x' /ᵈ x] t). 
    + destruct (x == x'); subst.
      * replace ([`ᵈ x' /ᵈ x'] t) with t; auto.
        now apply subst_same_eq.
      * apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H. destruct H.
        apply ld_wf_mtype_subst.
        -- auto.
        -- apply ld_wf_mtype_equiv_ld_wf_type_and_mono. split; auto.
            replace (G1, x', x,, G2) with (G1,, (ld_ctx_nil, x'),, (ld_ctx_nil, x,, G2)).
            apply ld_wf_type_weakening.
            ++ simpl. rewrite <- context_cons_app_eq. auto. 
            ++ simpl. clear IHsized_ld_sub. 
               apply ld_wf_type_is_wf_ctx in H.
               rewrite <- context_cons_app_eq. apply ld_wf_ctx_middle; auto. 
            ++ clear. induction G2; auto.
               simpl. rewrite <- IHG2. auto.
        -- constructor. replace (G1, x') with (G1,x',,ld_ctx_nil) by auto. eapply ld_wf_ctx_weakening; eauto.
           constructor. 
    + replace (([`ᵈ x' /ᵈ x] A) ^^ᵈ ([`ᵈ x' /ᵈ x] t)) with ([`ᵈ x' /ᵈ x] A ^^ᵈ t).
      * apply IHsized_ld_sub; auto.
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type; auto. 
  - simpl. eapply sls_forallr with (L:=L `union` singleton x `union` ld_ctx_dom ( G1, x',, G2)).
    intros. inst_cofinites_with x0.
    rewrite_subst_open_var.
    replace  (([`ᵈ x' /ᵈ x] B) ^^ᵈ ([`ᵈ x' /ᵈ x] `ᵈ x0)) with ( [`ᵈ x' /ᵈ x] B ^^ᵈ `ᵈ x0).
    + replace (G1, x',, G2, x0 ) with (G1,x',, (G2, x0)) by auto. apply H0; auto.
      simpl. constructor; auto. 
    + rewrite subst_ld_type_open_ld_type_wrt_ld_type. reflexivity. simpl.
      replace (G1,, G2, x0 ) with (G1,, (G2, x0)) by auto. now apply ld_mono_is_ld_lc.
Qed.


Hint Resolve ld_sub_wf_ctx : trans.
Hint Resolve sized_ld_sub_to_ld_sub : trans.
Hint Resolve sized_ld_sub_weakening_cons : trans.
Hint Resolve ld_wf_mtype_is_mtype : trans.
Hint Resolve sized_ld_sub_weakening : trans.
Hint Resolve open_subst_eq : trans.
Hint Extern 1 (?x < ?y) => lia : trans.


Lemma ld_sub_to_sized_ld_sub : forall G t1 t2,
  G ⊢ t1 <: t2 -> exists n', G ⊢ t1 <: t2 | n'.
Proof with eauto with trans.
  intros. induction H.
  + exists 0. econstructor; eauto.
  + exists 0. econstructor; eauto.
  + destruct IHld_sub1 as [n1].
    destruct IHld_sub2 as [n2].
    exists (S (n1 + n2)). econstructor; eauto.
  + destruct IHld_sub1 as [n1].
    destruct IHld_sub2 as [n2].
    exists (S (n1 + n2)). econstructor; eauto.
  + destruct IHld_sub as [n].
    exists (S n). econstructor; eauto.
  + destruct IHld_sub as [n].
    exists (S n). eapply sls_intersection_l2; eauto.
  + destruct IHld_sub as [n].
    exists (S n). eapply sls_union_r1; eauto.
  + destruct IHld_sub as [n].
    exists (S n). eapply sls_union_r2; eauto.
  + destruct IHld_sub1 as [n1].
    destruct IHld_sub2 as [n2].
    exists (S (n1 + n2)). eapply sls_union_l; eauto.
  + destruct IHld_sub as [n].
    exists (S n). econstructor; eauto.
  + inst_cofinites_by (L `union` fv_ld_type A `union` fv_ld_type B). destruct H0 as [n].
    exists (S n). eapply sls_forallr with (L:=L `union` (ld_ctx_dom G)). intros.
    replace (G, x0) with (G, x0,,ld_ctx_nil) by auto.
    replace A with ([`ᵈ x0 /ᵈ x] A).
    replace (B ^^ᵈ `ᵈ x0) with ([`ᵈ x0 /ᵈ x] B ^^ᵈ `ᵈ x).
    eapply  sized_var_substitution; eauto.
    * simpl. constructor; auto.
      apply ld_sub_wf_ctx in H. dependent destruction H. auto.
    * apply eq_sym. eauto...
    * rewrite subst_ld_type_fresh_eq; auto.
Qed.


Theorem sized_substitution : forall G1 G2 x A B t n,
  G1 , x  ,, G2 ⊢ A <: B | n ->
  G1 ⊢ t -> ld_mono_type t ->
  exists n', G1 ,, G2 ⊢ [t /ᵈ x] A <: [t /ᵈ x] B | n'.
Proof.
  intros.
  apply sized_ld_sub_to_ld_sub in H.
  apply substitution with (t:=t) in H; auto.
  apply ld_sub_to_sized_ld_sub in H. auto.
Qed.

Lemma nat_split: forall n n1 n2, n >= S (n1 + n2) -> 
  exists n1' n2', n = S (n1' + n2') /\ n1' >= n1 /\ n2' >= n2.
Proof.
  intros. induction H.
  - exists n1, n2. split; lia.
  - destruct IHle as [n1' [n2' Hn1n2]].
    exists (S n1'), n2'. split; lia.
Qed.

Lemma nat_suc: forall n n1, n >= S n1 -> 
  exists n1', n = S n1' /\ n1' >= n1.
Proof.
  intros. induction H.
  - exists n1. split; lia.
  - destruct IHle as [n1' [n2' Hn1n2]].
    exists (S n1'). split; lia.
Qed.

Lemma size_sub_more: forall G A B n,
  G ⊢ A <: B | n -> forall n', n' >= n -> G ⊢ A <: B | n'.
Proof.
  intros G A B n H.
  dependent induction H; intros.
  - econstructor; auto.
  - econstructor; auto.
  - specialize (nat_split n' n1 n2 H1). 
    intros Hn'. destruct Hn' as [n1' [n2' Hn1n2]].
    inversion Hn1n2. subst.
    econstructor; intuition.
  - specialize (nat_split n' n1 n2 H1). 
    intros Hn'. destruct Hn' as [n1' [n2' Hn1n2]].
    inversion Hn1n2. subst.
    econstructor; intuition.
  - specialize (nat_suc n' n1 H1).
    intros Hn'. destruct Hn' as [n1' Hn1].
    inversion Hn1. subst.
    apply sls_intersection_l1; auto.
  - specialize (nat_suc n' n2 H1).
    intros Hn'. destruct Hn' as [n2' Hn2].
    inversion Hn2. subst.
    apply sls_intersection_l2; auto.
  - specialize (nat_suc n' n1 H1).
    intros Hn'. destruct Hn' as [n1' Hn1].
    inversion Hn1. subst.
    apply sls_union_r1; auto.
  - specialize (nat_suc n' n2 H1).
    intros Hn'. destruct Hn' as [n2' Hn2].
    inversion Hn2. subst.
    apply sls_union_r2; auto.
  -  specialize (nat_split n' n1 n2 H1). 
    intros Hn'. destruct Hn' as [n1' [n2' Hn1n2]].
    inversion Hn1n2. subst.
    econstructor; intuition.
  - specialize (nat_suc n' n H1).
    intros Hn'. destruct Hn' as [n1 Hn1].
    inversion Hn1. subst.
    econstructor; auto. auto.
  - specialize (nat_suc n' n H1).
    intros Hn'. destruct Hn' as [n1 Hn1].
    inversion Hn1. subst.
    econstructor; auto. 
Qed.


Lemma sized_sub_union_inv: forall G A1 A2 B n,
  G ⊢ (ld_t_union A1 A2) <: B | n -> G ⊢ A1 <: B | n /\ G ⊢ A2 <: B | n.
Proof.
  intros.
  dependent induction H.
  - specialize (IHsized_ld_sub1 A1 A2 (eq_refl _)).
    specialize (IHsized_ld_sub2 A1 A2 (eq_refl _)).
    split; econstructor; intuition.
  - specialize (IHsized_ld_sub A1 A2 (eq_refl _)).
    split; constructor; intuition.
  - specialize (IHsized_ld_sub A1 A2 (eq_refl _)).
    split; apply sls_union_r2; intuition.
  - split.
    apply size_sub_more with (n:=n1); auto. lia.
    apply size_sub_more with (n:=n2); auto. lia.
  - split; intros;
    apply sls_forallr with (L:=L); intros;
    inst_cofinites_with x; specialize (H0 A1 A2 (eq_refl _));
    intuition.
Qed.

Theorem generalized_transitivity : forall t_order t_ssize G A B C n1 n2 ,
  type_order B < t_order ->
  n1 + n2 < t_ssize -> 
  (G ⊢ A <: B | n1) -> (G ⊢ B <: C | n2) -> (ld_sub G A C).
Proof with eauto with trans.
  induction t_order; induction t_ssize; intros.
  - inversion H. 
  - inversion H. 
  - dependent destruction H1; inversion H0.
  - dependent destruction H1...
      + dependent destruction H2. 
        * simpl in H. econstructor. 
          eapply IHt_ssize with (B:=C0); eauto...
          eapply IHt_ssize with (B:=D); eauto...
        * simpl in *. econstructor. 
          -- eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
          -- eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
        * simpl. eapply ld_sub_union_r1; auto.
          eapply IHt_ssize with  (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
        * simpl. eapply ld_sub_union_r2; auto.
          eapply IHt_ssize with  (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
        * eapply ld_sub_forallr with (L:=L `union` ld_ctx_dom G). 
          intros. inst_cofinites_with x.
          eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1:=S (n1 + n0)); eauto...
      + simpl in H. dependent destruction H2.
        * apply ld_sub_intersection_r. eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
          eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
        * eapply IHt_ssize with (B:=B1); eauto...
        * eapply IHt_ssize with (B:=B2); eauto...
        * eapply ld_sub_union_r1; auto. eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
        * eapply ld_sub_union_r2; auto. eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
        * eapply ld_sub_forallr with (L:=L `union` ld_ctx_dom G).
          intros.
          eapply IHt_ssize with (B:=ld_t_intersection B1 B2) (n1:=S(n1 + n0)) (n2:=n); eauto...
      + apply ld_sub_intersection_l1; auto. eapply IHt_ssize; eauto... 
      + apply ld_sub_intersection_l2; auto. eapply IHt_ssize; eauto... 
      + simpl in H.
        specialize (sized_sub_union_inv G B1 B2 C n2 H3). intros. destruct H4.
        eapply IHt_ssize with (B:=B1) (n1:=n1) (n2:=n2); eauto...
      + simpl in H.
        specialize (sized_sub_union_inv G B1 B2 C n2 H3). intros. destruct H4.
        eapply IHt_ssize with (B:=B2) (n1:=n0) (n2:=n2); eauto...
      + apply ld_sub_union_l. eapply IHt_ssize; eauto... eapply IHt_ssize; eauto...
      + eapply ld_sub_foralll with (t:=t). auto.
        eapply IHt_ssize with (B:=B); eauto...
      + dependent destruction H2. 
        * apply ld_sub_intersection_r. eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
          eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
        * apply ld_sub_union_r1. eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
          auto.
        * apply ld_sub_union_r2. eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
          auto.
        * inst_cofinites_by (L `union` fv_ld_type A `union` fv_ld_type B).
          apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H2. destruct H2.
          specialize (sized_substitution G ld_ctx_nil x _ _ _ _ H1 H2 H4).
          intros. destruct H5 as [n1 Hsub].
          eapply IHt_order with (B:=B ^^ᵈ t) (n1:=n1) (n2:=n0); eauto. simpl in H; eauto.
          rewrite (open_mono_order B t); eauto...
          replace G with (G ,, ld_ctx_nil) by auto.
          replace (B ^^ᵈ t) with ([t /ᵈ x] B ^^ᵈ `ᵈ x).
          replace A with ([t /ᵈ x] A).
          -- auto. 
          -- rewrite subst_ld_type_fresh_eq; auto.
          -- apply eq_sym. eapply open_subst_eq; auto.
             apply ld_mono_is_ld_lc. auto. 
        * apply ld_sub_forallr with (L:=L `union` L0 `union` fv_ld_type B `union` fv_ld_type A).
          intros. inst_cofinites_with x.
          eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n) (n2:=n0); auto... 
          eapply sls_forallr with (L:= (ld_ctx_dom G) `union` singleton x). intros.
          assert (⊢ G, x). { auto... } 
          assert (⊢ G, x0). { constructor. dependent destruction H5;  auto. auto. }
          replace (G, x, x0) with (G ,, (ld_ctx_nil,  x) ,, (ld_ctx_nil, x0)) by auto.
          eapply sized_ld_sub_weakening; simpl.
          replace A with ([`ᵈ x0 /ᵈ x] A).
          replace (B ^^ᵈ `ᵈ x0) with ([`ᵈ x0 /ᵈ x] B ^^ᵈ `ᵈ x).
          replace (G, x0) with (G, x0,, ld_ctx_nil) by auto.
          apply sized_var_substitution; auto.
          -- apply eq_sym. eauto... 
          -- rewrite subst_ld_type_fresh_eq; auto.
          -- econstructor; eauto.
Qed.


 *)

Lemma sub_transitivity' : forall n_dtyp_order n_dsub_size E R1 S1 T1 n1 n2 ,
  dtyp_order S1 < n_dtyp_order ->
  n1 + n2 < n_dsub_size -> 
  dsub_sized E R1 S1 n1 -> dsub_sized E S1 T1 n2 -> E ⊢ R1 <: T1.
Proof.
Admitted.


Theorem sub_transitivity : forall E R1 S1 T1,
   E ⊢ R1 <: S1 -> E ⊢ S1 <: T1 -> E ⊢ R1 <: T1.
Proof.
  intros E R1 S1 T1 Hrs Hst.
  apply dsub_sized_wrt_dub_complete in Hrs. destruct Hrs as [n1].
  apply dsub_sized_wrt_dub_complete in Hst. destruct Hst as [n2].
  eapply sub_transitivity'; eauto.
Qed.
