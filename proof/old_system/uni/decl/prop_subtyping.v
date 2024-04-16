Require Import Coq.Program.Equality.
Require Import Lia.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import ltac_utils.


Lemma dsub_refl : forall Ψ A,
  ⊢ Ψ -> Ψ ⊢ A -> Ψ ⊢ A <: A.
Proof.
  intros *Hwfenv Hwfa. apply d_wf_typ_lc_typ in Hwfa as Hlc.  
  generalize dependent Ψ. induction Hlc; intros; try dependent destruction Hwfa; auto.
  - inst_cofinites_for d_sub__all; 
    intros; inst_cofinites_with X; auto. 
    apply d_wf_typ_tvar_stvar_cons in H2; eauto.
Qed.


Lemma dsub_union_inversion : forall Ψ S1 S2 T1,
  Ψ ⊢ typ_union S1 S2 <: T1 ->
  Ψ ⊢ S1 <: T1 /\ Ψ ⊢ S2 <: T1.
Proof with auto.
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
Proof with auto.
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
  s_in X T ->
  Ψ ⊢ typ_top <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.

Theorem dsub_unit_fv_false: forall Ψ X T,
  s_in X T ->
  Ψ ⊢ typ_unit <: T ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.


#[local] Hint Resolve dsub_refl d_wf_typ_subst d_wf_typ_subst_stvar d_wf_env_subst_tvar_typ : core.
(* Hint Resolve dsub_refl : subtyping.
Hint Resolve d_wf_typ_subst : subtyping.
Hint Resolve d_wf_typ_subst_stvar : subtyping.
Hint Resolve d_wf_env_subst_tvar_typ : subtyping. *)



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
Qed.

Lemma d_open_rec_mono_same_order : forall Ψ A T n,
  d_mono_typ Ψ T ->
  d_typ_order (open_typ_wrt_typ_rec n T A) = d_typ_order A.
Proof.
  induction A; simpl; intros; auto.
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
  d_typ_order (A ᵗ^^ₜ T) = d_typ_order A.
Proof.
  intros. unfold open_typ_wrt_typ. eapply d_open_rec_mono_same_order; eauto.
Qed.


Lemma d_open_svar_same_order : forall A X,
  d_typ_order (A ᵗ^ₜ X) = d_typ_order A.
Proof.
  intros. unfold open_typ_wrt_typ. apply d_open_rec_tvar_same_order; auto.
Qed.


Theorem d_sub_mono_stvar_false : forall Ψ T X,
  X ~ ■ ∈ᵈ Ψ ->
  Ψ ⊢ T <: typ_var_f X ->
  Ψ ⊢ₘ T ->
  False.
Proof.
  intros.
  induction H1; dependent destruction H0; auto.
  unify_binds.
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
Qed.


Lemma d_ord_mono_sound: forall Ψ A1,
  d_ord_mono Ψ A1 -> d_mono_typ Ψ A1.
Proof.
  intros. induction H; auto.
Qed.

(* Lemma d_mono_ordiu_sound : forall Ψ A1,
  d_mono_ordiu Ψ A1 -> d_mono_typ Ψ A1.
Proof.
  intros. induction H; auto.
  - apply d_ord_mono_sound. auto.
Qed. *)



(* Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end. *)
Hint Resolve d_wf_typ_weaken : weaken.

Theorem d_sub_weaken: forall Ψ1 Ψ2 Ψ3 A B,
  Ψ3 ++ Ψ1 ⊢ A <: B ->
  ⊢ Ψ3 ++ Ψ2 ++ Ψ1 ->
  Ψ3 ++ Ψ2 ++ Ψ1 ⊢ A <: B.
Proof with auto with weaken.
  intros Ψ1 Ψ2 Ψ3 A B Hsub Hwf.
  dependent induction Hsub;
    try solve [simpl in *];
    try solve [eapply d_wf_typ_weaken with (Ψ2 := Ψ2) in H0; auto]; auto.
  - apply d_sub__all with (L :=  L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1)); intros x Fr; inst_cofinites_with x; auto...
    eapply H2 with (Ψ1 := Ψ1) (Ψ3 := (x, ■) :: Ψ3); simpl; auto.
    constructor; auto.
  - apply d_sub__alll with (T := T) (L :=  L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1)); auto...
    eauto using d_mono_typ_weaken.
  - apply d_sub__intersection2; eauto...
  - apply d_sub__intersection3; auto...
  - apply d_sub__union1; auto...
  - apply d_sub__union2; auto...
Qed.


Corollary d_sub_weaken_cons: forall Ψ x b A B,
  Ψ ⊢ A <: B ->
  ⊢ x ~ b ++ Ψ ->
  x ~ b ++ Ψ ⊢ A <: B.
Proof.
  intros.
  rewrite_env (nil ++ (x ~ b) ++ Ψ).
  eapply d_sub_weaken; eauto.
Qed.


#[local] Hint Resolve d_wf_typ_subst_stvar d_wf_env_subst_stvar_typ : core.
(* Hint Resolve d_subst_stv_lc_typ : lngen. *)

Lemma dneq_all_intersection_union_subst_stv : forall T1 T2 X,
  lc_typ T1 -> lc_typ T2 ->
  neq_all T1 -> neq_intersection T1 -> neq_union T1 ->
  (neq_all ({T2 ᵗ/ₜ X} T1) /\
   neq_intersection ({T2 ᵗ/ₜ X} T1) /\
   neq_union ({T2 ᵗ/ₜ X} T1)) \/ T1 = ` X.
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

Theorem d_sub_mono_refl : forall Ψ A B,
  d_mono_typ Ψ A ->
  d_mono_typ Ψ B ->
  Ψ ⊢ A <: B ->
  A = B.
Proof.
  intros * Hmonoa Hmonob Hsub. dependent induction Hsub;
   try dependent destruction Hmonoa; try dependent destruction Hmonob; auto.
  - erewrite IHHsub1; auto. erewrite IHHsub2; auto.  
Qed.

Theorem d_sub_open_mono_stvar_false: forall n1 n2 Ψ A T X L,
    d_typ_order (A ᵗ^^ₜ T) < n1 ->
    d_typ_size (A ᵗ^^ₜ T) < n2 ->
    X ~ ■ ∈ᵈ Ψ ->
    Ψ ⊢ A ᵗ^^ₜ T <: typ_var_f X ->
    (forall X, X `notin` L -> s_in X (A ᵗ^ₜ X)) ->
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
            subst. dependent destruction H5. unify_binds. 
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
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H4; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H5.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
             inversion Heq.
        -- dependent destruction Heq. unfold open_typ_wrt_typ in *.
           eapply IHn2 with (L:=L); eauto. lia. lia.
           intros. inst_cofinites_with X0. dependent destruction H4; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in H, H0, Heq. simpl in *.
              subst. dependent destruction H4.
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
    assert (X ~ ■ ∈ᵈ (Ψ2 ++ (X, ■) :: Ψ1)) by eauto.
    unify_binds.
  - dependent destruction H; auto... apply notin_union; eauto.
Qed.

(* bookmark *)

Theorem d_sub_subst_stvar : forall Ψ1 X Ψ2 A B T,
  Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1 ⊢ A <: B ->
  Ψ1 ⊢ T ->
  map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1 ⊢ {T ᵗ/ₜ X} A <: {T ᵗ/ₜ X} B.
Proof with subst; eauto using d_wf_typ_weaken_app.
  intros. dependent induction H; try solve [simpl in *; eauto].
  - eapply dsub_refl; auto...
  - simpl. inst_cofinites_for d_sub__all; intros X1 Hfr; inst_cofinites_with X1.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto...
      apply s_in_subst_inv; auto...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto...
      apply s_in_subst_inv; auto...
    + repeat rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; eauto...
      rewrite_env (map (subst_tvar_in_dbind T X) (X1 ~ ■ ++ Ψ2) ++ Ψ1).
      eapply H2; auto...
  - simpl. destruct (dneq_all_intersection_union_subst_stv B T X) as [[? [? ?]] | ?]; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={T ᵗ/ₜ X} T0); auto...
      * intros. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; auto...
        apply s_in_subst_inv; auto...
      * applys* d_mono_typ_subst_stvar... eauto using d_sub_dwft_0.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto using d_wf_typ_lc_typ.
    + eapply d_sub_open_mono_stvar_false in H3; eauto. contradiction.
  - simpl. apply d_sub__intersection2. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__intersection3. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__union1. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_dwft _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__union2. eauto.
    apply d_wf_typ_subst_stvar; auto...
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
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ B1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A1 (typ_var_f X) )   ( open_typ_wrt_typ B1 (typ_var_f X) )  n )  ->
      d_sub_size Ψ (typ_all A1) (typ_all B1) (S n)
 | d_subs__alll : forall (L:vars) (Ψ:denv) (A1 B1 T1:typ) (n:nat),
     neq_all B1 ->
     neq_intersection B1 ->
     neq_union B1 ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
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

#[local] Hint Constructors d_sub_size : core.

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
  Ψ2 ++ X ~ ■ ++ Ψ1 ⊢ A <: B | n ->
  Y ∉ (dom Ψ1 `union` dom Ψ2) ->
  (map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2) ++ Y ~ ■ ++ Ψ1 ⊢
        {typ_var_f Y ᵗ/ₜ X} A <: {typ_var_f Y ᵗ/ₜ X} B | n.
Proof with (simpl in *; eauto using d_wf_env_subst_tvar_typ).
  intros * HS HN.
  case_eq (Y == X); intros.
  1: { subst. rewrite* subst_same_tvar_map_id.
       repeat rewrite* subst_same_tvar_typ_id. } clear H.

  gen Y.
  inductions HS; intros...
  - constructor.
    applys d_wf_env_subst_stvar_typ; auto.
    rewrite_env ((Ψ2 ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ■ ++ Ψ1)...
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - constructor.
    applys d_wf_env_subst_stvar_typ; auto.
    rewrite_env ((Ψ2 ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ■ ++ Ψ1)...
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - constructor. 
    applys d_wf_env_subst_stvar_typ; auto.
    rewrite_env ((Ψ2 ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ■ ++ Ψ1)...
    solve_notin.
  (* - econstructor...
    applys d_wf_env_subst_stvar_typ...
    rewrite_env ((F ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ).
    applys d_wf_env_weaken_stvar.
    rewrite_env (F ++ X ~ ■ ++ Ψ)...
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
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      applys~ s_in_subst_inv.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      applys~ s_in_subst_inv.
    + forwards~: H2 SZ Ψ1 ((SZ, ■) :: Ψ2)...
      repeat rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
  - pick fresh SZ and apply d_subs__alll.
    6: forwards* H4: IHHS;
    rewrite subst_tvar_in_typ_open_typ_wrt_typ in H4; eauto using d_wf_typ_lc_typ.
    1-3: auto...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      applys~ s_in_subst_inv.
    + applys d_mono_typ_subst_stvar.
      * rewrite_env ((Ψ2 ++ X ~ ■) ++ Y ~ ■ ++ Ψ1).
        applys* d_mono_typ_weaken. rewrite_env (Ψ2 ++ (X, ■) :: Ψ1)...
      * rewrite_env ((Ψ2 ++ X ~ ■) ++ Y ~ ■ ++ Ψ1).
        applys d_wf_env_weaken_stvar.
        forwards: d_sub_dwft_sized_0 HS. rewrite_env (Ψ2 ++ (X, ■) :: Ψ1)...
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
    Ψ2 ++ X ~ ■ ++ Ψ1 ⊢ A ᵗ^^ₜ typ_var_f X <: B ᵗ^^ₜ typ_var_f X | n ->
    map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2 ++ Y ~ ■ ++ Ψ1 ⊢ A ᵗ^^ₜ typ_var_f Y <: B ᵗ^^ₜ typ_var_f Y | n.
Proof with eauto.
  intros.
  forwards: d_sub_size_rename_stvar Y H1. solve_notin.
  rewrite 2 subst_tvar_in_typ_open_typ_wrt_typ in H2...
  simpl in H2. case_if.
  rewrite 2 subst_tvar_in_typ_fresh_eq in H2...
Qed.

Lemma d_sub_size_complete : forall Ψ A B,
  Ψ ⊢ A <: B -> exists n, Ψ ⊢ A <: B | n.
Proof with eauto.
  intros. induction H; eauto...
  - destruct IHd_sub1 as [n1]. destruct IHd_sub2 as [n2].
    eauto...
  - pick fresh X.
    destruct (H2 X) as [n]. solve_notin.
    exists (S n).
    eapply d_subs__all with (L:=L `union` ftvar_in_typ A `union` ftvar_in_typ B `union` (dom Ψ)); intros; eauto.
    + rewrite_env (nil ++ X0 ~ ■ ++ Ψ). rewrite_env (nil ++ X ~ ■ ++ Ψ) in H3.
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
Proof with auto.
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


#[local] Hint Extern 1 (?x < ?y) => lia : core.
#[local] Hint Extern 1 (?x <= ?y) => lia : core.
#[local] Hint Extern 1 (?x >= ?y) => lia : core.
#[local] Hint Extern 1 (?x > ?y) => lia : core.


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
    eapply d_sub_size_more; eauto.
    eapply d_sub_size_more; eauto.
Qed.



Theorem d_sub_size_subst_stvar : forall Ψ1 Ψ2 X A B T n,
  Ψ2 ++ (X ~ dbind_stvar_empty) ++ Ψ1 ⊢ A <: B | n ->
  Ψ1 ⊢ T ->
  exists n', map (subst_tvar_in_dbind T X) Ψ2 ++ Ψ1 ⊢ {T ᵗ/ₜ X} A <: {T ᵗ/ₜ X} B | n'.
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

#[local] Hint Constructors d_ord d_wft_ord : core.

Lemma d_wft_ord_complete: forall Ψ A,
  Ψ ⊢ A -> d_wft_ord A.
Proof with auto.
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
    d_typ_order (A ᵗ^^ₜ T) < n1 ->
    d_typ_size (A ᵗ^^ₜ T) < n2 ->
    Ψ ⊢ A ᵗ^^ₜ T <: typ_bot ->
    (forall X, X `notin` L -> s_in X (A ᵗ^ₜ X)) ->
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
           erewrite d_open_mono_same_order; eauto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H4.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H4.
           ++ inversion Heq.
        -- inversion Heq. subst. eapply IHn2 with (L:=L); eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
           ++ intros. inst_cofinites_with X. dependent destruction H3; auto.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
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
        apply d_sub_size_more with (n':=S(n1+n2)) in H1; auto;
        apply d_sub_size_more with (n':=S(n1+n2)) in H2; auto
      end
   end.

Ltac solve_trans_forall_B_union_impl T1 T2:=
  match goal with
    | H1 : ?Ψ ⊢ ?T <: T1 | ?n1 |- _ =>
      apply d_sub_size_more with (n':=S n1) in H1; auto
    | H2 : ?Ψ ⊢ ?T <: T2 | ?n1 |- _ =>
      apply d_sub_size_more with (n':=S n1) in H2; auto
  end.

Ltac solve_trans_forall_B_iu :=
  match goal with
   | H : ?Ψ ⊢ ?T <: ?C | ?n |- ?Ψ ⊢ ?B <: ?D => match D with
      | typ_intersection ?D1 ?D2 => dependent destruction H; auto; solve_trans_forall_B_intersection_impl D1 D2
      | typ_union ?D1 ?D2 => dependent destruction H; auto; solve_trans_forall_B_union_impl D1 D2
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
Proof with auto.
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
           rewrite_env (nil ++ Y ~ ■ ++ Ψ) in H4.
           rewrite_env (nil ++ Y ~ ■ ++ Ψ) in H5.
           forwards: d_wf_typ_stvar_tvar H5.
           simpl in H6. auto.
      * eapply d_sub__all with (L:=L `union` L0 `union` dom Ψ); auto.
        intros. inst_cofinites_with X.
        eapply IHn_d_typ_order with (B:= B1 ᵗ^ₜ X); eauto...
        -- simpl in *. rewrite d_open_svar_same_order...
      * pick fresh Y and apply d_sub__alll. 5: applys H6. all: eauto.
        ** pick fresh X. inst_cofinites_with X.
        replace Ψ with (map (subst_tvar_in_dbind T1 X) nil ++ Ψ) by auto.
        rewrite_env  (nil ++ (X, ■) :: Ψ) in H1.
        eapply d_sub_size_subst_stvar with (T:=T1) in H1; simpl; eauto.
        destruct H1 as [n' Hsub].
        eapply IHn_d_typ_order with (B:=B1 ᵗ^^ₜ T1) (n1:=n'); eauto...
        erewrite d_open_mono_same_order; eauto. 
        rewrite 2 subst_tvar_in_typ_open_typ_wrt_typ in Hsub... simpl in Hsub.
        unfold eq_dec in Hsub. destruct (EqDec_eq_of_X X X) in Hsub.
        rewrite (subst_tvar_in_typ_fresh_eq A1) in Hsub...
        rewrite (subst_tvar_in_typ_fresh_eq B1) in Hsub...
        contradiction.
        all: eauto using d_mono_typ_lc, d_mono_typ_d_wf_typ.
      * eapply d_sub__intersection1.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n1); eauto...
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n2); eauto...
      * eapply d_sub__union1.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n0); eauto...
        -- auto.
      * eapply d_sub__union2.
        -- eapply IHn_dsub_size with (B:=typ_all B1) (n1:=S n) (n2:=n0); eauto...
        -- auto.
    + simpl in *. assert (Ψ ⊢ B1) as Hwft1 by applys* d_sub_dwft_sized_1.
      dependent destruction Hwft1; solve_trans_forall_B_C.
      (* solve_trans_forall_B_C. *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
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
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
           applys* d_wf_typ_open_tvar_subst_mono.
      (* forall a. A < X < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. applys* H2.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
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
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
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
