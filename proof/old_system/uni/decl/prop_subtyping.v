Require Import Coq.Program.Equality.
Require Import Lia.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_rename.
Require Import ltac_utils.


Lemma d_sub_refl : forall Ψ A,
  ⊢ᵈ Ψ -> Ψ ᵗ⊢ᵈ A -> Ψ ⊢ A <: A.
Proof.
  intros *Hwfenv Hwfa. apply d_wf_typ_lc_typ in Hwfa as Hlc.  
  generalize dependent Ψ. induction Hlc; intros; try dependent destruction Hwfa; auto.
  - inst_cofinites_for d_sub__all_refl; 
    intros; inst_cofinites_with X; auto.
    eapply H0...
    apply d_wf_env__stvar; auto.
    apply d_wf_typ_tvar_stvar_cons in H1; eauto.
Qed.


Lemma d_sub_union_inv : forall Ψ A1 A2 B,
  Ψ ⊢ typ_union A1 A2 <: B ->
  Ψ ⊢ A1 <: B /\ Ψ ⊢ A2 <: B.
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


Lemma d_sub_intersection_inv : forall Ψ A B1 B2,
  Ψ ⊢ A <: typ_intersection B1 B2 ->
  Ψ ⊢ A <: B1 /\ Ψ ⊢ A <: B2.
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


Theorem d_sub_unit_all_false: forall Ψ A,
  Ψ ᵗ⊢ᵈ typ_all A ->
  Ψ ⊢ typ_unit <: typ_all A ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem d_sub_top_all_false: forall Ψ A,
  Ψ ᵗ⊢ᵈ typ_all A ->
  Ψ ⊢ typ_top <: typ_all A ->
  False.
Proof.
  intros. dependent induction H0.
Qed.

Theorem d_sub_top_fv_false: forall Ψ X A,
  s_in X A ->
  Ψ ⊢ typ_top <: A ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.

Theorem d_sub_unit_fv_false: forall Ψ X A,
  s_in X A ->
  Ψ ⊢ typ_unit <: A ->
  False.
Proof.
  intros. dependent induction H0; try solve [inversion H; eauto].
Qed.


#[local] Hint Resolve d_sub_refl d_wf_typ_subst_tvar d_wf_typ_subst_stvar d_wf_env_subst_tvar : core.
(* Hint Resolve d_sub_refl : subtyping.
Hint Resolve d_wf_typ_subst : subtyping.
Hint Resolve d_wf_typ_subst_stvar : subtyping.
Hint Resolve d_wf_env_subst_tvar : subtyping. *)



Fixpoint d_typ_order (A : typ) : nat :=
  match A with
  | typ_all A1 => S ( d_typ_order A1 )
  | typ_arrow A1 A2 => d_typ_order A1 + d_typ_order A2
  | typ_intersection A1 A2 => d_typ_order A1 + d_typ_order A2
  | typ_union A1 A2 => d_typ_order A1 + d_typ_order A2
  | _ => 0
  end.

Fixpoint d_typ_size (A : typ) :=
  match A with
  | typ_intersection A1 A2 => 1 + d_typ_size A1 + d_typ_size A2
  | typ_union A1 A2 => 1 + d_typ_size A1 + d_typ_size A2
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
  Ψ ᵗ⊢ᵈₘ T ->
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

Lemma d_sneq_stvar_weaken : forall Ψ1 Ψ2 Ψ3 A,
  d_sneq_stvar (Ψ3 ++ Ψ1) A ->
  uniq (Ψ3 ++ Ψ2 ++ Ψ1) ->
  d_sneq_stvar (Ψ3 ++ Ψ2 ++ Ψ1) A.
Proof.
  intros. dependent induction H; eauto.
Qed.

Theorem d_sub_weaken: forall Ψ1 Ψ2 Ψ3 A B,
  Ψ3 ++ Ψ1 ⊢ A <: B ->
  ⊢ᵈ Ψ3 ++ Ψ2 ++ Ψ1 ->
  Ψ3 ++ Ψ2 ++ Ψ1 ⊢ A <: B.
Proof with auto with weaken.
  intros Ψ1 Ψ2 Ψ3 A B Hsub Hwf.
  dependent induction Hsub;
    try solve [simpl in *];
    try solve [eapply d_wf_typ_weaken with (Ψ2 := Ψ2) in H0; auto]; auto.
  - apply d_sub__all with (L :=  L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1)); intros X Fr; inst_cofinites_with X; auto...
    rewrite_env ((X ~ □ ++ Ψ3) ++ Ψ2 ++ Ψ1). apply d_sneq_stvar_weaken; simpl...
    rewrite_env ((X ~ □ ++ Ψ3) ++ Ψ2 ++ Ψ1). apply d_sneq_stvar_weaken; simpl...
    eapply H2 with (Ψ1 := Ψ1) (Ψ3 := (X, ■) :: Ψ3); simpl; auto.
    apply d_wf_env__stvar; auto.
  - apply d_sub__alll with (T := T) (L :=  L `union` dom (Ψ3 ++ Ψ2 ++ Ψ1)); auto...
    intros. inst_cofinites_with X. rewrite_env ((X ~ □ ++ Ψ3) ++ Ψ2 ++ Ψ1). apply d_sneq_stvar_weaken; simpl...
    eauto using d_mono_typ_weaken.
  - apply d_sub__intersection2; eauto...
  - apply d_sub__intersection3; auto...
  - apply d_sub__union1; auto...
  - apply d_sub__union2; auto...
  - inst_cofinites_for d_sub__all_refl. intros. inst_cofinites_with X.
    rewrite_env ((X ~ ■ ++ Ψ3) ++ Ψ2 ++ Ψ1)...
    eapply H0... simpl... apply d_wf_env__stvar...
Qed.


Corollary d_sub_weaken_cons: forall Ψ x b A B,
  Ψ ⊢ A <: B ->
  ⊢ᵈ x ~ b ++ Ψ ->
  x ~ b ++ Ψ ⊢ A <: B.
Proof.
  intros.
  rewrite_env (nil ++ (x ~ b) ++ Ψ).
  eapply d_sub_weaken; eauto.
Qed.


#[local] Hint Resolve d_wf_typ_subst_stvar d_wf_env_subst_stvar : core.

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
  Ψ ᵗ⊢ᵈₘ A ->
  Ψ ᵗ⊢ᵈₘ B ->
  Ψ ⊢ A <: B ->
  A = B.
Proof.
  intros * Hmonoa Hmonob Hsub. dependent induction Hsub;
   try dependent destruction Hmonoa; try dependent destruction Hmonob; auto.
  - erewrite IHHsub1; auto. erewrite IHHsub2; auto.  
Qed.

Inductive typ_sub_bot : typ -> Prop :=
  | typ_sb__bot : typ_sub_bot typ_bot
  | typ_sb__intersection1 : forall A B,
      typ_sub_bot A ->
      typ_sub_bot (typ_intersection A B)
  | typ_sb__intersection2 : forall A B,
      typ_sub_bot B ->
      typ_sub_bot (typ_intersection A B)      
  | typ_sb__union : forall A B,
      typ_sub_bot A ->
      typ_sub_bot B ->
      typ_sub_bot (typ_union A B)
  | typ_sb__all : forall A L,
      (forall X, X `notin` L -> typ_sub_bot (open_typ_wrt_typ A (typ_var_f X))) ->
      typ_sub_bot (typ_all A)
  .

Lemma d_mono_typ_sub_bot_false : forall Ψ T,
  d_mono_typ Ψ T ->
  typ_sub_bot T ->
  False.
Proof.
  intros. dependent induction H; eauto.
  - dependent destruction H0.
  - dependent destruction H0.
  - dependent destruction H1.
Qed.

#[local] Hint Constructors typ_sub_bot : core.

Lemma typ_sub_bot_subst_inv : forall X Ψ A T,
  lc_typ A ->
  Ψ ᵗ⊢ᵈₘ T ->
  typ_sub_bot ({T ᵗ/ₜ X} A) ->
  typ_sub_bot A.
Proof with eauto.
  intros. dependent induction H; eauto.
  - simpl in H1. destruct_eq_atom.
    + exfalso. eapply d_mono_typ_sub_bot_false; eauto. 
    + dependent destruction H1.
  - simpl in H2. inversion H2.
  - dependent destruction H2.
    inst_cofinites_for typ_sb__all; intros.
    inst_cofinites_with X0. apply H0; auto.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2 in H2...
  - simpl in H2. dependent destruction H2... 
  - simpl in H2. dependent destruction H2...
Qed.


(* Lemma d_sub_sub_bot_subst_inv : forall Ψ A B X,
  Ψ ⊢ A ᵗ^^ₜ T <: typ_bot ->
  Ψ ᵗ⊢ᵈₘ T ->
  Ψ ⊢ A <: typ_bot -> *)

Theorem d_sub_open_mono_bot_sub_bot: forall n1 n2 Ψ A T,
  d_typ_order (A ᵗ^^ₜ T) < n1 ->
  d_typ_size (A ᵗ^^ₜ T) < n2 ->
  Ψ ⊢ A ᵗ^^ₜ T <: typ_bot ->
  Ψ ᵗ⊢ᵈₘ T ->
  typ_sub_bot (A ᵗ^^ₜ T).
Proof with auto.
  intro n1. induction n1.
  - intros. inversion H.
  - intros n2. induction n2.
    + intros. inversion H0.
    + intros. dependent destruction H1; rename x into Heq.
      * destruct A; simpl in *; try solve [inversion Heq]...
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H3.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
      * destruct A; simpl in *; try solve [ inversion Heq].
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H7.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
        -- inversion Heq. subst. inst_cofinites_for typ_sb__all; intros.
           fold open_typ_wrt_typ_rec.
           eapply typ_sub_bot_subst_inv with (X:=X) (T:=T0); eauto.
           ++ apply d_sub_d_wf_typ1 in H6. apply d_wf_typ_lc_typ in H6.
              eapply lc_typ_subst_inv with (X:=X) (T:=T0); eauto.
              rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2; eauto. rewrite ftvar_in_typ_open_typ_wrt_typ_rec_upper...
           ++ rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2; auto. 
              simpl. eapply IHn1 with (Ψ:=Ψ) (T:=T0); eauto.
              erewrite d_open_mono_same_order; eauto. lia. eauto.
              eauto. rewrite ftvar_in_typ_open_typ_wrt_typ_rec_upper...
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
           ++ inversion Heq.
        -- inversion Heq. subst. apply typ_sb__intersection1. eapply IHn2; eauto.
           ++  unfold open_typ_wrt_typ. lia.
           ++  unfold open_typ_wrt_typ. lia.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
           ++ inversion Heq.
        -- inversion Heq. subst. apply typ_sb__intersection2. eapply IHn2; eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H2.
           ++ inversion Heq.
        -- inversion Heq. subst. constructor.
           ++ eapply IHn2; unfold open_typ_wrt_typ; eauto. lia. lia. 
           ++ eapply IHn2; unfold open_typ_wrt_typ; eauto. lia. lia. 
Qed.


Theorem d_sub_open_mono_bot_sub_bot: forall n1 n2 Ψ A T,
  d_typ_order (A ᵗ^^ₜ T) < n1 ->
  d_typ_size (A ᵗ^^ₜ T) < n2 ->
  Ψ ⊢ A ᵗ^^ₜ T <: typ_bot ->
  Ψ ᵗ⊢ᵈₘ T ->
  typ_sub_bot (typ_all A).
Proof with auto.
  intro n1. induction n1.
  - intros. inversion H.
  - intros n2. induction n2.
    + intros. inversion H0.
    + intros. dependent destruction H1; rename x into Heq.
      * destruct A; simpl in *; try solve [inversion Heq]...
        -- econstructor. intros. unfold open_typ_wrt_typ. simpl...
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H3.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
      * destruct A; simpl in *; try solve [ inversion Heq].
        -- destruct n.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                subst. inversion H7.
            ++ unfold open_typ_wrt_typ in Heq. simpl in *.
                inversion Heq.
        -- inversion Heq. subst. inst_cofinites_for typ_sb__all; intros.
          eapply typ_sub_bot_subst_inv with (X:=X) (T:=T); eauto. admit.
           simpl. eapply IHn1 with (Ψ:=Ψ) (T:=T0); eauto.

           ++ admit. 
           ++ admit.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
           ++ inversion Heq.
        -- inversion Heq. inst_cofinites_for typ_sb__all.
          intros.
        subst.
          eapply IHn1.
           constructor. eapply IHn2; eauto.
           ++ unfold open_typ_wrt_typ. simpl. lia.
           ++ unfold open_typ_wrt_typ. simpl. lia.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H3.
           ++ inversion Heq.
        -- inversion Heq. subst. apply typ_sb__intersection2. eapply IHn2; eauto.
           ++ unfold open_typ_wrt_typ. lia.
           ++ unfold open_typ_wrt_typ. lia.
      * destruct A; simpl in *; try solve [inversion Heq].
        -- destruct n.
           ++ unfold open_typ_wrt_typ in Heq. simpl in Heq.
              subst. dependent destruction H2.
           ++ inversion Heq.
        -- inversion Heq. subst. constructor.
           ++ eapply IHn2; unfold open_typ_wrt_typ; eauto. lia. lia. 
           ++ eapply IHn2; unfold open_typ_wrt_typ; eauto. lia. lia. 
Admitted.


Theorem d_mono_notin_stvar : forall Ψ2 Ψ1 T X,
  Ψ2 ++ X ~ ■ ++ Ψ1 ᵗ⊢ᵈₘ T ->
  uniq (Ψ2 ++ (X ~ ■) ++ Ψ1) ->
  X ∉ ftvar_in_typ T.
Proof.
  intros. dependent induction H; simpl in *; auto.
  - case_eq (X0 == X); intros; subst*; try solve_notin.
    assert (X ~ ■ ∈ᵈ (Ψ2 ++ (X, ■) :: Ψ1)) by eauto.
    unify_binds.
  - eauto.
Qed.

(* bookmark *)

Theorem d_sub_subst_stvar : forall Ψ1 X Ψ2 A B C,
  Ψ2 ++ (X ~ ■) ++ Ψ1 ⊢ A <: B ->
  Ψ1 ᵗ⊢ᵈ C ->
  map (subst_tvar_in_dbind C X) Ψ2 ++ Ψ1 ⊢ {C ᵗ/ₜ X} A <: {C ᵗ/ₜ X} B.
Proof with subst; eauto using d_wf_typ_weaken_app.
  intros. dependent induction H; try solve [simpl in *; eauto].
  - eapply d_sub_refl; auto...
  - simpl. inst_cofinites_for d_sub__all; intros X1 Hfr; inst_cofinites_with X1.
    + intros. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2... admit.
    + intros. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2... admit.  
    + repeat rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; eauto...
      rewrite_env (map (subst_tvar_in_dbind C X) (X1 ~ ■ ++ Ψ2) ++ Ψ1).
      eapply H2; auto...
  - simpl. destruct (dneq_all_intersection_union_subst_stv B C X) as [[? [? ?]] | ?]; eauto...
    + eapply d_sub__alll with (L:=L `union` singleton X) (T:={C ᵗ/ₜ X} T); auto...
      * intros. rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2... admit.
      * applys* d_mono_typ_subst_stvar... eauto using d_sub_d_wf_env.
      * rewrite <- subst_tvar_in_typ_open_typ_wrt_typ; eauto using d_wf_typ_lc_typ.
    + simpl. destruct_eq_atom. admit. (* *** *)
  - simpl. apply d_sub__intersection2. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_d_wf _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__intersection3. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_d_wf _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__union1. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_d_wf _ _ _ H) as [? [? ?]]. auto.
  - simpl. apply d_sub__union2. eauto.
    apply d_wf_typ_subst_stvar; auto...
    destruct (d_sub_d_wf _ _ _ H) as [? [? ?]]. auto.
Admitted.


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
      ( forall X , X \notin  L  -> d_sneq_stvar  ( X ~ dbind_tvar_empty  ++  Ψ )   ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sneq_stvar  ( X ~ dbind_tvar_empty  ++  Ψ )   ( open_typ_wrt_typ B1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_size  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A1 (typ_var_f X) )   ( open_typ_wrt_typ B1 (typ_var_f X) )  n )  ->
      d_sub_size Ψ (typ_all A1) (typ_all B1) (S n)
 | d_subs__alll : forall (L:vars) (Ψ:denv) (A1 B1 T1:typ) (n:nat),
     neq_all B1 ->
     neq_intersection B1 ->
     neq_union B1 ->
     ( forall X , X \notin  L  -> d_sneq_stvar  ( X ~ dbind_tvar_empty  ++  Ψ )   ( open_typ_wrt_typ A1 (typ_var_f X) )  )  ->
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
     d_sub_size Ψ (typ_union A1 A2) B1 (S (n1 + n2))
 | d_subs__all_refl : forall (L:vars) (Ψ:denv) (A1:typ) (n:nat),
     ( forall X , X \notin  L  -> d_sub_size  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) n )  ->
     d_sub_size Ψ (typ_all A1) (typ_all A1) (S n).
     
Notation "Ψ ⊢ A <: B | n" :=
  (d_sub_size Ψ A B n)
    (at level 65, A at next level, B at next level, no associativity) : type_scope.

Theorem d_sub_size_sound : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> Ψ ⊢ A <: B.
Proof.
  intros. induction H; eauto.
Qed.

#[local] Hint Constructors d_sub_size : core.

Lemma d_sub_dwft_sized : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> ⊢ᵈ Ψ /\ Ψ ᵗ⊢ᵈ A /\ Ψ ᵗ⊢ᵈ B.
Proof.
  intros. applys d_sub_d_wf. applys* d_sub_size_sound.
Qed.

Corollary d_sub_dwft_sized_0 : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> ⊢ᵈ Ψ.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

Corollary d_sub_dwft_sized_1 : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> Ψ ᵗ⊢ᵈ A.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

Corollary d_sub_dwft_sized_2 : forall Ψ A B n,
    Ψ ⊢ A <: B | n -> Ψ ᵗ⊢ᵈ B.
Proof.
  intros. forwards*: d_sub_dwft_sized H.
Qed.

#[local] Hint Resolve d_sub_dwft_sized_0 d_sub_dwft_sized_1 d_sub_dwft_sized_2 : core.


Lemma d_wf_env_all_stvar_after : forall Ψ1 Ψ2 X,
  d_wf_env (Ψ2 ++ X ~ ■ ++ Ψ1) ->
  all_stvar (Ψ2 ++ X ~ ■).
Proof.
  intros. dependent induction H; auto.
  - apply d_wf_tenv_stvar_false in H; contradiction.
  - destruct Ψ2; dependent destruction x.
    + constructor. constructor.
    + simpl. constructor. eapply IHd_wf_env with (Ψ1:=Ψ1); eauto.
Qed.


Lemma d_sub_size_rename_stvar : forall Ψ1 Ψ2 X Y A B n,
  Ψ2 ++ X ~ ■ ++ Ψ1 ⊢ A <: B | n ->
  Y ∉ (dom Ψ1 `union` dom Ψ2) ->
  (map (subst_tvar_in_dbind (typ_var_f Y) X) Ψ2) ++ Y ~ ■ ++ Ψ1 ⊢
        {typ_var_f Y ᵗ/ₜ X} A <: {typ_var_f Y ᵗ/ₜ X} B | n.
Proof with (simpl in *; eauto using d_wf_env_subst_tvar).
  intros * HS HN.
  case_eq (Y == X); intros.
  1: { subst. rewrite* map_subst_tvar_in_dbind_refl_eq.
       repeat rewrite* subst_tvar_in_typ_refl_eq. } clear H.

  gen Y.
  inductions HS; intros...
  - constructor.
    applys d_wf_env_subst_stvar; auto.
    rewrite_env ((Ψ2 ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ■ ++ Ψ1)...
    eapply d_wf_env_all_stvar_after with (Ψ1:=Ψ1); eauto.
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - constructor.
    applys d_wf_env_subst_stvar; auto.
    rewrite_env ((Ψ2 ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ■ ++ Ψ1)...
    eapply d_wf_env_all_stvar_after with (Ψ1:=Ψ1); eauto.
    solve_notin.
    applys d_wf_typ_rename_stvar...
  - constructor. 
    applys d_wf_env_subst_stvar; auto.
    rewrite_env ((Ψ2 ++ (X, ■) :: nil ) ++ [(Y, ■)] ++ Ψ1).
    applys d_wf_env_weaken_stvar.
    rewrite_env (Ψ2 ++ X ~ ■ ++ Ψ1)...
    eapply d_wf_env_all_stvar_after with (Ψ1:=Ψ1); eauto.
    solve_notin.
  (* - econstructor...
    applys d_wf_env_subst_stvar...
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
      eapply d_wf_typ_rename_stvar with (Y:=Y) in H0...
    + econstructor.
      applys* d_wf_env_rename_stvar...
      forwards: d_wf_typ_rename_stvar Y H0...
      case_if in H1...
  - pick fresh SZ and apply d_subs__all. inst_cofinites_with SZ.
    + admit.
    + admit.
    + rewrite_env (map (subst_tvar_in_dbind ` Y X) (SZ ~ ■ ++ Ψ2) ++ (Y, ■) :: Ψ1).
      repeat rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2; eauto.
  - pick fresh SZ and apply d_subs__alll.
    6: forwards* H4: IHHS;
    rewrite subst_tvar_in_typ_open_typ_wrt_typ in H4; eauto using d_wf_typ_lc_typ.
    1-3: auto...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      rewrite_env (map (subst_tvar_in_dbind ` Y X) (SZ ~  □ ++ Ψ2) ++ (Y, ■) :: Ψ1).
      eapply d_sneq_stvar_rename_dtvar...
    + applys d_mono_typ_subst_stvar.
      * rewrite_env ((Ψ2 ++ X ~ ■) ++ Y ~ ■ ++ Ψ1).
        applys* d_mono_typ_weaken. rewrite_env (Ψ2 ++ (X, ■) :: Ψ1)...
      * rewrite_env ((Ψ2 ++ X ~ ■) ++ Y ~ ■ ++ Ψ1).
        apply d_sub_dwft_sized_0 in HS. apply d_wf_env_uniq.
        apply d_wf_env_weaken_stvar; auto. rewrite_env (Ψ2 ++ (X, ■) :: Ψ1)...
        eapply d_wf_env_all_stvar_after with (Ψ1:=Ψ1); eauto.
      * now eauto.
  - applys d_subs__intersection2; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__intersection3; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__union1; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - applys d_subs__union2; forwards: IHHS...
    forwards: d_wf_typ_rename_stvar Y H...
  - admit.
Admitted.

Corollary d_sub_size_rename : forall n X Y Ψ1 Ψ2 A B,
    X ∉ ftvar_in_typ A `union` ftvar_in_typ B ->
    Y ∉ (dom Ψ1) `union` (dom Ψ2) ->
    Ψ2 ++ X ~ ■ ++ Ψ1 ⊢ A ᵗ^^ₜ ` X <: B ᵗ^^ₜ ` X | n ->
    map (subst_tvar_in_dbind (` Y) X) Ψ2 ++ Y ~ ■ ++ Ψ1 ⊢ A ᵗ^^ₜ ` Y <: B ᵗ^^ₜ ` Y | n.
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
  intros. induction H...
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
  - pick fresh X. destruct (H0 X) as [n]...
    exists (S n).
    inst_cofinites_for d_subs__all_refl. intros.
    inst_cofinites_with X0. 
    + rewrite_env (nil ++ X0 ~ ■ ++ Ψ). rewrite_env (nil ++ X ~ ■ ++ Ψ) in H1.
      applys d_sub_size_rename H1; solve_notin.
  Unshelve. all: econstructor.
Qed.


Lemma nat_suc: forall n n1, 
  n >= S n1 ->
  exists n1', n = S n1' /\ n1' >= n1.
Proof.
  intros. induction H.
  - exists n1. split; lia.
  - destruct IHle as [n1' [n2' Hn1n2]].
    exists (S n1'). split; lia.
Qed.

Lemma nat_split: forall n n1 n2, 
  n >= S (n1 + n2) ->
  exists n1' n2', n = S (n1' + n2') /\ n1' >= n1 /\ n2' >= n2.
Proof.
  intros. induction H.
  - exists n1, n2. split; lia.
  - destruct IHle as [n1' [n2' Hn1n2]].
    exists (S n1'), n2'. split; lia.
Qed.


Lemma d_sub_size_more: forall Ψ A B n,
  Ψ ⊢ A <: B | n -> 
  forall n', n' >= n -> Ψ ⊢ A <: B | n'.
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
  Ψ ⊢ (typ_union A1 A2) <: B | n -> 
  Ψ ⊢ A1 <: B | n /\ Ψ ⊢ A2 <: B | n.
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



Theorem d_sub_size_subst_stvar : forall Ψ1 Ψ2 X A B C n,
  Ψ2 ++ (X ~ ■) ++ Ψ1 ⊢ A <: B | n ->
  Ψ1 ᵗ⊢ᵈ C ->
  exists n', map (subst_tvar_in_dbind C X) Ψ2 ++ Ψ1 ⊢ {C ᵗ/ₜ X} A <: {C ᵗ/ₜ X} B | n'.
Proof.
  intros.
  apply d_sub_size_sound in H.
  apply d_sub_subst_stvar with (C:=C) in H; auto.
  apply d_sub_size_complete in H. auto.
Qed.

Inductive d_ord : typ -> Prop :=
  | d_ord__tvar : forall X, d_ord (typ_var_f X)
  | d_ord__bot : d_ord typ_bot
  | d_ord__top : d_ord typ_top
  | d_ord__unit : d_ord typ_unit
  | d_ord__arr : forall A1 A2,
      d_ord (typ_arrow A1 A2)
  | d_ord__all : forall A,
      d_ord (typ_all A)
  .

Inductive d_wft_ord : typ -> Prop :=
| d_wftord__base : forall A, d_ord A -> d_wft_ord A
| d_wftord__intersection: forall A1 A2,
    d_wft_ord A1 ->
    d_wft_ord A2 ->
    d_wft_ord (typ_intersection A1 A2)
| d_wftord__union: forall A1 A2,
    d_wft_ord A1 ->
    d_wft_ord A2 ->
    d_wft_ord (typ_union A1 A2)
.

#[local] Hint Constructors d_ord d_wft_ord : core.

Lemma d_wft_ord_complete: forall Ψ A,
  Ψ ᵗ⊢ᵈ A -> d_wft_ord A.
Proof with auto.
  intros. induction H; eauto...
Qed.

Theorem d_sub_mono_bot_false : forall Ψ T,
  Ψ ᵗ⊢ᵈₘ T ->
  Ψ ⊢ T <: typ_bot ->
  False.
Proof.
  intros. induction H; try solve [(dependent destruction H0); auto].
Qed.

(* Theorem d_sub_open_mono_bot_false: forall n1 n2 Ψ A T L,
  d_typ_order (A ᵗ^^ₜ T) < n1 ->
  d_typ_size (A ᵗ^^ₜ T) < n2 ->
  Ψ ⊢ A ᵗ^^ₜ T <: typ_bot ->
  (forall X, X ∉ L -> s_in X (A ᵗ^ₜ X)) ->
  Ψ ᵗ⊢ᵈₘ T ->
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
Qed. *)



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
              apply d_sub_d_wf in H1; destruct H1 as [_ [_ Hwtf1]];
              apply d_wft_ord_complete in Hwtf1; induction Hwtf1; solve_trans_forall_B_iu
   end
  end.

Ltac ord_inv :=
    match goal with
    | H : d_ord (typ_intersection _ _) |- _ => inversion H
    | H : d_ord (typ_union _ _)|- _ => inversion H
   end.


Lemma d_sub_size_transitivity : forall n_d_typ_order n_d_sub_size Ψ A B C n1 n2 ,
  d_typ_order B < n_d_typ_order ->
  n1 + n2 < n_d_sub_size ->
  Ψ ⊢ A <: B | n1 -> Ψ ⊢ B <: C | n2 -> Ψ ⊢ A <: C.
Proof with auto.
  induction n_d_typ_order; induction n_d_sub_size; intros * Horder Hsize Hsub1 Hsub2.
  - inversion Horder.
  - inversion Horder.
  - inversion Hsize.
  - dependent destruction Hsub1...
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_d_sub_size with (B:=typ_top) (n1:=n2); eauto...
        eapply IHn_d_sub_size with (B:=typ_top) (n1:=n1); eauto...
      * simpl in H. eapply d_sub__union1.
        eapply IHn_d_sub_size with (B:=typ_top) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub__union2.
        eapply IHn_d_sub_size with (B:=typ_top) (n1:=n); eauto...
        auto.
    + apply d_sub_size_sound in Hsub2.
      apply d_sub_d_wf in Hsub2; auto.
      eapply d_sub__bot; intuition.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_d_sub_size with (B:=typ_unit) (n1:=n2); eauto...
        eapply IHn_d_sub_size with (B:=typ_unit) (n1:=n1); eauto...
      * simpl in H. eapply d_sub__union1.
        eapply IHn_d_sub_size with (B:=typ_unit) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub__union2.
        eapply IHn_d_sub_size with (B:=typ_unit) (n1:=n); eauto...
        auto.
    + dependent destruction Hsub2...
      * econstructor.
        eapply IHn_d_sub_size with (B:=` X) (n1:=n2); eauto...
        eapply IHn_d_sub_size with (B:=` X) (n1:=n1); eauto...
      * simpl in H. eapply d_sub__union1.
        eapply IHn_d_sub_size with (B:=` X) (n1:=n); eauto...
        auto.
      * simpl in H. eapply d_sub__union2.
        eapply IHn_d_sub_size with (B:=` X) (n1:=n); eauto...
        auto.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_size_sound in Hsub1_2.
        apply d_sub_d_wf in Hsub1_1. apply d_sub_d_wf in Hsub1_2. econstructor; intuition.
      * econstructor.
        eapply IHn_d_sub_size with (B:=B1); eauto...
        eapply IHn_d_sub_size with (B:=B2); eauto...
      * econstructor.
        eapply IHn_d_sub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
        eapply IHn_d_sub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
      * apply d_sub__union1.
        eapply IHn_d_sub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
        auto.
      * apply d_sub__union2.
        eapply IHn_d_sub_size with (B:=typ_arrow B1 B2) (n1:=S(n1+n0)); eauto...
        auto.
    (* forall X. A < forall X. B < C *)
    + simpl in *. dependent destruction Hsub2...
      * econstructor...
        pick fresh Y and apply d_wf_typ__all.
        ** admit.
      * eapply d_sub__all with (L:=L `union` L0 `union` dom Ψ); auto;
        intros; inst_cofinites_with X. auto.
        eapply IHn_d_typ_order with (B:= B1 ᵗ^ₜ X); eauto...
        -- simpl in *. rewrite d_open_svar_same_order...
      * pick fresh Y and apply d_sub__alll. 5: applys H6. all: eauto.
        ** inst_cofinites_with Y. auto.
        ** pick fresh X. inst_cofinites_with X.
           replace Ψ with (map (subst_tvar_in_dbind T1 X) nil ++ Ψ) by auto.
          rewrite_env  (nil ++ (X, ■) :: Ψ) in H1.
          eapply d_sub_size_subst_stvar with (C:=T1) in H1; simpl; eauto.
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
        -- eapply IHn_d_sub_size with (B:=typ_all B1) (n1:=S n) (n2:=n1); eauto...
        -- eapply IHn_d_sub_size with (B:=typ_all B1) (n1:=S n) (n2:=n2); eauto...
      * eapply d_sub__union1.
        -- eapply IHn_d_sub_size with (B:=typ_all B1) (n1:=S n) (n2:=n0); eauto...
        -- auto.
      * eapply d_sub__union2.
        -- eapply IHn_d_sub_size with (B:=typ_all B1) (n1:=S n) (n2:=n0); eauto...
        -- auto.
    + simpl in *. assert (Ψ ᵗ⊢ᵈ B1) as Hwft1 by applys* d_sub_dwft_sized_1.
      dependent destruction Hwft1; solve_trans_forall_B_C.
      (* solve_trans_forall_B_C. *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
           applys* d_wf_typ_open_mono_inv.
        -- eapply d_sub__alll with (T:=T1) (L:=L); auto.
           eapply d_sub_size_sound; eauto.
      (* forall a. A < bot < C *)
      * admit.
      (* forall a. A < top < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
           applys* d_wf_typ_open_mono_inv.
      (* forall a. A < X < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all.
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
           applys* d_wf_typ_open_mono_inv.
        -- eapply d_sub__alll with (T:=T1); eauto...
            apply d_sub_size_sound in Hsub1. auto.
      (* forall a. A < X < C *)
      * admit.
      (* forall a. A < B1 -> B2 < C *)
      * dependent destruction Hsub2; try solve ord_inv; auto...
        -- econstructor...
           pick fresh Y and apply d_wf_typ__all. 
           forwards HW: d_sub_dwft_sized_1 Hsub1.
           rewrite_env (nil ++ Ψ) in HW.
           rewrite_env (nil ++ Y ~ □ ++ Ψ).
           applys* d_wf_typ_open_mono_inv.
        -- assert (Ψ ᵗ⊢ᵈ B1) by applys* d_sub_dwft_sized_1. assert (Ψ ᵗ⊢ᵈ B2) by applys* d_sub_dwft_sized_2.
          eapply d_sub__alll with (T:=T1); eauto...
          eapply IHn_d_sub_size with (B:=typ_arrow A0 A2) (n2:=S(n1+n2)); eauto...
      * inversion H.
      * inversion H1.
      * inversion H0.
    + simpl in *. dependent destruction Hsub2...
      * econstructor... apply d_sub_size_sound in Hsub1_1. apply d_sub_d_wf in Hsub1_1.
        intuition.
      * econstructor.
        eapply IHn_d_sub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
        eapply IHn_d_sub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
      * eapply IHn_d_sub_size with (B:=B1); eauto...
      * eapply IHn_d_sub_size with (B:=B2); eauto...
      * apply d_sub__union1...
        eapply IHn_d_sub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
      * apply d_sub__union2...
        eapply IHn_d_sub_size with (B:=typ_intersection B1 B2) (n1:=S(n1+n0)); eauto...
    + simpl in H. apply d_sub__intersection2...
      * eapply IHn_d_sub_size with (B:=B1) (n1:=n); eauto...
    + simpl in H. apply d_sub__intersection3...
      * eapply IHn_d_sub_size with (B:=B1) (n1:=n); eauto...
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_d_sub_size with (B:=B1) (n2:=n2); eauto... intuition.
    + simpl in Horder. apply d_sub_size_union_inv in Hsub2.
      eapply IHn_d_sub_size with (B:=B2) (n2:=n2); eauto... intuition.
    + simpl in Horder. econstructor...
      * eapply IHn_d_sub_size with (B:=B1) (n1:=n1); eauto...
      * eapply IHn_d_sub_size with (B:=B1) (n1:=n0); eauto...
Admitted.





Theorem sub_transitivity : forall Ψ A B C,
  Ψ ⊢ A <: B -> Ψ ⊢ B <: C -> Ψ ⊢ A <: C.
Proof.
  intros * Hab Hbc.
  apply d_sub_size_complete in Hab. destruct Hab as [n1].
  apply d_sub_size_complete in Hbc. destruct Hbc as [n2].
  eapply d_sub_size_transitivity; eauto.
Qed.
