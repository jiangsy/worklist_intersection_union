Require Import Coq.Program.Equality.

Require Import decl.notations.
Require Import decl.prop_ln_extra.
Require Import decl.prop_basic.
Require Import ln_utils.

Hint Constructors dsub : sub.

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


Lemma dsub_union_inversion : forall E S1 S2 T, 
  E ⊢ dtyp_union S1 S2 <: T -> 
  E ⊢ S1 <: T /\ E ⊢ S2 <: T.
Proof with auto with sub.
  intros.
  dependent induction H; auto...
  - inversion H. split; econstructor; auto.
  - specialize (IHdsub1 _ _ (eq_refl _)).
    specialize (IHdsub2 _ _ (eq_refl _)).
    destruct IHdsub1. destruct IHdsub2.
    intuition.
  - specialize (IHdsub _ _ (eq_refl _)).
    intuition.
  - specialize (IHdsub _ _ (eq_refl _)).
    intuition.
Qed.


Lemma dsub_intersection_inversion : forall E S T1 T2, 
  E ⊢ S <: dtyp_intersection T1 T2 -> 
  E ⊢ S <: T1 /\ E ⊢ S <: T2.
Proof with auto with sub.
  intros.
  dependent induction H; auto...
  - inversion H. auto.
  - inversion H0.
  - specialize (IHdsub _ _ (eq_refl _)).
    intuition.
  - specialize (IHdsub _ _ (eq_refl _)).
    intuition.
  - specialize (IHdsub1 _ _ (eq_refl _)).
    specialize (IHdsub2 _ _ (eq_refl _)).
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
     dneq_intersection T1 ->
     dneq_union T1 -> 
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

Hint Constructors dsub_sized : sub.

Theorem dsub_sized_wrt_dub_sound : forall E S T n,
  dsub_sized E S T n -> E ⊢ S <: T.
Proof.
  intros. induction H; eauto.
Qed.

Definition Snat := S.

Lemma dsub_sized_wrt_dub_complete : forall E T1 T2,
  E ⊢ T1 <: T2 -> exists n, dsub_sized E T1 T2 n.
Proof with eauto with sub.
  intros. induction H; eauto...
  - destruct IHdsub1 as [n1]. destruct IHdsub2 as [n2].
    eauto...
  - inst_cofinites_by L. destruct H2 as [n].
    exists (Snat n). eapply dsubsized_all with (L:=L); intros.
    + admit.
    + admit.
    + admit.
  - destruct IHdsub as [n]. eauto...
  - destruct IHdsub1 as [n1]. destruct IHdsub2 as [n2].
  eauto...
  - destruct IHdsub as [n]. eauto...
  - destruct IHdsub as [n]. eauto...
  - destruct IHdsub as [n]. eauto...
  - destruct IHdsub as [n]. eauto...
  - destruct IHdsub1 as [n1]. destruct IHdsub2 as [n2].
  eauto...
Admitted.

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

Theorem  d_sub_subst_mono : forall E X F S1 T1 T2,
  F ++ (X ~ dbind_tvar_empty) ++ E ⊢ S1 <: T1 ->
  E ⊢ T2 -> 
  dmono_typ T2 ->
  map (dsubst_tv_in_binding T2 X) F ++ E ⊢ {T2 /ᵈ X} S1 <: {T2 /ᵈ X} T1.
Proof with eauto with subtyping.
  intros. dependent induction H; try solve [simpl in *; eauto with subtyping].
  - eapply dsub_refl. auto...
  - eapply dsub_refl. auto...
  - simpl. eapply dsub_all with (L:=L); intros SX Hfr; inst_cofinites_with SX.
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + rewrite dtyp_subst_open_comm; auto...
      apply fstv_sin_dtyp_subst_tv; auto...
    + inst_cofinites_with SX. repeat rewrite dtyp_subst_open_comm; eauto...
      replace (SX ~ dbind_stvar_empty ++ map (dsubst_tv_in_binding T2 X) F ++ E) with 
      (map (dsubst_tv_in_binding T2 X) (SX ~ dbind_stvar_empty ++ F) ++ E) by auto.
      eapply H2; auto...
  - simpl. destruct T1; try solve [inversion H; inversion H0; inversion H1].
    +  eapply dsub_alll with (L:=L `union` singleton X) (T2:= {T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
          apply ftv_sin_dtyp_subst_inv; auto...
      * admit.
      * rewrite <- dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto... 
    + eapply dsub_alll with (L:=L `union` singleton X) (T2:= {T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
          apply ftv_sin_dtyp_subst_inv; auto...
      * admit.
      * rewrite <- dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto... 
    + eapply dsub_alll with (L:=L `union` singleton X) (T2:= {T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
          apply ftv_sin_dtyp_subst_inv; auto...
      * admit.
      * rewrite <- dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto... 
    + admit. (* hard : problematic *)
    + eapply dsub_alll with (L:=L `union` singleton X) (T2:= {T2 /ᵈ X} T0); auto...
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
          apply ftv_sin_dtyp_subst_inv; auto...
      * admit.
      * rewrite <- dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto... 
    + eapply dsub_alll with (L:=L `union` singleton X) (T2:= {T2 /ᵈ X} T0); simpl; auto...
      * admit.
      * admit.
      * admit.
      * intros. inst_cofinites_with X0. rewrite dtyp_subst_open_comm; auto...
        apply ftv_sin_dtyp_subst_inv; auto...
      * admit.
      * rewrite <- dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto... 
Admitted.


(* Theorem substitution : forall G1 G2 x A B t,
  G1 , x  ,, G2 ⊢ A <: B ->
  G1 ⊢ t -> ld_mono_type t ->
  G1 ,, G2 ⊢ [t /ᵈ x] A <: [t /ᵈ x] B.
Proof.
  intros.
  dependent induction H.
  - simpl. destruct (x0 == x). 
    + eapply ld_sub_refl. replace (G1,,G2) with (G1,,G2,,ld_ctx_nil) by auto.
      apply ld_wf_type_weakening; auto.
      simpl. replace (G1, x,, G2) with (G1 ,, (ld_ctx_nil, x),, G2) in H by auto.
      eapply ld_wf_ctx_weakening; eauto.
    + econstructor.
      * replace (G1, x,, G2) with (G1 ,, (ld_ctx_nil, x),, G2) in * by auto. eapply ld_wf_ctx_weakening; eauto.
      * eapply ld_in_context_other; eauto. 
  - simpl. constructor.
    replace (G1, x,, G2) with (G1 ,, (ld_ctx_nil, x),, G2) in * by auto. eapply ld_wf_ctx_weakening; eauto.
  - simpl. constructor; eauto.
  - simpl. eapply ld_sub_intersection_r.
    + apply IHld_sub1; auto.
    + apply IHld_sub2; auto.
  - simpl. eapply ld_sub_intersection_l1.
    + apply IHld_sub; auto.
    + apply ld_wf_type_subst; auto. 
  - simpl. eapply ld_sub_intersection_l2.
    + apply IHld_sub; auto.
    + apply ld_wf_type_subst; auto. 
  - simpl. eapply ld_sub_union_r1.
    + apply IHld_sub; auto.
    + apply ld_wf_type_subst; auto. 
  - simpl. eapply ld_sub_union_r2.
    + apply IHld_sub; auto.
    + apply ld_wf_type_subst; auto. 
  - simpl. eapply ld_sub_union_l.
    + apply IHld_sub1; auto.
    + apply IHld_sub2; auto.
  - simpl. eapply ld_sub_foralll with (t:=[t /ᵈ x] t0). 
    + apply ld_wf_mtype_subst; auto.
    + replace (([t /ᵈ x] A) ^^ᵈ ([t /ᵈ x] t0)) with ([t /ᵈ x] A ^^ᵈ t0).
      * apply IHld_sub; auto.
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type; auto. now apply ld_mono_is_ld_lc.
  - simpl. eapply ld_sub_forallr with (L:=L `union` singleton x).
    intros. inst_cofinites_with x0.
    rewrite_subst_open_var.
    replace  (([t /ᵈ x] B) ^^ᵈ ([t /ᵈ x] `ᵈ x0)) with ( [t /ᵈ x] B ^^ᵈ `ᵈ x0).
    + replace (G1,, G2, x0 ) with (G1,, (G2, x0)) by auto. apply H0; auto.
    + rewrite subst_ld_type_open_ld_type_wrt_ld_type. reflexivity. simpl.
      replace (G1,, G2, x0 ) with (G1,, (G2, x0)) by auto. now apply ld_mono_is_ld_lc.
Qed.




Lemma mono_type_order : forall t,
  ld_mono_type t -> type_order t = 0.
Proof.
  intros. induction H; simpl; auto; lia.
Qed. 

Lemma open_mono_order_rec : forall t A n,
  ld_mono_type t -> type_order (open_ld_type_wrt_ld_type_rec n t A) = type_order A.
Proof.
induction A; simpl; intros; auto.
- destruct (lt_eq_lt_dec n n0).
  + destruct s. auto. now apply mono_type_order.
  + auto.
Qed. 

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

Lemma transitivity' : forall n_dtyp_order n_dsub_size E R S T n1 n2 ,
  dtyp_order S < n_dtyp_order ->
  n1 + n2 < n_dsub_size -> 
  dsub_sized E R S n1 -> dsub_sized E S T n2 -> E ⊢ R <: T.
Proof.
Admitted.


Theorem transitivity : forall E R S T,
   E ⊢ R <: S -> E ⊢ S <: T -> E ⊢ R <: T.
Proof.
  intros E R S T Hrs Hst.
  apply dsub_sized_wrt_dub_complete in Hrs. destruct Hrs as [n1].
  apply dsub_sized_wrt_dub_complete in Hst. destruct Hst as [n2].
  eapply transitivity'; eauto.
Qed.