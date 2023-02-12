Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import decl.notations.
Require Import decl.ln_inf_extra.
Require Import ln_utils.


Definition wf_dom : forall {E}, ⊢ E -> atoms.
Proof.
  intros.
  set (x := dom E). exact x.
Defined.

(* Ltac gather_for_weakening :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : ld_context => ld_ctx_dom x) in
  let D := gather_atoms_with wf_dom in
  constr:(A `union` B `union` C `union` D).

Ltac apply_fresh_base_fixed H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  let x := fresh atom_name in
  pick fresh x excluding L and apply H.

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weakening" :=
  apply_fresh_base_fixed H gather_for_weakening x. *)


(* Lemma open_subst_eq : forall A x t, 
  x `notin` fv_ld_type A -> lc_ld_type t  ->
    A ^^ᵈ t = [t /ᵈ x] A ^^ᵈ (`ᵈ x).
Proof.
  intros.  
  rewrite subst_ld_type_open_ld_type_wrt_ld_type. simpl.
  rewrite eq_dec_refl.
  rewrite subst_ld_type_fresh_eq.
  all : auto.
Qed.  *)

Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.

(* Lemma ftv_in_dtyp_stvar_fstv_in_dtyp : forall X T,
  X `in` ftv_in_dtyp T ->
  X `in` fstv_in_dtyp ({dtyp_svar X /ᵈ X} T).
Proof.
  intros.
  induction T; auto.
  - simpl. destruct (X0 == X).
    + simpl. auto.
    + simpl in H. 
      specialize (notin_singleton_2 _ _ n). 
      intros. contradiction.
  - simpl. destruct (SX == X).
    + subst. auto.
    + simpl in H. 
      apply notin_empty in H. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed.

Lemma fstv_in_dtyp_subst_tv : forall SX X T T',
  SX `in` fstv_in_dtyp T ->
  SX `in` fstv_in_dtyp ({T' /ᵈ X} T).
Proof.
  intros.
  induction T; auto.
  - simpl. destruct (X0 == X).
    + subst. simpl in *. apply notin_empty in H.  contradiction.
    + simpl in H. 
      apply notin_empty in H. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed.

Lemma fstv_in_dtyp_tvar_ftv_in_dtyp : forall SX T,
  SX `in` fstv_in_dtyp T ->
  SX `in` ftv_in_dtyp ({dtyp_var_f SX /ₛᵈ SX} T).
Proof.
  intros.
  induction T; auto.
  - simpl in *. 
    apply notin_empty in H. contradiction.
  - simpl. destruct (SX0 == SX).
    + subst. auto.
    + simpl in H.
      apply AtomSetImpl.singleton_1 in H.
      subst. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed. *)

(* Lemma fstv_in_dtyp_subst_tv : forall SX X T T',
  SX `in` fstv_in_dtyp T ->
  SX `in` fstv_in_dtyp ({T' /ᵈ X} T).
Proof.
  intros.
  induction T; auto.
  - simpl. destruct (X0 == X).
    + subst. simpl in *. apply notin_empty in H.  contradiction.
    + simpl in H. 
      apply notin_empty in H. contradiction.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
  - simpl in H.
    destruct (AtomSetImpl.union_1 H).
    + simpl. apply AtomSetImpl.union_2. auto.
    + simpl. apply AtomSetImpl.union_3. auto.
Qed. *)

Hint Constructors ds_in_s: core.
Hint Constructors ds_in: core.

Lemma ftv_sin_dtyp_stvar_fstv_sin_dtyp : forall X T,
  ds_in X T ->
  ds_in_s X ({dtyp_svar X /ᵈ X} T).
Proof.
  intros. induction H; simpl; auto.
  - destruct (X == X).
    + constructor.
    + contradiction.
  - apply dsins_arrow1; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - apply dsins_all with (L:=L `union` singleton X). intros.
    inst_cofinites_with Y. 
    replace (({dtyp_svar X /ᵈ X} T) ^ᵈ Y) with ({dtyp_svar X /ᵈ X} T ^ᵈ Y).
    auto.
    rewrite dtyp_subst_open_comm; auto.
Qed.

Lemma fstv_sin_dtyp_subst_tv : forall SX X T T',
  ds_in_s SX T ->
  lc_dtyp T' ->
  ds_in_s SX ({T' /ᵈ X} T).
Proof.
  intros.
  induction H; simpl; auto.
  - apply dsins_arrow1; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - apply dsins_arrow2; auto.
    now apply dsubst_tv_in_dtyp_lc_dtyp.
  - simpl in H. 
    apply dsins_all with (L:=L `union` singleton X). intros.
    rewrite dtyp_subst_open_comm; auto.
Qed.


Lemma ftv_sins_dtyp_tvar_fstv_sin_dtyp : forall SX T,
  ds_in_s SX T ->
  ds_in SX ({dtyp_var_f SX /ₛᵈ SX} T).
Proof.
  intros. induction H; simpl; auto.
  - destruct (SX == SX).
    + constructor.
    + contradiction.
  - apply dsin_arrow1; auto.
    apply dsubst_stv_lc_dtyp; auto.
  - apply dsin_arrow2; auto.
    apply dsubst_stv_lc_dtyp; auto.
  - apply dsin_all with (L:=L `union` singleton SX). intros.
    inst_cofinites_with Y. 
    replace (({dtyp_var_f SX /ₛᵈ SX} T) ^ᵈ Y) with ({dtyp_var_f SX /ₛᵈ SX} T ^ᵈ Y).
    auto.
    rewrite dsubst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma fstv_sins_dtyp_subst_stv : forall SX X T T',
  ds_in X T ->
  lc_dtyp T' ->
  ds_in X ({T' /ₛᵈ SX} T).
Proof.
  intros.
  induction H; simpl; auto.
  - apply dsin_arrow1; auto.
    now apply dsubst_stv_lc_dtyp.
  - apply dsin_arrow2; auto.
    now apply dsubst_stv_lc_dtyp.
  - simpl in H. 
    apply dsin_all with (L:=L `union` singleton X). intros.
    rewrite dsubst_stv_in_dtyp_open_comm; auto.
Qed.

Lemma dwf_typ_s_tvar_stvar : forall E F X T,
  E ++ [(X, dbind_tvar_empty)] ++ F  ⊢ₛ T  -> 
  map (dsubst_tv_in_binding (dtyp_svar X) X ) E ++ [(X, dbind_stvar_empty)] ++ F ⊢ₛ { dtyp_svar X /ᵈ X } T.
Proof.
  intros E F X T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X).
    + econstructor; auto.
    + econstructor.
      induction E.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. constructor. 
    induction E.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. constructor.
    + apply IHdwf_typ_s1; auto.
    + apply IHdwf_typ_s2; auto.
  - simpl. eapply dwftyps_all with (L:=L);
    intros; inst_cofinites_with SX.
    + replace  (({dtyp_svar X /ᵈ X} T) ^^ᵈ dtyp_svar SX) with ({dtyp_svar X /ᵈ X} T ^^ᵈ dtyp_svar SX).
    apply fstv_sin_dtyp_subst_tv. auto.
    auto.
    rewrite dtyp_subst_open_comm; auto.
    + replace (SX ~ dbind_stvar_empty ++
    map (dsubst_tv_in_binding (dtyp_svar X) X) E ++ (X, dbind_stvar_empty) :: F
    ) with (
    map (dsubst_tv_in_binding (dtyp_svar X) X) (SX ~ dbind_stvar_empty ++ E) ++ (X, dbind_stvar_empty) :: F
    ) by auto.
    replace (({dtyp_svar X /ᵈ X} T) ^^ᵈ dtyp_svar SX) with 
    ({dtyp_svar X /ᵈ X} T ^^ᵈ dtyp_svar SX).
    apply H1. auto. 
    rewrite dtyp_subst_open_comm; auto. 
  - simpl. constructor.
    + apply IHdwf_typ_s1; auto.
    + apply IHdwf_typ_s2; auto.
  - simpl. constructor.
    + apply IHdwf_typ_s1; auto.
    + apply IHdwf_typ_s2; auto.
Qed.


Lemma dwf_typ_stvar_tvar : forall E F SX T,
  E ++ [(SX, dbind_stvar_empty)] ++ F  ⊢ T  -> 
  map (dsubst_stv_in_binding (dtyp_var_f SX) SX ) E ++ [(SX, dbind_tvar_empty)] ++ F ⊢ { dtyp_var_f SX /ₛᵈ SX } T.
Proof.
  intros E F SX T H.
  dependent induction H; try solve [simpl; auto].
  - simpl. constructor. 
    induction E.
    * simpl in *. inversion H.
      -- inversion H0.
      -- auto.
    * destruct a. inversion H.
      -- inversion H0. subst. simpl. auto.
      -- simpl. auto.
  - simpl. unfold eq_dec. destruct (EqDec_eq_of_X SX0 SX).
    + econstructor; auto.
    + econstructor.
      induction E.
      * simpl in *. inversion H.
        -- inversion H0. subst. contradiction.
        -- auto.
      * destruct a. inversion H.
        -- inversion H0. subst. simpl. auto.
        -- simpl. auto.
  - simpl. constructor.
    + apply IHdwf_typ1; auto.
    + apply IHdwf_typ2; auto.
  - simpl. eapply dwftyp_all with (L:=L);
    intros; inst_cofinites_with X.
    + replace  (({`ᵈ SX /ₛᵈ SX} T) ^ᵈ X) with ({`ᵈ SX /ₛᵈ SX} T ^ᵈ X).
      apply fstv_sins_dtyp_subst_stv; auto.
      rewrite dsubst_stv_in_dtyp_open_comm; auto.
    + replace (X ~ dbind_tvar_empty ++
    map (dsubst_stv_in_binding `ᵈ SX SX) E ++ (SX, dbind_tvar_empty) :: F) with (
    map (dsubst_stv_in_binding `ᵈ SX SX) (X ~ dbind_tvar_empty ++ E) ++ (SX, dbind_tvar_empty) :: F) by auto.
      replace (({`ᵈ SX /ₛᵈ SX} T) ^ᵈ X) with ({`ᵈ SX /ₛᵈ SX} T ^ᵈ X).
      apply H1. auto. 
      rewrite dsubst_stv_in_dtyp_open_comm; auto.
  - simpl. constructor.
    + apply IHdwf_typ1; auto.
    + apply IHdwf_typ2; auto.
  - simpl. constructor.
    + apply IHdwf_typ1; auto.
    + apply IHdwf_typ2; auto.
Qed.


Lemma dwf_typ_dwf_typ_s : forall E T, 
  E ⊢ T -> E ⊢ₛ T.
Proof.
  intros.   
  induction H; auto.
  - eapply dwftyps_all with (L:= (L `union` ftv_in_dtyp T)); 
    intros; inst_cofinites_with SX.  
    + replace (T ^^ᵈ dtyp_svar SX) with ({dtyp_svar SX /ᵈ SX}T ^ᵈ SX).
      now apply ftv_sin_dtyp_stvar_fstv_sin_dtyp.
      rewrite dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X SX SX).
      * rewrite dsubst_tv_in_dtyp_fresh_eq; auto.
      * contradiction.
    + replace (SX ~ dbind_tvar_empty ++ E) with (nil ++ SX ~ dbind_tvar_empty ++ E) in H1 by auto.
    specialize (dwf_typ_s_tvar_stvar _ _ _ _ H1).
      intros. rewrite dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp in H3; auto. simpl in H3. unfold eq_dec in H3. destruct (EqDec_eq_of_X SX SX).
      * rewrite dsubst_tv_in_dtyp_fresh_eq in H3; auto.
      * contradiction.
Qed.

Lemma dwf_typ_s_dwf_typ : forall E T, 
  E ⊢ₛ T -> E ⊢ T.
Proof.
  intros. induction H; auto.
  - eapply dwftyp_all with (L:= (L `union` fstv_in_dtyp T)); 
    intros; inst_cofinites_with X.  
    + replace (T ^ᵈ X) with ({dtyp_var_f X /ₛᵈ X} T ^^ᵈ dtyp_svar X).
      now apply ftv_sins_dtyp_tvar_fstv_sin_dtyp.
      rewrite dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp; auto.
      simpl. unfold eq_dec. destruct (EqDec_eq_of_X X X).
      * rewrite dsubst_stv_in_dtyp_fresh_eq; auto.
      * contradiction.
    + replace (X ~ dbind_stvar_empty ++ E) with (nil ++ X ~ dbind_stvar_empty ++ E) in H1 by auto.
      specialize (dwf_typ_stvar_tvar _ _ _ _ H1). intros. 
      rewrite dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp in H3; auto. simpl in H3. unfold eq_dec in H3. destruct (EqDec_eq_of_X X X).
      * rewrite dsubst_stv_in_dtyp_fresh_eq in H3; auto.
      * contradiction.
Qed.

Hint Constructors dsub.
Hint Resolve dwf_typ_dwf_typ_s : core.
Hint Resolve dwf_typ_s_dwf_typ : core.

Lemma dsub_dwft : forall E T1 T2,
  E ⊢ T1 <: T2 -> E ⊢ T1 /\ E ⊢ T2.
Proof.
  intros.
  induction H; intuition.
Admitted.

Hint Constructors dneq_union : Core.
Hint Constructors dneq_intersection : Core.

Lemma dwf_typ_dlc_type : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
  intros; induction H; auto.
Qed.

Lemma dwf_typ_s_dlc_type : forall E T,
  E ⊢ₛ T -> lc_dtyp T.
Proof.
  intros.
  eapply dwf_typ_dlc_type.
  apply dwf_typ_s_dwf_typ.
  eauto.
Qed.

Hint Resolve dwf_typ_s_dlc_type : core.

Lemma dsub_refl' : forall E T, 
  E ⊢ₛ T -> E ⊢ T <: T.
Proof.
  intros; dependent induction H; eauto.
  - inst_cofinites_by L. eapply dsub_forall with (SX:=x); eauto.
  - apply dsub_union3; auto.
  - apply dsub_intersection1; auto.
Qed. 

(* Lemma dsub_refl' : forall E T, 
  E ⊢ₛ T -> (E ⊢ T <: T /\ (forall T2, E ⊢ₛ T2 -> E ⊢ T <: dtyp_union T T2) /\ (forall T2, E ⊢ₛ T2 -> E ⊢ T <: dtyp_union T2 T)).
Proof.
  intros. dependent induction H; try solve [intuition].
  - intuition. 
    apply dsub_union1; auto.
    econstructor; eauto.
    apply dsub_union2; auto.
    econstructor; eauto.
  - admit.
  - split. 
    + apply dsub_union3.
      destruct IHdwf_typ_s1. intuition.
      destruct IHdwf_typ_s2. intuition.
    + split; intros.
      apply dsub_union3.

    intuition.
  
   intro.
  - induction. admit.
  - split.
    + apply dsub_union3. intuition. intuition.
    

   apply dsub_union3. 
    + generalize dependent T2. 
      dependent induction H; intros; auto;
      try solve [dependent destruction H;
                  apply dsub_union1; auto; constructor; eauto 3].
      * apply dsub_union1; auto. constructor; eauto.
      * clear IHdwf_typ_s1. clear IHdwf_typ_s2. clear IHdwf_typ_s3.
        dependent induction IHdwf_typ_s0.
        inversion H1.
        inversion H1.
        apply IHIHdwf_typ_s0_1; auto.
      * admit.
    + 

    + dependent induction IHdwf_typ_s2; auto;
      try solve [eapply dsub_union2; eauto 3].
  - apply dsub_intersection1.
    + dependent induction IHdwf_typ_s1; auto.
      * eapply dsub_intersection2; eauto 3. admit.
      * eapply dsub_intersection2; eauto 3. 
        constructor.

      try solve [eapply dsub_intersection2; eauto 3].
    + dependent induction IHdwf_typ_s2; auto;
    try solve [eapply dsub_union2; eauto 3].
  econstructor.
Admitted. *)

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
Proof.
  intros.
  dependent induction H; auto.
  - inversion H. split; econstructor; auto.
  - specialize (IHdsub1 _ _ (eq_refl _)).
    specialize (IHdsub2 _ _ (eq_refl _)).
    destruct IHdsub1. destruct IHdsub2.
    split; constructor; auto.
  - specialize (IHdsub _ _ (eq_refl _)).
    split; apply dsub_union1; intuition.
  - specialize (IHdsub _ _ (eq_refl _)).
    split; apply dsub_union2; intuition.
Qed.


Lemma dsub_intersection_inversion : forall E S T1 T2, 
  E ⊢ S <: dtyp_intersection T1 T2 -> 
  E ⊢ S <: T1 /\ E ⊢ S <: T2.
Proof.
  intros.
  dependent induction H; auto.
  - inversion H. split; econstructor; auto.
  - inversion H0.
  - specialize (IHdsub _ _ (eq_refl _)).
    split; apply dsub_intersection2; intuition.
  - specialize (IHdsub _ _ (eq_refl _)).
    split; apply dsub_intersection3; intuition.
  - specialize (IHdsub1 _ _ (eq_refl _)).
    specialize (IHdsub2 _ _ (eq_refl _)).
    intuition.
Qed.

(* Lemma ld_in_context_exact : 
  forall G1 G3 x, 
    ld_in_context x (G1,x,,G3).
Proof.
  intros.
  induction G3.
  - simpl. econstructor.
  - simpl. apply ld_inc_there.
    auto.
Qed.

Lemma ld_in_context_weakenning : 
  forall G1 G2 G3 x, 
    ld_in_context x (G1,,G3) -> ld_in_context x (G1,, G2,, G3).
Proof.
  intros.
  induction G3.
  - induction G2.
    + auto.
    + simpl in *. auto.
  - simpl in *.  dependent destruction H.
    + apply ld_inc_here.
    + apply ld_inc_there. auto.
Qed.

Corollary ld_in_context_weakenning_single: 
  forall G1 G3 x x', 
    ld_in_context x (G1,,G3) -> ld_in_context x (G1, x',, G3).
Proof.
  intros.
  replace (G1, x',, G3) with (G1,, (ld_ctx_nil, x'),,G3) by auto.
  apply ld_in_context_weakenning. auto.
Qed.


Lemma ld_in_ctx_dom_weakenning : 
  forall G1 G2 G3 x, 
   x `notin` (ld_ctx_dom (G1,, G2,, G3)) -> x `notin` (ld_ctx_dom (G1,,G3)) .
Proof.
  intros.
  induction G3.
  - induction G2.
    + auto.
    + simpl in *. auto.
  - simpl in *. apply notin_add_3.
    + apply notin_add_1 in H. auto.
    + apply IHG3. apply notin_add_2 in H. auto.
Qed.

Theorem ld_wf_type_weakening : 
  forall G1 G2 G3 t, 
  G1 ,, G3 ⊢ t -> 
  ⊢ G1 ,, G2 ,, G3 -> 
  G1 ,, G2 ,, G3 ⊢ t.
Proof.
  intros.
  dependent induction H; auto.
  - constructor. auto. eapply ld_in_context_weakenning. auto.
  - eapply ld_wft_forall with (L:=L `union` ld_ctx_dom (G1,, G2,, G3)). intros.
    inst_cofinites_with x. replace (G1,, G2,, G3, x ) with (G1,, G2,, (G3, x)) by auto. apply H0; auto.
    simpl. econstructor; eauto.
Qed.


Lemma ld_wf_type_fv: forall G t x, 
  G ⊢ t -> x `notin` ld_ctx_dom G -> x `notin` fv_ld_type t.
Proof.
  intros.
  induction H; simpl in *; auto.
  - induction G.
    + inversion H1.
    + inversion H1; subst.
      * simpl in H0. auto.
      * inversion H. simpl in H0. apply IHG; auto.
  - inst_cofinites_by (L `union` singleton x).
    assert (x ∉ add x0 (ld_ctx_dom G)) by auto.
    specialize (H1 H2). 
    simpl in H1.
    rewrite fv_ld_type_open_ld_type_wrt_ld_type_lower.
    eauto.
Qed.


Theorem ld_wf_ctx_weakening : forall G3 G1 G2,
  ⊢ G1 ,, G2 ,, G3 -> ⊢ G1 ,, G3.
Proof.
  induction G3; intros.
  - induction G2; auto.
    + simpl in *. apply IHG2. dependent destruction H. auto.
  - simpl in *. dependent destruction H. econstructor. 
    + eapply IHG3. eauto.
    + eapply ld_in_ctx_dom_weakenning. eauto.
Qed.
  
Theorem ld_wf_mtype_weakening : 
  forall G1 G2 G3 t, 
  ld_wf_mtype (G1 ,, G3) t -> ⊢ G1 ,, G2 ,, G3 ->
  ld_wf_mtype (G1 ,, G2 ,, G3) t.
Proof.
  intros.
  dependent induction H; eauto.
  - econstructor; eauto. now apply ld_in_context_weakenning.
Qed.


Theorem ld_sub_weakening: 
  forall G1 G2 G3 t1 t2, 
  G1 ,, G3 ⊢ t1 <: t2 -> ⊢ G1 ,, G2 ,, G3 -> 
  G1 ,, G2 ,, G3 ⊢ t1 <: t2.
Proof.
  intros.
  dependent induction H; auto.
  - constructor; auto. eapply ld_in_context_weakenning. auto.
  - constructor; auto. eapply ld_wf_type_weakening; eauto.
  - apply ld_sub_intersection_l2. auto. eapply ld_wf_type_weakening; eauto.
  - apply ld_sub_union_r1. auto. eapply ld_wf_type_weakening; eauto.
  - apply ld_sub_union_r2. auto. eapply ld_wf_type_weakening; eauto.
  - eapply ld_sub_foralll with (t:=t); auto.
    eapply ld_wf_mtype_weakening; auto.
  - pick fresh x and apply ld_sub_forallr for weakening.
    replace (G1,, G2,, G3, x) with (G1,, G2,, (G3, x)) by auto.
    eapply H0; auto. constructor; auto.
Qed.


Theorem ld_in_context_other : forall G1 G2 x x', 
  x <> x' -> ld_in_context x (G1, x',,G2) -> ld_in_context x (G1,,G2).
Proof.
  intros.
  induction G2.
  - simpl in *. dependent destruction H0.
    + contradiction.
    + auto.
  - simpl in *. dependent destruction H0.
    + econstructor.
    + constructor. auto. 
Qed.


Theorem ld_wf_mtype_equiv_ld_wf_type_and_mono : forall G t,
  ld_wf_mtype G t <-> G ⊢ t /\ ld_mono_type t.
Proof.
  intros. split; intros.
  - dependent induction H; auto. 
    split; intuition.
    + split. constructor; intuition. constructor; intuition.
    + split. constructor; intuition. constructor; intuition.
  - inversion H. dependent induction H0; auto.
    + dependent destruction H1. intuition.
    + inversion H1. constructor; intuition.
    + destruct H. inversion H0. constructor; intuition. 
    + inversion H2.
Qed.


Theorem ld_wf_type_subst_var: forall G1 G2 x x' A,
  G1, x,, G2 ⊢ A ->  ⊢ G1, x',, G2 -> G1, x',, G2 ⊢ [`ᵈ x' /ᵈ x] A.
Proof.
  intros.
  dependent induction H; simpl; auto.
  - destruct (x0 == x); subst.
    + constructor. auto. 
      now apply ld_in_context_exact.
    + constructor; auto.
      apply ld_in_context_other in H0.
      apply ld_in_context_weakenning_single; auto.
      auto.
  - eapply ld_wft_forall with (L:=L `union` (singleton x) `union` (ld_ctx_dom (G1, x',, G2))).
    intros. inst_cofinites_with x0.
    replace (G1, x',, G2, x0) with (G1, x',, (G2, x0)) by auto.
    replace (([`ᵈ x' /ᵈ x] t) ^ᵈ x0) with ([`ᵈ x' /ᵈ x] t ^ᵈ x0).
    apply H0; eauto.
    simpl. constructor; auto.
    rewrite subst_ld_type_open_ld_type_wrt_ld_type. simpl.
    apply notin_union_2 in H2. apply notin_union_1 in H2.
    apply notin_singleton_1' in H2.  unfold not in H2. 
    + destruct (x0 == x); auto.
      * subst. contradiction.
    + auto.
Qed.

Ltac rewrite_subst_open_var :=
  repeat
    match goal with 
      | _ : _ |-  context [ ([?e /ᵈ ?x] ?A) ^^ᵈ `ᵈ ?x' ] => 
        replace (`ᵈ x') with ([e /ᵈ x] `ᵈ x') by (apply subst_ld_type_fresh_eq; auto)
    end; repeat rewrite <- subst_ld_type_open_ld_type_wrt_ld_type by auto.



Theorem ld_wf_mtype_subst :
  forall G1 G2 x t t', 
    ld_mono_type t' -> ld_wf_mtype (G1, x,, G2) t -> G1 ⊢ t' ->  ld_wf_mtype (G1,, G2) ([t' /ᵈ x] t).
Proof.
  intros.
  dependent induction H0.
  - simpl. econstructor. 
    replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H0 by auto. eapply ld_wf_ctx_weakening; eauto.
  - simpl. destruct (x0 == x).
    + apply ld_wf_mtype_equiv_ld_wf_type_and_mono. intuition.
      replace (G1,,G2) with (G1,,G2,,ld_ctx_nil) by auto. eapply ld_wf_type_weakening. eauto.
      simpl.  replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H1 by auto. eapply ld_wf_ctx_weakening; eauto.
    + constructor.
      * replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H1 by auto. eapply ld_wf_ctx_weakening; eauto.
      * eapply ld_in_context_other; eauto.    
  - simpl. constructor.
    + apply IHld_wf_mtype1; auto.
    + apply IHld_wf_mtype2; auto.  
  - simpl. constructor.
    + apply IHld_wf_mtype1; auto.
    + apply IHld_wf_mtype2; auto.
  - simpl. constructor.
    + apply IHld_wf_mtype1; auto.
    + apply IHld_wf_mtype2; auto.
Qed.



Theorem ld_mono_is_ld_lc : forall t, 
  ld_mono_type t -> lc_ld_type t.
Proof.
  intros. induction H; auto.
Qed.

Theorem ld_wf_type_subst :
  forall G1 G2 x t t', 
    ld_mono_type t' -> ld_wf_type (G1, x,, G2) t -> G1 ⊢ t' ->  ld_wf_type (G1,, G2) ([t' /ᵈ x] t).
Proof.
  intros.
  dependent induction H0.
  - simpl. econstructor. 
    replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H0 by auto. eapply ld_wf_ctx_weakening; eauto.
  - simpl. destruct (x0 == x).
    + replace (G1,,G2) with (G1,,G2,,ld_ctx_nil) by auto. eapply ld_wf_type_weakening. eauto.
      simpl.  replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H1 by auto. eapply ld_wf_ctx_weakening; eauto.
    + constructor.
      * replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H1 by auto. eapply ld_wf_ctx_weakening; eauto.
      * eapply ld_in_context_other; eauto.    
  - simpl. constructor.
    + apply IHld_wf_type1; auto.
    + apply IHld_wf_type2; auto.  
  - simpl. constructor.
    + apply IHld_wf_type1; auto.
    + apply IHld_wf_type2; auto.
  - simpl. constructor.
    + apply IHld_wf_type1; auto.
    + apply IHld_wf_type2; auto.
  - replace ([t' /ᵈ x] ld_t_forall t) with (ld_t_forall ([t' /ᵈ x] t)) by auto.
    eapply ld_wft_forall with (L:=L `union` singleton x). intros. 
    replace (([t' /ᵈ x] t) ^ᵈ x0) with ([t' /ᵈ x] t ^ᵈ x0).
    replace (G1,, G2, x0) with (G1,, (G2, x0)) by auto. eapply H0; eauto.
    + rewrite subst_ld_type_open_ld_type_wrt_ld_type. 
    simpl. apply notin_union_2 in H3.
    apply notin_singleton_1' in H3.  unfold not in H3. 
    destruct (x0 == x).
    * subst. contradiction.
    * auto.
    * now apply ld_mono_is_ld_lc.
Qed. *)


(* Theorem ld_union_sub_inv: forall G A1 A2 B,
  G ⊢ ld_t_union A1 A2 <: B -> G ⊢ A1 <: B /\ G ⊢ A2 <: B.
Proof.
  intros.
  dependent induction H; auto.
  - specialize (IHld_sub1 A1 A2 (eq_refl _)).
    specialize (IHld_sub2 A1 A2 (eq_refl _)).
    split; apply ld_sub_intersection_r; intuition.
  - specialize (IHld_sub A1 A2 (eq_refl _)).
    split; apply ld_sub_union_r1; intuition.
  - specialize (IHld_sub A1 A2 (eq_refl _)).
    split; apply ld_sub_union_r2; intuition.
  - split; apply ld_sub_forallr with (L:=L); intros; 
    inst_cofinites_with x; 
    specialize (H0 A1 A2 (eq_refl _)); intuition.
Qed. *)



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



Fixpoint type_order (t : ld_type) : nat :=
  match t with
  | ld_t_arrow A B => type_order A + type_order B
  | ld_t_forall A  => S (type_order A)
  | ld_t_intersection A B => type_order A + type_order B
  | ld_t_union A B => type_order A + type_order B
  | _ => 0
  end.

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

Reserved Notation "G ⊢ t1 <: t2 | n"
  (at level 65, t1 at next level, t2 at next level, no associativity).
Inductive sized_ld_sub : ld_context -> ld_type -> ld_type -> nat -> Prop :=
  | sls_var : forall G x n,
    ⊢ G ->  ld_in_context x G -> G ⊢ (ld_t_var_f x) <: (ld_t_var_f x) | n
  | sls_int : forall G n,
    ⊢ G -> G ⊢ ld_t_int <: ld_t_int | n
  | sls_arrow : forall G A B C D n1 n2,
    G ⊢ C <: A | n1 ->
    G ⊢ B <: D | n2 ->
    G ⊢ (ld_t_arrow A B) <: (ld_t_arrow C D) | S (n1 + n2)
  | sls_intersection_r : forall G A B1 B2 n1 n2,
    G ⊢ A <: B1 | n1 ->
    G ⊢ A <: B2 | n2 -> 
    G ⊢ A <: (ld_t_intersection B1 B2) | S (n1 + n2)
  | sls_intersection_l1 : forall G A1 A2 B n1,
    G ⊢ A1 <: B | n1 ->
    ld_wf_type G A2 -> 
    G ⊢ (ld_t_intersection A1 A2) <: B | S n1
  | sls_intersection_l2 : forall G A1 A2 B n2,
    G ⊢ A2 <: B | n2 ->
    ld_wf_type G A1 -> 
    G ⊢ (ld_t_intersection A1 A2) <: B | S n2
  | sls_union_r1 : forall G A B1 B2 n1,
    G ⊢ A <: B1 | n1 ->
    ld_wf_type G B2 ->
    G ⊢ A <: (ld_t_union B1 B2) | S n1
  | sls_union_r2 : forall G A B1 B2 n2,
    G ⊢ A <: B2 | n2 ->
    ld_wf_type G B1 ->
    G ⊢ A <: (ld_t_union B1 B2) | S n2
  | sls_union_l : forall G A1 A2 B n1 n2,
    G ⊢ A1 <: B | n1 ->
    G ⊢ A2 <: B | n2 ->
    G ⊢ (ld_t_union A1 A2) <: B | S ( n1 + n2)
  | sls_foralll : forall G A B t n,
    ld_wf_mtype G t ->
    G ⊢ (open_ld_type_wrt_ld_type A t) <: B | n ->
    G ⊢ (ld_t_forall A) <: B | S n
  | sls_forallr : forall L G A B n,
    (forall x, x \notin L -> (ld_ctx_cons G x) ⊢ A <: (open_ld_type_wrt_ld_type B (ld_t_var_f x)) | n) ->
    G ⊢ A <: (ld_t_forall B) | S n
where "G ⊢ t1 <: t2 | n" := (sized_ld_sub G t1 t2 n).


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


Lemma ld_wf_type_is_wf_ctx : forall G A,
  G ⊢ A -> ⊢ G.
Proof.
  intros. induction H; auto.
  inst_cofinites_with_new. dependent destruction H0.
  auto.
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

Theorem transitivity : forall G A B C,
   G ⊢ A <: B -> G ⊢ B <: C -> G ⊢ A <: C.
Proof.
  intros.
  apply ld_sub_to_sized_ld_sub in H. destruct H as [n1].
  apply ld_sub_to_sized_ld_sub in H0. destruct H0 as [n2].
  eapply generalized_transitivity; eauto.
Qed.
 *)

Scheme dcheck_mut := Induction for dchk Sort Prop
  with dinfer_mut := Induction for dinf Sort Prop
  with dinferapp_mut := Induction for dinfapp Sort Prop.

(* Theorem progress.  *)

Lemma desub_same_dom : forall E E', 
  desub E' E ->
  dom E = dom E'.
Proof.
  intros. induction H; simpl; auto; rewrite IHdesub; auto.
Qed.

Lemma desub_same_tvar : forall E E' X, 
  desub E' E ->
  binds X dbind_tvar_empty E ->
  binds X dbind_tvar_empty E'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.

Lemma desub_same_stvar : forall E E' SX, 
  desub E' E ->
  binds SX dbind_stvar_empty E ->
  binds SX dbind_stvar_empty E'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.


Lemma desub_wf_typ : forall E T, 
  E ⊢ T -> 
  forall E', 
    desub E' E ->
    E' ⊢ T.
Proof.
  intros E T H. induction H; intros; auto.
  - econstructor. 
    eapply desub_same_tvar; eauto.
  - econstructor.
    eapply desub_same_stvar; eauto.
  - eapply dwftyp_all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed.

Hint Resolve desub_wf_typ : core.


Theorem check_subsumtion : forall E e S,
  E ⊢ e ⇐ S ->
  forall  E' T, 
    desub E' E ->
    E ⊢ S <: T ->
    E' ⊢ e ⇐ T
with 
infer_subsumption : forall E e T, 
  E ⊢ e ⇒ T ->
  forall E',
    desub E' E ->
    exists S, 
      dsub E S T /\ E' ⊢ e ⇒ S
with 
inferapp_subsumtion : forall E T1 e T2,
  E ⊢ T1 • e ⇒⇒ T2 ->
  forall E' S1, 
    desub E' E -> 
    E ⊢ S1 <: T1 -> 
    exists S2, 
      E ⊢ S2 <: T2 /\ E' ⊢ S1 • e ⇒⇒ S2.
Proof.
  - intros E e S H.
    induction H; auto; intros.
    + dependent induction H2; auto.
      * eapply dchk_top_abs with (L:=L `union` dom E). 
        intros. inst_cofinites_with x.
        apply H0; auto.
        econstructor; auto.
      * apply dchk_union1.
        -- apply IHdsub; auto.
        -- eapply desub_wf_typ; eauto.
      * apply dchk_union2.
        -- apply IHdsub; auto.
        -- eapply desub_wf_typ; eauto.
    + dependent induction H3. 
      * apply dchk_top_abs with (L:=L `union` dom E). intros.
      inst_cofinites_with x.
      dependent destruction H3.
      apply H1; auto.
      econstructor; auto.
      constructor.
      admit. (* easy: weakening *)
      * eapply dchk_abs with (L:=L).
        -- admit.
        -- intros. inst_cofinites_with x.  
          apply H1. econstructor; eauto.
          admit.
      * apply dchk_intersection; eauto.
      * apply dchk_union1; eauto. 
      * apply dchk_union2; eauto.
    + specialize (infer_subsumption _ _ _ H _ H1).
      destruct infer_subsumption as [S1 [Hsub Hinf]].
      specialize (inferapp_subsumtion _ _ _ _ H0 _ _ H1 Hsub).
      destruct inferapp_subsumtion as [S2 [Hsub2 Hinfapp]].
      eapply dchk_sub with (S:=S2).
      eapply dinf_app with (T2:=S1); auto.
      admit. (* easy *)
    + admit.
Admitted.





Theorem check_subsumtion : forall E e S,
  E ⊢ e ⇐ S ->
  forall  E' T, 
    desub E' E ->
    E ⊢ S <: T ->
    E' ⊢ e ⇐ T.
Proof.
  intros E e S H.
  pattern E, e, S, H.
  Print dcheck_mut.
  eapply dcheck_mut with (d:=E) (d0:=e) (d1:=S) 
    (P0 := fun E e T (pf : E ⊢ e ⇒ T) => 
      forall E', desub E' E -> exists S, dsub E S T /\ E' ⊢ e ⇒ S)
    (P1 := fun E T1 e T2 (pf : E ⊢ T1 • e ⇒⇒ T2 ) => 
      forall E' S1, desub E' E -> E ⊢ S1 <: T1 -> exists S2, E ⊢ S2 <: T2 /\ E' ⊢ S1 • e ⇒⇒ S2); intros.

  (* - dependent induction H2; auto.
    + eapply dchk_top_abs with (L:=L `union` dom E0). intros.
      inst_cofinites_with x.
      apply H0; auto.
      econstructor; auto.
    + apply dchk_union1.
      * apply IHdsub; auto.
      * eapply desub_wf_typ; eauto.
    + apply dchk_union2.
      * apply IHdsub; auto.
      * eapply desub_wf_typ; eauto.
  - dependent induction H2. 
    + eapply dchk_top_abs with (L:=L `union` dom E0). intros.
      inst_cofinites_with x.
      dependent destruction H2.
      apply H0; auto.
      econstructor; auto.
      constructor.
      admit. (* easy: weakening *)
    + eapply dchk_abs with (L:=L).
      * admit.
      * intros. inst_cofinites_with x.  
        apply H0. econstructor; eauto.
        admit.
    + apply dchk_intersection; eauto.
    + apply dchk_union1; eauto. 
    + apply dchk_union2; eauto. *)
  - specialize (H0 _ H2).
    destruct H0 as [S1 [Hsub Hinf]].
    specialize (H1 _ _ H2 Hsub).
    destruct H1 as [S2 [Hsub2 Hinfapp]].
    eapply dchk_sub with (S:=S2).
    eapply dinf_app with (T2:=S1); auto.
    admit. (* easy *)
  - dependent destruction H2. 
    +
  
   admit.
  - specialize (H0 _ H1).
    destruct H0 as [S1 [Hsub Hinf]].
    eapply dchk_sub; eauto. 
    admit. (* easy : transitivity *)
  - assert (E0 ⊢ T <: T0 \/ E0 ⊢ S0 <: T0) by admit.
    inversion H4.
    + apply H1; eauto.
    + apply H0; eauto.
  - assert (E0 ⊢ T <: T0 /\ E0 ⊢ S0 <: T0) by admit.
    destruct H3.
    apply H0; auto.
  - assert (E0 ⊢ T <: T0 /\ E0 ⊢ S0 <: T0) by admit.
    destruct H3.
    apply H0; auto.
  
  (* P0 *)
  - admit. (* easy *)
  - exists T. split.
    + eapply dsub_refl. auto.
    + econstructor. 
      admit. (* easy *)
      apply H0; auto. 
      apply dsub_refl; auto.
  - exists dtyp_unit.
    split; auto.
    constructor. auto.
    admit. (* easy *)
  - specialize (H0 _ H1).
    destruct H0 as [S1 [Hsub Hinf]].
    exists S1. split; auto.
    admit.
  - specialize (H0 _ H2).
    destruct H0 as [S1 [Hsub Hinf]].
    specialize (H1 _ _ H2 Hsub).
    destruct H1 as [S2 [Hsub1 Hinfapp]].
    exists S2. split; auto.
    econstructor; eauto.

  - exists (dtyp_all T2). split.
    admit.
    econstructor. intros. eapply H0. eauto.
    admit.
    admit.
  - specialize (H0 _ H1).
    destruct H0 as [S1 [Hsub Hinf]].
    dependent induction Hsub; admit.
  (* P1 *)
  - dependent induction H2.
    + exists dtyp_bot.
      dependent destruction H2.
      split; auto.
    + admit.
    + admit.
    + admit.
    + admit.
    + admit.
  - dependent induction H2.
    + exists dtyp_bot.
      
      admit.
  admit.
  - admit.
Admitted.
    
  