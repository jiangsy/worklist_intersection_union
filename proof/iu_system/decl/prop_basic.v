Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import decl.notations.
Require Import decl.prop_ln_extra.
Require Import ln_utils.


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



Lemma d_wf_typ_subst_tvar_stvar : forall E F X T,
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


Lemma d_wf_typ_subst_stvar_tvar : forall E F SX T,
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

Corollary d_wf_typ_subst_stvar_tvar_cons : forall E X T,
  X `notin` ftv_in_dtyp T ->
  X ~ dbind_tvar_empty ++ E ⊢ₛ T ^ᵈ X ->
  X ~ dbind_stvar_empty ++ E ⊢ₛ T ^^ᵈ dtyp_svar X.
Proof.
  intros.
  replace (X ~ dbind_tvar_empty ++ E) with (nil ++ X ~ dbind_tvar_empty ++ E) in H0 by auto.
  specialize (d_wf_typ_subst_tvar_stvar _ _ _ _ H0).
  intros.
  rewrite dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp in H1.
  simpl in H1.
  unfold eq_dec in H1. destruct (EqDec_eq_of_X X X).
  - rewrite dsubst_tv_in_dtyp_fresh_eq in H1; auto.
  - contradiction.
  - auto.
Qed.

Corollary d_wf_typ_subst_tvar_stvar_cons : forall E SX T,
  SX `notin` fstv_in_dtyp T ->
  SX ~ dbind_stvar_empty ++ E ⊢ T ^^ᵈ dtyp_svar SX ->
  SX ~ dbind_tvar_empty ++ E ⊢ T ^ᵈ SX.
Proof.
  intros.
  replace (SX ~ dbind_stvar_empty ++ E) with (nil ++ SX ~ dbind_stvar_empty ++ E) in H0 by auto.
  specialize (d_wf_typ_subst_stvar_tvar _ _ _ _ H0). intros. 
  rewrite dsubst_stv_in_dtyp_open_dtyp_wrt_dtyp in H1; auto. simpl in H1. unfold eq_dec in H1. destruct (EqDec_eq_of_X SX SX).
  - rewrite dsubst_stv_in_dtyp_fresh_eq in H1; auto.
  - contradiction.
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
    + apply d_wf_typ_subst_stvar_tvar_cons; auto.  
Qed.

Lemma dwf_typ_s_dwf_typ : forall E T, 
  E ⊢ₛ T -> E ⊢ T.
Proof.
  intros. induction H; auto.
  - eapply dwftyp_all with (L:= (L `union` fstv_in_dtyp T)); 
    intros; inst_cofinites_with X.  
    + eapply fstv_open_tvar; auto. 
    + eapply d_wf_typ_subst_tvar_stvar_cons; auto.
Qed.

Hint Constructors dsub : core.
Hint Resolve dwf_typ_dwf_typ_s : core.
Hint Resolve dwf_typ_s_dwf_typ : core.

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

Hint Constructors dneq_union : Core.
Hint Constructors dneq_intersection : Core.


Lemma dwf_typ_open_inv : forall E T S X,
  lc_dtyp S ->
  E ⊢ {S /ᵈ X} T ->
  binds X dbind_tvar_empty E ->
  E ⊢ T.
Proof.
  intros. dependent induction H0; auto.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
    - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (X0 == X).
      * subst. auto.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (X1 == X) in x; subst.
      auto.
      inversion x. subst. auto.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (X0 == X) in x; subst.
      auto.
      inversion x. 
    + inversion x. subst. auto.
  - destruct T; simpl in *; try solve [inversion x].
      destruct (X0 == X) in x.
      subst. auto. inversion x.
    + inversion x. eauto.
  - destruct T; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    + subst. auto.
    + inversion x.
    + inversion x.
      eapply dwftyp_all with (L:=L `union` singleton X `union` ftv_in_dtyp S); intros; 
      inst_cofinites_with X0.
      * rewrite H5 in H2.
        rewrite dtyp_subst_open_comm in H2; auto.
        eapply ftv_sin_dtyp_subst; eauto.
      * eapply H1 with (X:=X) (S:=S); auto.
        -- rewrite H5. rewrite dtyp_subst_open_comm; auto.
  - destruct T; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
  - destruct T; simpl in *; try solve [inversion x].
    destruct (X0 == X) in x.
    subst. auto. inversion x.
    + inversion x. eauto.
Qed.


Hint Constructors dwf_typ: core.
Hint Constructors dwf_env: core.
Hint Constructors dwf_typ_s: core.



Lemma dwf_typ_weakening : forall E1 E2 E3 T, 
  E1 ++ E3 ⊢ T ->
  E1 ++ E2 ++ E3 ⊢ T.
Proof.
  intros.
  dependent induction H; auto.
  - eapply dwftyp_all with (L:=L `union` dom (E1 ++ E2 ++ E3));
    intros; inst_cofinites_with X.
    + auto.
    + replace (X ~ dbind_tvar_empty ++ E1 ++ E2 ++ E3) with ((X ~ dbind_tvar_empty ++ E1) ++ E2 ++ E3) by auto.
    eapply H1; eauto.
Qed.

Corollary dwf_typ_weakening_cons : forall E X b T,
  E ⊢ T ->
  ((X ~ b) ++ E) ⊢ T.
Proof.
  intros.
  replace (X ~ b ++ E) with (nil ++ X ~ b ++ E) by auto.
  now apply dwf_typ_weakening.
Qed.

Lemma dwf_env_binds_dwf_typ : forall E x T,
  ⊢ E ->
  binds x (dbind_typ T) E ->
  E ⊢ T.
Admitted.

Lemma dwft_subst : forall E X T1 T2,
  X ~ dbind_tvar_empty ++ E ⊢ T1 ^ᵈ X ->
  E ⊢ T2 ->
  E ⊢ T1 ^^ᵈ T2.
Admitted.

Hint Constructors dtyping : core.

Lemma d_wft_typ_subst : forall E X F T1 T2,
  F ++ X ~ dbind_tvar_empty ++ E ⊢ T1 ->
  E ⊢ T2 ->
  map (dsubst_tv_in_binding T2 X) F  ++ E ⊢ {T2 /ᵈ X} T1.
Proof.
Admitted.

Lemma d_wf_env_subst_tvar_typ : forall E X F T1,
  ⊢ F ++ X ~ dbind_tvar_empty ++ E ->
  E ⊢ T1 ->
  ⊢ (map (dsubst_tv_in_binding T1 X) F ++ E).
Proof.
Admitted.

Lemma d_new_tv_notin_wf_typ : forall X E T1,
  ⊢ (X, dbind_tvar_empty) :: E ->
  E ⊢ T1 ->
  X `notin` ftv_in_dtyp T1.
Proof.
  intros; induction H0; auto.
  - simpl. destruct (X0 == X).
    + subst. dependent destruction H.
      simpl in *. exfalso.
      eapply binds_dom_contradiction; eauto.
    + apply notin_singleton; auto.
  - simpl. inst_cofinites_by L.
    admit.
Admitted.
    

Lemma dwf_typ_lc_dtyp : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
  intros. induction H; eauto.
Qed.

Lemma wft_all_open_wfdtyp_wft : forall E X T1 T2,
  E ⊢ T1 ->
  E ⊢ T2 ->
  E ⊢ {T2 /ᵈ X} T1.
Proof.
  intros E X T1 T2 Hwft1.
  generalize dependent T2.
  dependent induction Hwft1; intros; try solve [simpl; eauto].
  - simpl. destruct (X0 == X); auto.
  - simpl. apply dwftyp_all with (L:=L `union` singleton X); intros.
    inst_cofinites_with X0.
    + rewrite dtyp_subst_open_comm; eauto.
      apply ftv_sin_dtyp_subst_inv; auto.
      eapply dwf_typ_lc_dtyp; eauto.
    + rewrite dtyp_subst_open_comm; eauto.
      eapply H1; auto.
      apply dwf_typ_weakening_cons; eauto.
Qed.

Lemma bind_typ_subst : forall F X E x T1 T2,
  ⊢ F ++ (X, dbind_tvar_empty) :: E ->
  binds x (dbind_typ T1) (F ++ (X, dbind_tvar_empty) :: E) ->
  E ⊢ T2 ->
  binds x (dbind_typ ({T2 /ᵈ X} T1)) (map (dsubst_tv_in_binding T2 X) F ++ E).
Proof.
  intros. induction F; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (E ⊢ T1) by admit.
      rewrite dsubst_tv_in_dtyp_fresh_eq; auto.
      eapply d_new_tv_notin_wf_typ; eauto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      admit.
Admitted.


Lemma d_mono_typ_subst_mono_mono : forall T1 T2 X,
  dmono_typ T1 ->
  dmono_typ T2 ->
  dmono_typ ({T2 /ᵈ X} T1).
Proof.
  intros. induction T1; try solve [simpl; eauto].
  - simpl. destruct (X0 == X); auto.
  - simpl. dependent destruction H. auto. 
  - inversion H.
  - simpl. dependent destruction H. auto.
  - simpl. dependent destruction H. auto.
Qed.


Lemma dsub_dwft : forall E T1 T2,
  E ⊢ T1 <: T2 -> E ⊢ T1 /\ E ⊢ T2.
Proof.
  intros.
  induction H; try solve [intuition].
  - split; eapply dwftyp_all with (L:=L `union` fstv_in_dtyp S `union` fstv_in_dtyp T); intros; inst_cofinites_with X.
    + eapply fstv_open_tvar; auto.
    + apply d_wf_typ_subst_tvar_stvar_cons; intuition.
    + eapply fstv_open_tvar; auto.
    + apply d_wf_typ_subst_tvar_stvar_cons; intuition.
  - split; try solve [intuition].
    + eapply dwftyp_all with (L:=L `union` ftv_in_dtyp S). 
      * intros. inst_cofinites_with X. auto.
      * intros. inst_cofinites_with X.
        destruct IHdsub. 
        eapply dwf_typ_open_inv with (X:=X) (S:=T2); auto.
        eapply dwf_typ_dlc_type; eauto.
        -- replace (X ~ dbind_tvar_empty ++ E) with (nil ++ X ~ dbind_tvar_empty ++ E) by auto. apply dwf_typ_weakening. simpl. rewrite  dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp.
          ++ simpl. unfold eq_dec. destruct ( EqDec_eq_of_X X X ).
            ** rewrite dsubst_tv_in_dtyp_fresh_eq; auto.
            ** contradiction.
          ++ eapply dwf_typ_dlc_type; eauto.
Qed.