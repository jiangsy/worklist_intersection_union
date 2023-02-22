Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import decl.notations.
Require Import decl.prop_ln_extra.
Require Import decl.prop_basic.
Require Import decl.prop_subtyping.
Require Import ln_utils.


Definition wf_dom : forall {E}, ⊢ E -> atoms.
Proof.
  intros.
  set (x := dom E). exact x.
Defined.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : denv => dom x) in
  let D1 := gather_atoms_with (fun x => ftv_in_dtyp x) in
  let D2 := gather_atoms_with (fun x => fstv_in_dtyp x) in
  (* let D3 := gather_atoms_with (fun x => fv_typ_in_binding x) in *)
  (* let D4 := gather_atoms_with (fun x => fv_exp_in_exp x) in *)
  constr:(A \u B \u C \u D1 \u D2).

(* Ltac apply_fresh_base_fixed H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  let x := fresh atom_name in
  pick fresh x excluding L and apply H. *) 

(* 

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weakening" :=
  apply_fresh_base_fixed H gather_for_weakening x. *)


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
  


Lemma dwf_typ_strengthening : forall F E x T b,
    E ++ x ~ b ++ F ⊢ T ->
    x \notin ftv_in_dtyp T ->
    x \notin fstv_in_dtyp T -> 
    E ++ F ⊢ T.
Proof.
  intros.
  dependent induction H; auto.
  - induction E.
    + inversion H. dependent destruction H2.
      simpl in H0. apply notin_singleton_1 in H0. contradiction.
      auto.
    + destruct a. inversion H.
      * dependent destruction H2. auto.
      * simpl. apply dwf_typ_weakening_cons; auto.
  - induction E.
    + inversion H. dependent destruction H2.
      * simpl in H1. apply notin_singleton_1 in H1. contradiction.
      * auto.
    + destruct a. inversion H.
      * dependent destruction H2. auto.
      * simpl. apply dwf_typ_weakening_cons; auto.
  - simpl in *. constructor.
    + apply notin_union_1 in H1.
      eauto.
    + apply notin_union_2 in H1.
      eauto.
  - simpl in *.
    apply dwftyp_all with (L:=L `union` singleton x); intros; inst_cofinites_with X.
    + auto. 
    + replace (X ~ dbind_tvar_empty ++ E ++ F) with ((X ~ dbind_tvar_empty ++ E)++ F) by auto. eapply H1 with (x:=x) (b:=b); auto.
    rewrite ftv_in_dtyp_open_dtyp_wrt_dtyp_upper; auto.
    rewrite fstv_in_dtyp_open_dtyp_wrt_dtyp_upper; auto. 
  - simpl in *. eauto.
  - simpl in *. eauto.
Qed.



(* Lemma wft_all_inversion : forall E S T,
  dmono_typ T ->
  E ⊢ T ->
  E ⊢ T2  *)

(* Lemma dwf_typ_open_inv : forall E T S1 S2 n,
  E ⊢ S1 ->
  E ⊢ S2 ->
  E ⊢ open_dtyp_wrt_dtyp_rec n S2 T ->
  E ⊢ open_dtyp_wrt_dtyp_rec n S1 T.
Proof.
  intros. 
  dependent induction H1; auto.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + econstructor.
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
    + inversion x. subst. auto.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
    + inversion x. subst. auto.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
    + inversion x. econstructor; eauto.
  - destruct T; simpl in *; try solve [inversion x].
    + destruct (lt_eq_lt_dec n0 n).
      * destruct s; auto. inversion x.
      * inversion x.
    + inversion x.
      eapply dwftyp_all with (L:=L); intros; inst_cofinites_with X.
      * admit.
      * replace (open_dtyp_wrt_dtyp_rec (S n) S1 T ^ᵈ X) with (open_dtyp_wrt_dtyp_rec (S n) S1 (T ^ᵈ X)).

        apply H1 with (S2:=S2); eauto.
        admit.
        admit.
Admitted. *)

Theorem dwf_typ_subst : forall E1 E2 X T1 T2, 
  E1 ++ (X ~ dbind_tvar_empty) ++ E2 ⊢ T1 ->
  E2 ⊢ T2 -> 
  E1 ++ E2 ⊢ {T2 /ᵈ X} T1.
Proof.
  intros; dependent induction H; try solve [simpl; auto].
  - simpl. destruct (X0 == X).
    + replace (E1 ++ E2) with (nil ++ E1 ++ E2) by auto. 
    apply dwf_typ_weakening; auto.
    + econstructor. 
      induction E1.
      * simpl in *. inversion H; auto.
        inversion H1. subst. contradiction. 
      * destruct a; inversion H.
        -- dependent destruction H1. auto.
        -- simpl. auto.
  - simpl. constructor.
    induction E1.
    + simpl in *. inversion H; auto.
      inversion H1.
    + destruct a; inversion H.
      * dependent destruction H1. auto.
      * simpl. auto.
  - simpl. eapply dwftyp_all with (L:=L `union` singleton X).
    + intros. inst_cofinites_with X0. 
      admit.
    + intros. inst_cofinites_with X0. 
      rewrite dtyp_subst_open_comm; eauto.
      * replace (X0 ~ dbind_tvar_empty ++ E1 ++ E2) with ((X0 ~ dbind_tvar_empty ++ E1) ++ E2) by auto. eapply H1; auto.
Admitted.

(* Theorem dwf_typ_subst_inversion : forall E X T1, 
  E ⊢ T1 ->
  forall T2 T3, T1 = {T2 /ᵈ X} T3 ->
    E ⊢ T3.
Proof.
  intros. dependent induction H; auto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  -

  + admit.
  + simpl in *. 
    dependent destruction H; eauto.
  + simpl in *.
    apply IHT1.
    dependent destruction H.
    apply dwftyp_all with (L:=L); intros.
    * admit.
    * inst_cofinites_with X0.
      apply IHT1.
    appl *)

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

(* Theorem dwf_type_subst_var: forall G1 G2 x x' A,
  G1, x,, G2 ⊢ A ->  ⊢ G1, x',, G2 -> G1, x',, G2 ⊢ [`ᵈ x' /ᵈ x] A.
Proof.Theorem ld_wf_type_subst_var: forall G1 G2 x x' A,
G1, x,, G2 ⊢ A ->  ⊢ G1, x',, G2 -> G1, x',, G2 ⊢ [`ᵈ x' /ᵈ x] A.
Proof. *)


Lemma mono_type_order : forall T,
  dmono_typ T -> dtyp_order T = 0.
Proof.
  intros. induction H; simpl; auto; lia.
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


Inductive d_subenv : denv -> denv -> Prop := 
| d_subenv_empty: d_subenv nil nil  
| d_subenv_tvar : forall E1 E2 X, 
    d_subenv E1 E2 -> 
    d_subenv (X ~ dbind_tvar_empty  ++  E1) 
        (X ~ dbind_tvar_empty  ++  E2)
| d_subenv_stvar : forall E1 E2 SX, 
    d_subenv E1 E2 -> 
    d_subenv (SX ~ dbind_stvar_empty  ++  E1) 
        (SX ~ dbind_stvar_empty  ++  E2)
| d_subenv_var : forall E1 E2 x S T,
    d_subenv E1 E2 ->
    dsub E2 S T ->
    d_subenv (x ~ dbind_typ S ++ E1) 
        (x ~ dbind_typ T ++ E2)        
.


(* Theorem progress.  *)

Lemma d_subenv_same_dom : forall E E', 
  d_subenv E' E ->
  dom E = dom E'.
Proof.
  intros. induction H; simpl; auto; rewrite IHd_subenv; auto.
Qed.

Lemma d_subenv_same_tvar : forall E E' X, 
  d_subenv E' E ->
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

Lemma d_subenv_same_stvar : forall E E' SX, 
  d_subenv E' E ->
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


Lemma d_subenv_wf_typ : forall E T, 
  E ⊢ T -> 
  forall E', 
    d_subenv E' E ->
    E' ⊢ T.
Proof.
  intros E T H. induction H; intros; auto.
  - econstructor. 
    eapply d_subenv_same_tvar; eauto.
  - econstructor.
    eapply d_subenv_same_stvar; eauto.
  - eapply dwftyp_all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed.


Lemma d_subenv_wf_env : forall E, 
  ⊢ E -> 
  forall E', 
    d_subenv E' E ->
    ⊢ E'.
Proof.
  intros E H. induction H; intros.
  - inversion H. auto.
  - dependent destruction H1.
    econstructor; auto. 
    erewrite <- d_subenv_same_dom; auto.
  - dependent destruction H1.
    econstructor; auto. 
    erewrite <- d_subenv_same_dom; auto.
  - dependent destruction H2.
    econstructor; auto.
    + apply dsub_dwft in H3; destruct H3.
      eapply d_subenv_wf_typ; eauto.
    + erewrite <- d_subenv_same_dom; auto.
Qed.

Hint Resolve d_subenv_wf_typ : typing.
Hint Resolve d_subenv_wf_env : typing.
Hint Resolve d_wft_typ_subst : typing.
Hint Resolve d_wf_env_subst_tvar_typ : typing.
Hint Resolve bind_typ_subst : typing. 
Hint Resolve dwf_typ_dlc_type : typing.


Theorem chkinffinapp_subst: forall E F X e m T1 T2,
  dtyping (F ++ X ~ dbind_tvar_empty ++ E) e m T1 ->
  E ⊢ T2 ->
  dmono_typ T2 ->
  dtyping (map (dsubst_tv_in_binding T2 X) F  ++ E) (dsubst_tv_in_dexp T2 X e) (dsubst_tv_in_dtypingmode T2 X m) ({T2 /ᵈ X} T1).
Proof with auto with typing.
  intros.
  generalize dependent T2.
  dependent induction H; intros; try solve [simpl in *; eauto 5 with typing].
  - simpl in *. eapply dtyping_inftabs with (L:=L `union` singleton X).
    + replace (dtyp_all ({T2 /ᵈ X} T)) with ({T2 /ᵈ X}  dtyp_all T) by auto.
      auto... 
    + intros. specialize (notin_union_1 _ _ _ H4). intros.
      specialize (H1 _ H5 E (X0 ~ dbind_tvar_empty ++ F) X (JMeq_refl _) T2 H2 H3).
      assert (lc_dtyp T2) by eauto...
      specialize (dsubst_tv_in_dexp_open_dexp_wrt_dtyp e T2 (dtyp_var_f X0) X H6).
      intros. simpl in H7. unfold eq_dec in H7.
      destruct (EqDec_eq_of_X X0 X) in H7.
      * subst. apply notin_union_2 in H4. apply notin_singleton_1 in H4.
        contradiction.
      * rewrite <- H7. rewrite dtyp_subst_open_comm; auto.
  - simpl in *. rewrite dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
  - simpl in *. apply dtyping_chkabstop with (L:=L).
    intros x Hfr. inst_cofinites_with x.
    replace (dexp_var_f x) with (dsubst_tv_in_dexp T2 X (dexp_var_f x)) by auto.
    rewrite <-  dsubst_tv_in_dexp_open_dexp_wrt_dexp. 
    replace (x ~ dbind_typ dtyp_bot ++ map (dsubst_tv_in_binding T2 X) F ++ E) with 
    ((map (dsubst_tv_in_binding T2 X) (x ~ dbind_typ dtyp_bot ++ F)) ++ E) by auto. 
    auto...
  - simpl in *. eapply dtyping_chkabs with (L:=L); eauto...
    intros X1 Hfr.
    inst_cofinites_with X1.
    specialize (H1 E ((X1, dbind_typ T1) :: F ) X (JMeq_refl _) T0 H2 H3).
    replace (dexp_var_f X1) with (dsubst_tv_in_dexp T0 X (dexp_var_f X1)) by (simpl; auto).
    rewrite <- dsubst_tv_in_dexp_open_dexp_wrt_dexp; eauto...
  - simpl in *. eapply dtyping_chkall with (L:=L `union` singleton X); eauto...
    + replace (dtyp_all ({T2 /ᵈ X} T)) with ({T2 /ᵈ X} dtyp_all T) by auto. 
      auto...
    + intros. inst_cofinites_with X0.
      rewrite dtyp_subst_open_comm; eauto...
      replace (X0 ~ dbind_tvar_empty ++ map (dsubst_tv_in_binding T2 X) F ++ E) with 
      (map (dsubst_tv_in_binding T2 X) (X0 ~ dbind_tvar_empty ++ F) ++ E) by auto.
      auto.
  - simpl in *. 
    apply dtyping_chksub with (S:=({T2 /ᵈ X} S)); eauto.
    eapply d_sub_subst_mono; eauto.
  - simpl in *. eapply dtyping_infappall with (T3:={T0 /ᵈ X} T3); eauto...
    + apply d_mono_typ_subst_mono_mono; auto.
    + replace (dtyp_all ({T0 /ᵈ X} T1)) with ({T0 /ᵈ X} dtyp_all T1) by auto.
      auto...
    + rewrite <- dsubst_tv_in_dtyp_open_dtyp_wrt_dtyp; eauto...
Qed.


Fixpoint dexp_size (e : dexp) : nat :=
  0.

Fixpoint dtyp_size (T : dtyp) : nat :=
  0.

Definition dmode_size (mode : dtyping_mode) : nat := 
  match mode with 
  | dtypingmode_inf => 2
  | dtypingmode_chk => 1
  | dtypingmode_infapp _ => 0
  end.

Definition dmode_type_size (mode : dtyping_mode) : nat := 
  match mode with 
  | dtypingmode_inf => 0
  | dtypingmode_chk => 0
  | dtypingmode_infapp T =>  dtyp_size T
  end.


Theorem dchk_dinf_dinfapp_subsumption : forall n1 n2 n3 E E' e T mode,
  dexp_size e < n1 ->
  dmode_size mode < n2 -> 
  dtyp_size T + dmode_type_size mode < n3 ->
  dtyping E e mode T ->
  d_subenv E' E ->
    match mode with 
    | dtypingmode_chk => forall S, E ⊢ T <: S -> dtyping E' e dtypingmode_chk S
    | dtypingmode_inf => exists S, E ⊢ S <: T /\ dtyping E' e dtypingmode_inf S
    | dtypingmode_infapp T1 => forall S1, E ⊢ S1 <: T1 -> exists S2, E ⊢ S2 <: T /\ dtyping E' e (dtypingmode_infapp S1) S2
    end.
Proof.
  intro n1; induction n1; intro n2; induction n2; intro n3; induction n3. intros.
  - admit.
  - admit.
  - admit.
Admitted.

(* Theorem dchk_subsumption : forall e n,
  dexp_size e < n -> 
  forall E S,
    E ⊢ e ⇐ S ->
    forall  E' T, 
      d_subenv E' E ->
      E ⊢ S <: T ->
      E' ⊢ e ⇐ T
with 
dinf_subsumption : forall e n,
  dexp_size e < n ->
  forall E T, 
    E ⊢ e ⇒ T ->
    forall E',
      d_subenv E' E ->
      exists S, 
        dsub E S T /\ E' ⊢ e ⇒ S
with 
dinfapp_subsumption : forall e n, 
  dexp_size e < n ->
    forall E T1 T2,  
    E ⊢ T1 • e ⇒⇒ T2 ->
    (exists T, E ⊢ e ⇐ T) /\
    forall E' S1, 
      d_subenv E' E -> 
      E ⊢ S1 <: T1 -> 
      exists S2, 
        E ⊢ S2 <: T2 /\ E' ⊢ S1 • e ⇒⇒ S2.
Proof.
  - intros e n.
    induction n.

Theorem dchk_subsumption : forall E e S,
  E ⊢ e ⇐ S ->
  forall  E' T, 
    d_subenv E' E ->
    E ⊢ S <: T ->
    E' ⊢ e ⇐ T
with 
dinf_subsumption : forall E e T, 
  E ⊢ e ⇒ T ->
  forall E',
    d_subenv E' E ->
    exists S, 
      dsub E S T /\ E' ⊢ e ⇒ S
with 
dinfapp_subsumption : forall E T1 e T2,
  E ⊢ T1 • e ⇒⇒ T2 ->
  (exists T, E ⊢ e ⇐ T) /\
  forall E' S1, 
    d_subenv E' E -> 
    E ⊢ S1 <: T1 -> 
    exists S2, 
      E ⊢ S2 <: T2 /\ E' ⊢ S1 • e ⇒⇒ S2.
Proof.
  - intros E e S H.
    induction H; auto; intros.
    + dependent induction H2; eauto.
    + dependent induction H3. 
      * apply dchk_top_abs with (L:=L `union` dom E). intros.
      inst_cofinites_with x.
      dependent destruction H3.
      apply H1; auto.
      econstructor; auto.
      constructor.
      admit. (* easy: weakening *)
      * eapply dchk_abs with (L:=L).
        -- eauto.  apply dsub_dwft in H3_.
           apply dsub_dwft in H3_0.
           destruct H3_. destruct H3_0.
           eauto.
        -- intros. inst_cofinites_with x.  
          apply H1. econstructor; eauto.
          admit. (* easy: weakening *)
      * apply dchk_intersection; eauto.
      * apply dchk_union1; eauto. 
      * apply dchk_union2; eauto.
    + specialize (dinf_subsumption _ _ _ H _ H1).
      destruct dinf_subsumption as [S1 [Hsub Hinf]].
      specialize (dinfapp_subsumption _ _ _ _ H0 ).
      destruct dinfapp_subsumption as [Hchk Hinfapp_subsumption].
      specialize (Hinfapp_subsumption _ _ H1 Hsub).
      destruct Hinfapp_subsumption as [S2 [Hsub2 Hinfapp]].
      eapply dchk_sub with (S:=S2).
      eapply dinf_app with (T2:=S1); auto.
      admit. (* easy : transitivity *)
    (* e <= ∀ X. T *)
    + admit.
    (* e <= T *)
    + specialize (dinf_subsumption _ _ _ H _ H1).
      destruct dinf_subsumption as [S1 [Hsub Hinf]].
      eapply dchk_sub; eauto. 
      admit. (* easy : transitivity *)
    (* e <= S * T *)
    + dependent induction H2.
      * dependent destruction H2. eapply dchk_subsumption; eauto.
      * eapply dchk_intersection.
        -- eapply IHdsub1 with (S:=S) (T:=T); eauto.
        -- eapply IHdsub2 with (S:=S) (T:=T); eauto.
      * eapply IHdchk1; eauto.
      * eapply IHdchk2; eauto.
      * eapply dchk_union1. eapply IHdsub with (S:=S) (T:=T); eauto.
        eauto.
      * eapply dchk_union2. eapply IHdsub with (S:=S) (T:=T); eauto.
        eauto.
    (* e <= S + T *)
    + apply dsub_union_inversion in H2. destruct H2.
      auto.
    (* e <= S + T *)
    + apply dsub_union_inversion in H2. destruct H2.
      auto.

  - intros. induction H.
    + admit. (* easy *)
    + exists T. split; auto.
      * apply dsub_refl; auto.
      * apply dinf_anno.
        eapply d_subenv_wf_typ; eauto.
        eapply dchk_subsumption; eauto.
        apply dsub_refl; auto.
    + eauto.
      (* exists dtyp_unit.
      split; eauto.  *)
    + eauto. 
      (* + specialize (dinfapp_subsumption _ _ _ _ H1).
      destruct dinfapp_subsumption as [Hchk Hinfapp_subsumption].
      specialize (IHdinf H0).
      destruct IHdinf as [S1 [Hsub Hinf]].
      specialize (Hinfapp_subsumption _ _ H0 Hsub).
      destruct Hinfapp_subsumption as [S2 [Hsub1 Hinfapp]].
      exists S2. split; eauto. *)
    (* e => ∀ X. T *)
    + admit.
    + specialize (IHdinf H0).
      destruct IHdinf as [S1 [Hsub Hinf]].
      dependent induction Hsub; eauto.
    + admit.
    
  - intros; induction H.
    + split. exists T1. auto. 
      intros. dependent induction H2; auto.
      * dependent destruction H2. exists dtyp_bot; split;     eauto. 
      * exists S2; split; eauto.
        constructor; eauto. admit.
      * admit.
      * specialize (IHdsub _ _ H H0 H1 (eq_refl _)).
        destruct IHdsub as [S3 [Hsub Hinfapp]].
        exists S3; split; auto. 
        admit. (* TODO : check rule *)
      * specialize (IHdsub _ _ H H0 H1 (eq_refl _)).
        destruct IHdsub as [S3 [Hsub Hinfapp]].
        exists S3; split; auto. 
        admit. (* TODO : check rule *)
      * admit. (* TODO : check rule *)
    + destruct IHdinfapp as [Hchk Hinfapp].
      destruct Hchk as [T]. split.
      exists T; auto. 
      intros. dependent induction H5.
      * exists dtyp_bot; split.
        -- constructor. admit.
        -- econstructor. eapply dchk_subsumption; eauto.
            econstructor. admit. 
      * admit.
      * admit.
      * admit.
      * admit.
      * admit.

    + split.
      exists dtyp_top; auto. 
      intros. dependent induction H1.
      * exists dtyp_bot. split; eauto.
      * specialize (IHdsub H H0 (eq_refl _)).
        destruct IHdsub as [S2 [Hsub Hinfapp]].
        exists S2; split; eauto.
        econstructor; eauto. admit.
      * admit. (* TODO : check rule *)
      * admit. (* TODO : check rule *)  
      * admit. (* TODO : check rule *)  
Admitted.
 *)