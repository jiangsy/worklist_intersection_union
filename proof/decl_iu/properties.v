Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import decl_iu.notations.
Require Import ln_utils.

Definition wf_dom : forall {Γ}, ⊢ Γ -> atoms.
Proof.
  intros.
  set (x := ld_ctx_dom Γ). exact x.
Defined.

Ltac gather_for_weakening :=
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
  apply_fresh_base_fixed H gather_for_weakening x.

Lemma subst_same_eq : forall A x,
  A = [`x /_ x] A.
Proof.
  intros.
  induction A; auto.
  - simpl. rewrite <- IHA. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. destruct (x0==x); subst; auto. 
Qed.


Lemma open_subst_eq : forall A x t, 
  x `notin` fv_ld_type A -> lc_ld_type t  ->
    A ^^ t = [t /_ x] A ^^ `x.
Proof.
  intros.  
  rewrite subst_ld_type_open_ld_type_wrt_ld_type. simpl.
  rewrite eq_dec_refl.
  rewrite subst_ld_type_fresh_eq.
  all : auto.
Qed. 


Lemma ld_wf_mtype_is_mtype : forall G t,
  ld_wf_mtype G t -> ld_mono_type t.
Proof.
  intros.
  induction H; auto.
Qed.

Theorem ld_sub_wf_ctx : forall G t1 t2, 
  G ⊢ t1 <: t2 -> ⊢ G.
Proof.
  intros.
  induction H; auto.
  - inst_cofinites_with_new.
    dependent destruction H0; auto.
Qed.


Lemma ld_sub_refl :
  forall G A, ld_wf_type G A -> ld_sub G A A.
Proof.
  intros.
  induction H.
  - constructor. auto.
  - constructor; auto.
  - constructor; auto.
  - eapply ld_sub_intersection_r.
    eapply ld_sub_intersection_l1; eauto. 
    eapply ld_sub_intersection_l2; eauto.
  - eapply ld_sub_union_l.
    eapply ld_sub_union_r1; eauto.
    eapply ld_sub_union_r2; eauto.
  - eapply ld_sub_forallr with (L:=L `union` (ld_ctx_dom G)). intros. 
    inst_cofinites_with x. eapply ld_sub_foralll with (t := `x); auto.
    constructor.
    + eapply ld_sub_wf_ctx; eauto.
    + simpl. auto. 
Qed.


Lemma ld_in_context_exact : 
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
  G1 ,, G3 ⊢ t -> ⊢ G1 ,, G2 ,, G3 -> 
  G1 ,, G2 ,, G3 ⊢ t.
Proof.
  intros.
  dependent induction H; auto.
  - constructor. auto. eapply ld_in_context_weakenning. auto.
  - eapply ld_wft_forall with (L:=L `union` ld_ctx_dom (G1,, G2,, G3)). intros.
    inst_cofinites_with x. replace (G1,, G2,, G3, x ) with (G1,, G2,, (G3, x)) by auto. apply H0; auto.
    simpl. econstructor; eauto.
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
  G1, x,, G2 ⊢ A ->  ⊢ G1, x',, G2 -> G1, x',, G2 ⊢ [` x' /_ x] A.
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
    replace (([`x' /_ x] t) ^` x0) with ([`x' /_ x] t ^` x0).
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
      | _ : _ |-  context [ ([?e /_ ?x] ?A) ^^ ` ?x' ] => 
        replace (` x') with ([e /_ x] `x') by (apply subst_ld_type_fresh_eq; auto)
    end; repeat rewrite <- subst_ld_type_open_ld_type_wrt_ld_type by auto.



Theorem ld_wf_mtype_subst :
  forall G1 G2 x t t', 
    ld_mono_type t' -> ld_wf_mtype (G1, x,, G2) t -> G1 ⊢ t' ->  ld_wf_mtype (G1,, G2) ([t' /_ x] t).
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
    ld_mono_type t' -> ld_wf_type (G1, x,, G2) t -> G1 ⊢ t' ->  ld_wf_type (G1,, G2) ([t' /_ x] t).
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
  - replace ([t' /_ x] ld_t_forall t) with (ld_t_forall ([t' /_ x] t)) by auto.
    eapply ld_wft_forall with (L:=L `union` singleton x). intros. 
    replace (([t' /_ x] t) ^` x0) with ([t' /_ x] t ^` x0).
    replace (G1,, G2, x0) with (G1,, (G2, x0)) by auto. eapply H0; eauto.
    + rewrite subst_ld_type_open_ld_type_wrt_ld_type. 
    simpl. apply notin_union_2 in H3.
    apply notin_singleton_1' in H3.  unfold not in H3. 
    destruct (x0 == x).
    * subst. contradiction.
    * auto.
    * now apply ld_mono_is_ld_lc.
Qed.


Theorem ld_union_sub_inv: forall G A1 A2 B,
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
Qed.



Theorem substitution : forall G1 G2 x A B t,
  G1 , x  ,, G2 ⊢ A <: B ->
  G1 ⊢ t -> ld_mono_type t ->
  G1 ,, G2 ⊢ [t /_ x] A <: [t /_ x] B.
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
  - simpl. eapply ld_sub_foralll with (t:=[t /_ x] t0). 
    + apply ld_wf_mtype_subst; auto.
    + replace (([t /_ x] A) ^^ ([t /_ x] t0)) with ([t /_ x] A ^^ t0).
      * apply IHld_sub; auto.
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type; auto. now apply ld_mono_is_ld_lc.
  - simpl. eapply ld_sub_forallr with (L:=L `union` singleton x).
    intros. inst_cofinites_with x0.
    rewrite_subst_open_var.
    replace  (([t /_ x] B) ^^ ([t /_ x] ` x0)) with ( [t /_ x] B ^^ ` x0).
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
  ld_mono_type t -> type_order (A ^^ t) = type_order A.
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


Lemma sized_ld_sub_to_ld_sub : forall G t1 t2 n,
  G ⊢ t1 <: t2 | n -> G ⊢ t1 <: t2.
Proof.
  intros. induction H; eauto.
Qed.


Lemma sized_ld_sub_weakening : forall G1 G2 G3 t1 t2 n,
  G1 ,, G3 ⊢ t1 <: t2 | n -> ⊢ G1 ,, G2 ,, G3 ->
  G1 ,, G2 ,, G3 ⊢ t1 <: t2 | n.
Proof.
  intros.
  dependent induction H; auto.
  - constructor; auto. eapply ld_in_context_weakenning; auto.
  - constructor; auto. 
  - constructor; auto. 
  - eapply sls_intersection_r. eapply IHsized_ld_sub1; auto. eapply IHsized_ld_sub2; auto.
  - eapply sls_intersection_l1. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_intersection_l2. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_union_r1. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_union_r2. eapply IHsized_ld_sub; auto.
    eapply ld_wf_type_weakening; auto.
  - eapply sls_union_l. eapply IHsized_ld_sub1; auto. eapply IHsized_ld_sub2; auto.
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
  G1 , x' ,, G2 ⊢ [`x' /_ x] A <: [`x' /_ x] B | n.
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
  - simpl. eapply sls_foralll with (t:=[`x' /_ x] t). 
    + destruct (x == x'); subst.
      * replace ([` x' /_ x'] t) with t; auto.
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
    + replace (([`x' /_ x] A) ^^ ([`x' /_ x] t)) with ([`x' /_ x] A ^^ t).
      * apply IHsized_ld_sub; auto.
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type; auto. 
  - simpl. eapply sls_forallr with (L:=L `union` singleton x `union` ld_ctx_dom ( G1, x',, G2)).
    intros. inst_cofinites_with x0.
    rewrite_subst_open_var.
    replace  (([`x' /_ x] B) ^^ ([`x' /_ x] ` x0)) with ( [`x' /_ x] B ^^ ` x0).
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
    replace A with ([`x0 /_ x] A).
    replace (B ^^ `x0) with ([`x0 /_ x] B ^^ `x).
    eapply  sized_var_substitution; eauto.
    * simpl. constructor; auto.
      apply ld_sub_wf_ctx in H. dependent destruction H. auto.
    * apply eq_sym. eauto...
    * rewrite subst_ld_type_fresh_eq; auto.
Qed.


Theorem sized_substitution : forall G1 G2 x A B t n,
  G1 , x  ,, G2 ⊢ A <: B | n ->
  G1 ⊢ t -> ld_mono_type t ->
  exists n', G1 ,, G2 ⊢ [t /_ x] A <: [t /_ x] B | n'.
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
             econstructor; eauto...
          -- eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
             econstructor; eauto...
        * simpl. eapply ld_sub_union_r1; auto.
          eapply IHt_ssize with  (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
          econstructor; eauto...
        * simpl. eapply ld_sub_union_r2; auto.
          eapply IHt_ssize with  (B:=ld_t_arrow C0 D) (n1 := S (n1 + n0)); eauto...
          econstructor; eauto...
        * eapply ld_sub_forallr with (L:=L `union` ld_ctx_dom G). 
          intros. inst_cofinites_with x.
          eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1:=S (n1 + n0)); eauto...
          econstructor; eauto... 
      + simpl in H. dependent destruction H2.
        * apply ld_sub_intersection_r. eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
          econstructor; eauto. 
          eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
          econstructor; eauto.
        * eapply IHt_ssize with (B:=B1); eauto...
        * eapply IHt_ssize with (B:=B2); eauto...
        * eapply ld_sub_union_r1; auto. eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
          econstructor; eauto.
        * eapply ld_sub_union_r2; auto. eapply IHt_ssize with (B:=ld_t_intersection B1 B2 ) (n1:=S (n1 + n0)); eauto...
          econstructor; eauto.
        * eapply ld_sub_forallr with (L:=L `union` ld_ctx_dom G).
          intros.
          eapply IHt_ssize with (B:=ld_t_intersection B1 B2) (n1:=S(n1 + n0)) (n2:=n); eauto...
          eapply sls_intersection_r; auto...
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
          eapply sls_forallr; eauto. eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
          eapply sls_forallr; eauto.
        * apply ld_sub_union_r1. eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
          eapply sls_forallr; eauto. auto.
        * apply ld_sub_union_r2. eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n); eauto...
          eapply sls_forallr; eauto. auto.
        * inst_cofinites_by (L `union` fv_ld_type A `union` fv_ld_type B).
          apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H2. destruct H2.
          specialize (sized_substitution G ld_ctx_nil x _ _ _ _ H1 H2 H4).
          intros. destruct H5 as [n1 Hsub].
          eapply IHt_order with (B:=B ^^ t) (n1:=n1) (n2:=n0); eauto. simpl in H; eauto.
          rewrite (open_mono_order B t); eauto...
          replace G with (G ,, ld_ctx_nil) by auto.
          replace (B ^^ t) with ([t /_ x] B ^^ `x).
          replace A with ([t /_ x] A).
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
          replace A with ([`x0 /_ x] A).
          replace (B ^^ `x0) with ([`x0 /_ x] B ^^ `x).
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

Print Assumptions transitivity.