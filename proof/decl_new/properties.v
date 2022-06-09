Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Metalib.Metatheory.


Require Import decl_new.notations.
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
  - eapply ld_sub_forallr with (L:=L `union` (ld_ctx_dom G)). intros. 
    inst_cofinites_with x. eapply ld_sub_foralll with (t := `x); auto.
    constructor.
    + eapply ld_sub_wf_ctx; eauto.
    + simpl. auto. 
Qed.


Lemma ld_sub_mono_symm : 
  forall G t1 t2, ld_mono_type t1 -> ld_mono_type t2 -> ld_sub G t1 t2 -> ld_sub G t2 t1.
Proof.
  intros.
  dependent induction H1; auto.
  - dependent destruction H. dependent destruction H1. eauto. 
  - inversion H.
  - inversion H0.
Qed.

Lemma ld_wl_red_mono_refl :  forall Γ t1 t2, 
  ld_mono_type t1 -> 
  ld_mono_type t2 -> 
  ld_worklist_reducible (ld_wl_cons_w Γ (ld_w_sub t1 t2)) -> 
  ld_worklist_reducible (ld_wl_cons_w Γ (ld_w_sub t2 t1)).
Proof.
  intros.
  dependent destruction H1.
  constructor; auto.
  apply ld_sub_mono_symm; auto.
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
  - eapply ld_wft_forall with (L:=L `union`  ld_ctx_dom (G1,, G2,, G3)). intros.
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
  dependent induction H; try constructor; auto.
  - eapply ld_in_context_weakenning. auto.
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
  - inversion H. dependent induction H0; auto.
    + dependent destruction H1. intuition.
    + inversion H2. 
Qed.


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
Qed.

Ltac rewrite_subst_open_var :=
  repeat
    match goal with 
      | _ : _ |-  context [ ([?e /_ ?x] ?A) ^^ ` ?x' ] => 
        replace (` x') with ([e /_ x] `x') by (apply subst_ld_type_fresh_eq; auto)
    end; repeat rewrite <- subst_ld_type_open_ld_type_wrt_ld_type by auto.


Theorem ld_mono_is_ld_lc : forall t, 
  ld_mono_type t -> lc_ld_type t.
Proof.
  intros. induction H; auto.
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


Reserved Notation "G ⊢ t1 <: t2 | n"
  (at level 65, t1 at next level, t2 at next level, no associativity).

Fixpoint type_order (t : ld_type) : nat :=
  match t with
  | ld_t_arrow A B => type_order A + type_order B
  | ld_t_forall A  => S (type_order A)
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


Inductive sized_ld_sub : ld_context -> ld_type -> ld_type -> nat -> Prop :=
  | sls_var : forall G x,
    ⊢ G ->  ld_in_context x G -> G ⊢ (ld_t_var_f x) <: (ld_t_var_f x) | 0
  | sls_int : forall G,
    ⊢ G -> G ⊢ ld_t_int <: ld_t_int | 0
  | sls_arrow : forall G A B C D n1 n2,
    G ⊢ C <: A | n1 ->
    G ⊢ B <: D | n2 ->
    G ⊢ (ld_t_arrow A B) <: (ld_t_arrow C D) | S (n1 + n2)
  | sls_foralll : forall G A B t n,
    ld_wf_mtype G t ->
    G ⊢ (open_ld_type_wrt_ld_type A t) <: B | n ->
    G ⊢ (ld_t_forall A) <: B | S n
  | sls_forallr : forall L G A B n,
    (forall x, x \notin L -> (ld_ctx_cons G x) ⊢ A <: (open_ld_type_wrt_ld_type B (ld_t_var_f x)) | n) ->
    G ⊢ A <: (ld_t_forall B) | S n
where "G ⊢ t1 <: t2 | n" := (sized_ld_sub G t1 t2 n).

Lemma sized_ld_sub_to_ld_sub : forall G t1 t2 n,
  G ⊢ t1 <: t2 | n -> (ld_sub G t1 t2).
Proof.
  intros. induction H; eauto.
Qed.

Lemma sized_ld_sub_weakening : forall G1 G2 G3 t1 t2 n,
  G1 ,, G3 ⊢ t1 <: t2 | n -> ⊢ G1 ,, G2 ,, G3 ->
  G1 ,, G2 ,, G3 ⊢ t1 <: t2 | n.
Proof.
  intros.
  dependent induction H; try constructor; auto.
  - eapply ld_in_context_weakenning; auto.
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



Theorem sized_substitution : forall G1 G2 x A B t n,
  G1 , x  ,, G2 ⊢ A <: B | n ->
  ld_wf_type G1 t -> ld_mono_type t ->
  G1 ,, G2 ⊢ [t /_ x] A <: [t /_ x] B | n.
Proof.
  intros.
  dependent induction H.
Admitted.

Hint Resolve sized_ld_sub_to_ld_sub : trans.

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
          eapply IHt_ssize with (B:=C0); eauto; lia. 
          eapply IHt_ssize with (B:=D); eauto; lia.
        * eapply ld_sub_forallr with (L:=L `union` ld_ctx_dom G). intros. inst_cofinites_with x.
          eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1:=S (n1 + n0)); eauto. lia.
          econstructor; eapply sized_ld_sub_weakening_cons; eauto. 
      + eapply ld_sub_foralll with (t:=t). auto.
        eapply IHt_ssize with (B:=B); eauto. lia.
      + dependent destruction H2. 
        * eapply IHt_order with (B:=B ^^ t) (n1:=n) (n2:=n0); eauto. simpl in H; eauto.
          rewrite (open_mono_order B t). lia. eapply ld_wf_mtype_is_mtype; eauto.
          inst_cofinites_by (L `union` fv_ld_type A `union` fv_ld_type B).
          replace G with (G ,, ld_ctx_nil) by auto.
          replace (B ^^ t) with ([t /_ x] B ^^ `x).
          replace A with ([t /_ x] A).
          apply sized_substitution; auto. 
          -- apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H2; intuition.
          -- apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H2; intuition.
          -- rewrite subst_ld_type_fresh_eq; auto.
          -- apply eq_sym. eapply open_subst_eq; auto. 
             apply ld_mono_is_ld_lc. apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H2. intuition.
        * apply ld_sub_forallr with (L:=L `union` L0 `union` fv_ld_type B `union` fv_ld_type A).
          intros. inst_cofinites_with x.
          
          eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n) (n2:=n0); auto. lia. 
          eapply sls_forallr with (L:= (ld_ctx_dom G) `union` singleton x). intros.
          assert (⊢ G, x). {
            eapply ld_sub_wf_ctx; eauto.
            eapply sized_ld_sub_to_ld_sub. eauto.
          } 
          assert (⊢ G, x0). {
            constructor. dependent destruction H5. auto. auto.
          }


          replace (G, x, x0) with (G ,, (ld_ctx_nil,  x) ,, (ld_ctx_nil, x0)) by auto.
          eapply sized_ld_sub_weakening. simpl.
          replace A with ([`x0 /_ x] A).
          replace (B ^^ `x0) with ([`x0 /_ x] B ^^ `x).
          replace (G, x0) with (G, x0,, ld_ctx_nil) by auto.
          apply sized_substitution; auto.
          -- simpl. replace (G, x0, x) with (G ,, (ld_ctx_nil,  x0) ,, (ld_ctx_nil, x)) by auto. eapply sized_ld_sub_weakening. simpl. auto.
          simpl. constructor; simpl. auto. 
          apply notin_add_3. 
          apply notin_union_2 in H4. apply notin_singleton_1 in H4. unfold not. intros. subst. contradiction. dependent destruction H5. auto. 
          -- apply eq_sym. eapply open_subst_eq; auto.
          -- rewrite subst_ld_type_fresh_eq; auto.
          -- simpl. econstructor. eauto.
             simpl. auto.
Qed.