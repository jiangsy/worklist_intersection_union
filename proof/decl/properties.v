Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.

Require Import decl.notations.
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
  A = [`x /ᵈ x] A.
Proof.
  intros.
  induction A; auto.
  - simpl. rewrite <- IHA. auto.
  - simpl. rewrite <- IHA1. rewrite <- IHA2. auto.
  - simpl. destruct (x0==x); subst; auto.
Qed.


Lemma open_subst_eq : forall A x t, 
  x `notin` fv_ld_type A -> lc_ld_type t  ->
    A ^^ᵈ t = [t /ᵈ x] A ^^ᵈ `x.
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

Print ld_in_context_other.


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
    ld_mono_type t' -> ld_wf_mtype (G1, x,, G2) t -> G1 ⊢ t' ->  ld_wf_mtype (G1,, G2) ([t' /ᵈ x] t).
Proof.
  intros.
  dependent induction H0.
  - simpl. econstructor. 
    replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H0 by auto. eapply ld_wf_ctx_weakening; eauto.
  - simpl. destruct (x0 == x).
    + apply ld_wf_mtype_equiv_ld_wf_type_and_mono. intuition.
      replace (G1,,G2) with (G1,,G2,,ld_ctx_nil) by auto. eapply ld_wf_type_weakening. eauto.
      simpl. replace (G1, x,, G2) with (G1,,(ld_ctx_nil, x),,G2) in H1 by auto. eapply ld_wf_ctx_weakening; eauto.
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
      | _ : _ |-  context [ ([?e /ᵈ ?x] ?A) ^^ᵈ ` ?x' ] => 
        replace (` x') with ([e /ᵈ x] `x') by (apply subst_ld_type_fresh_eq; auto)
    end; repeat rewrite <- subst_ld_type_open_ld_type_wrt_ld_type by auto.


Theorem ld_mono_is_ld_lc : forall t, 
  ld_mono_type t -> lc_ld_type t.
Proof.
  intros. induction H; auto.
Qed.


Theorem substitution : forall G1 G2 x A B t,
  G1 , x  ,, G2 ⊢ A <: B -> 
  G1 ⊢ t -> 
  ld_mono_type t -> 
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
  - simpl. eapply ld_sub_foralll with (t:=[t /ᵈ x] t0). 
    + apply ld_wf_mtype_subst; auto.
    + replace (([t /ᵈ x] A) ^^ᵈ ([t /ᵈ x] t0)) with ([t /ᵈ x] A ^^ᵈ t0).
      * apply IHld_sub; auto.
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type; auto. now apply ld_mono_is_ld_lc.
  - simpl. eapply ld_sub_forallr with (L:=L `union` singleton x).
    intros. inst_cofinites_with x0.
    rewrite_subst_open_var.
    replace  (([t /ᵈ x] B) ^^ᵈ ([t /ᵈ x] ` x0)) with ( [t /ᵈ x] B ^^ᵈ ` x0).
    + replace (G1,, G2, x0 ) with (G1,, (G2, x0)) by auto. apply H0; auto.
    + rewrite subst_ld_type_open_ld_type_wrt_ld_type. reflexivity. simpl.
      replace (G1,, G2, x0 ) with (G1,, (G2, x0)) by auto. now apply ld_mono_is_ld_lc.
Qed.


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
  ld_mono_type t -> type_order (A ^^ᵈ t) = type_order A.
Proof.
  intros.
  eapply open_mono_order_rec; auto.  
Qed.

Reserved Notation "G ⊢ t1 <: t2 | n"
  (at level 65, t1 at next level, t2 at next level, no associativity).
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

Hint Constructors sized_ld_sub : trans.

Lemma sized_ld_sub_to_ld_sub : forall G t1 t2 n,
  G ⊢ t1 <: t2 | n -> G ⊢ t1 <: t2.
Proof.
  intros. induction H; eauto.
Qed.


Lemma sized_ld_sub_weakening : forall G1 G2 G3 t1 t2 n,
  G1 ,, G3 ⊢ t1 <: t2 | n -> 
  ⊢ G1 ,, G2 ,, G3 ->
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
  G ⊢ t1 <: t2 | n -> 
  x `notin` ld_ctx_dom G -> 
  G , x ⊢ t1 <: t2 | n.
Proof.
  intros.
  replace (G , x) with (G ,, (ld_ctx_cons ld_ctx_nil x) ,, ld_ctx_nil) by auto.
  eapply sized_ld_sub_weakening; auto.
  simpl. constructor; auto.
  apply sized_ld_sub_to_ld_sub in H. apply ld_sub_wf_ctx in H. auto.
Qed.


Theorem ld_wf_type_is_wf_ctx : forall G A,
  ld_wf_type G A -> ⊢ G.
Proof.
  intros. induction H; auto.
  inst_cofinites_with_new. dependent destruction H0.
  auto.
Qed.

Theorem context_cons_app_eq : forall G1 G2 x,
  G1, x ,, G2 = G1 ,, (ld_ctx_nil, x ,, G2).
Proof.
  intros. induction G2; auto.
  simpl. rewrite IHG2. auto.
Qed.

Theorem ld_wf_ctx_middle : forall G1 G2 x x',
  x <> x' -> ld_wf_context (G1, x,, G2) -> ld_wf_context (G1, x',, G2) -> ld_wf_context (G1, x', x,, G2).
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
  G1 , x' ,, G2 ⊢ [`x' /ᵈ x] A <: [`x' /ᵈ x] B | n.
Proof with auto with trans.
  intros. dependent induction H; simpl; auto...
  - simpl. destruct (x0 == x). 
    + subst. constructor; auto. clear H1. clear H0. clear H. induction G2.
      * simpl. constructor.
      * simpl. constructor. eauto.
    + constructor.
      * auto.
      * eapply ld_in_context_other in H0; eauto.
        replace (G1,x',,G2) with (G1,,(ld_ctx_nil, x'),,G2) by auto. apply ld_in_context_weakenning. auto.
  - simpl. eapply sls_foralll with (t:=[`x' /ᵈ x] t). 
    + destruct (x==x'); subst.
      * replace ([` x' /ᵈ x'] t) with t; auto.
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
    + replace (([`x' /ᵈ x] A) ^^ᵈ ([`x' /ᵈ x] t)) with ([`x' /ᵈ x] A ^^ᵈ t).
      * apply IHsized_ld_sub; auto.
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type; auto. 
  - simpl. eapply sls_forallr with (L:=L `union` singleton x `union` ld_ctx_dom ( G1, x',, G2)).
    intros. inst_cofinites_with x0.
    rewrite_subst_open_var.
    replace  (([`x' /ᵈ x] B) ^^ᵈ ([`x' /ᵈ x] ` x0)) with ( [`x' /ᵈ x] B ^^ᵈ ` x0).
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
  intros. induction H; eauto...
  + destruct IHld_sub1 as [n1].
    destruct IHld_sub2 as [n2].
    exists (S (n1 + n2)). auto...
  + destruct IHld_sub as [n].
    exists (S n). auto...
  + inst_cofinites_by (L `union` fv_ld_type A `union` fv_ld_type B). destruct H0 as [n].
    exists (S n). eapply sls_forallr with (L:=L `union` (ld_ctx_dom G)). intros.
    replace (G, x0) with (G, x0,,ld_ctx_nil) by auto.
    replace A with ([`x0 /ᵈ x] A).
    replace (B ^^ᵈ `x0) with ([`x0 /ᵈ x] B ^^ᵈ `x).
    eapply sized_var_substitution; eauto.
    * simpl. auto.
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


Theorem generalized_transitivity : forall t_order t_ssize G A B C n1 n2 ,
  type_order B < t_order ->
  n1 + n2 < t_ssize -> 
  (G ⊢ A <: B | n1) -> (G ⊢ B <: C | n2) -> G ⊢ A <: C.
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
        * eapply ld_sub_forallr with (L:=L `union` ld_ctx_dom G). 
          intros. inst_cofinites_with x.
          eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1:=S (n1 + n0)); eauto...
      + eapply ld_sub_foralll with (t:=t). auto.
        eapply IHt_ssize with (B:=B); eauto...
      + dependent destruction H2. 
        * inst_cofinites_by (L `union` fv_ld_type A `union` fv_ld_type B).
          apply ld_wf_mtype_equiv_ld_wf_type_and_mono in H2. destruct H2.
          specialize (sized_substitution G ld_ctx_nil x _ _ _ _ H1 H2 H4).
          intros. destruct H5 as [n1 Hsub].
          eapply IHt_order with (B:=B ^^ᵈ t) (n1:=n1) (n2:=n0); eauto. simpl in H; eauto.
          rewrite (open_mono_order B t); eauto...
          replace G with (G ,, ld_ctx_nil) by auto.
          replace (B ^^ᵈ t) with ([t /ᵈ x] B ^^ᵈ `x).
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
          replace A with ([`x0 /ᵈ x] A).
          replace (B ^^ᵈ `x0) with ([`x0 /ᵈ x] B ^^ᵈ `x).
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