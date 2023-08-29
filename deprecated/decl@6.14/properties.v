(* Require Import Coq.Program.Equality.
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

Lemma ld_sub_mono_refl : 
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
  apply ld_sub_mono_refl; auto.
Qed.


Lemma ld_in_context_weakenning : 
  forall G1 G2 G3 x,
  ld_in_context x (G1,,G3) -> ld_in_context x (G1,,G2,,G3).
Proof.
  intros.
  induction G3.
  - induction G2.
    + auto.
    + simpl in *. auto.
  - simpl in *. inversion H; subst.
    + apply ld_inc_here.
    + apply ld_inc_there. auto.
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


Reserved Notation "G ⊢ t1 <: t2 | n"
  (at level 65, t1 at next level, t2 at next level, no associativity).

Fixpoint type_order (t : ld_type) : nat :=
  match t with
  | ld_t_arrow A B => type_order A + type_order B
  | ld_t_forall A  => S (type_order A)
  | _ => 0
  end.


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
    ld_notforall_type B ->
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

Hint Resolve sized_ld_sub_to_ld_sub : trans.

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
        * eapply ld_sub_forallr with (L:=L). intros. inst_cofinites_with x.
          eapply IHt_ssize with (B:=ld_t_arrow C0 D) (n1:=S (n1 + n0)); eauto. lia.
          econstructor; admit.
      + destruct H4.
        * eauto...
        * eauto...
        * econstructor; eauto. admit.
          eapply IHt_ssize with (B:=ld_t_arrow A0 B) (n1:=n) (n2:=S (n1 + n2)); eauto. lia.
          econstructor; eauto.
        * inversion H1.
        * eapply ld_sub_forallr. intros.
          eapply IHt_ssize with (B:=A0) (n1:=S n) (n2:=n0); eauto. admit.
          eapply sls_foralll with (t:=t). eauto. admit. admit. 
      + dependent destruction H2.
        * eapply IHt_order with (B:=B ^^ t) (n1:=n) (n2:=n0); eauto. admit. admit. 
        * rename B0 into C. eapply ld_sub_forallr with (L:=L `union` L0). intros.
          eapply IHt_ssize with (B:=ld_t_forall B) (n1:=S n) (n2:=n0); auto. lia.
          eapply sls_forallr.
          eapply H2; eauto. lia. intros.
      Admitted. *)
