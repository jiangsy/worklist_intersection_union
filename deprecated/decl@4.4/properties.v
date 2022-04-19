Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import decl.notations.


Definition wf_dom : forall {Γ}, ⊢ Γ -> atoms.
Proof.
  intros.
  set (x := ctx_dom Γ). exact x.
Defined.

Ltac gather_for_weakening :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : ld_context => ctx_dom x) in
  let D := gather_atoms_with wf_dom in
  constr:(A `union` B `union` C `union` D).

Ltac apply_fresh_base_fixed H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  let x := fresh atom_name in
  pick fresh x excluding L and apply H.

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weakening" :=
  apply_fresh_base_fixed H gather_for_weakening x.

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
    eapply ld_wf_type_weakening; auto.
  - pick fresh x and apply ld_sub_forallr for weakening.
    replace (G1,, G2,, G3, x) with (G1,, G2,, (G3, x)) by auto.
    eapply H0; auto. constructor; auto.
Qed.