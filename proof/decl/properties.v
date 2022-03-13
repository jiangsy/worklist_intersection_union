Require Import Coq.Program.Equality.

Require Import decl.notations.

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