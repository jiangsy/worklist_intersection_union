Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wf_wl : Hdb_a_wl_red_soundness.
Hint Constructors inst_typ : Hdb_a_wl_red_soundness.
Hint Constructors inst_cont : Hdb_a_wl_red_soundness.
Hint Constructors inst_work : Hdb_a_wl_red_soundness.
Hint Constructors inst_worklist : Hdb_a_wl_red_soundness.
Hint Constructors wf_ss : Hdb_a_wl_red_soundness.
Hint Constructors d_wl_del_red : Hdb_a_wl_red_soundness.



Ltac destruct_a_wf_wl :=
  repeat
    match goal with
    | H : a_wf_wl (aworklist_conswork ?Γ ?w) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_consvar ?Γ ?w ?b) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_constvar ?Γ ?X ?b) |- _ => dependent destruction H
    | H : a_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : a_wf_typ ?E (?Ct ?A1 ?A2) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?b) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?e1 ?e2) |- _ => dependent destruction H
    end.


Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵃ ?Γ) -> ?P |- _ => destruct_a_wf_wl; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃ Γ) by auto with Hdb_a_wl_red_soundness;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2;
      destruct H2 as [Ω [Htrans Hdred]];
      destruct Htrans as [θ Htrans]
    end.

Lemma a_wf_wl_wf_ss : forall θ Γ Ω,  
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> wf_ss θ.
Proof.
Admitted.

Lemma a_wf_typ_trans_typ : forall θ Γ Ω Aᵃ,
  a_wf_typ (awl_to_aenv Γ) Aᵃ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> exists Aᵈ,
    inst_typ θ Aᵃ Aᵈ.
Admitted.



Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto with Hdb_a_wl_red_soundness.
  intros * Hwfa Hared. induction Hared; auto; unfold transfer in *.
  - exists dworklist_empty. intuition...
  - _apply_IH_a_wl_red. 
    eapply a_wf_typ_trans_typ in H0...
    destruct H0 as [Aᵈ].
    exists (dworklist_consvar Ω x (dbind_typ Aᵈ))...
  - _apply_IH_a_wl_red.
    exists (dworklist_constvar Ω X dbind_tvar_empty)...
    split... exists ((X, ss_bind__tvar_empty) :: θ)...
  - _apply_IH_a_wl_red. admit.
  - destruct_a_wf_wl; intuition.
    + admit.
    + admit.
    + admit.
    + subst. _apply_IH_a_wl_red.
      admit.
  - admit.
  - admit.
  - _apply_IH_a_wl_red. 
    exists (dworklist_conswork Ω (work_sub typ_unit typ_unit)).
    split... exists θ... econstructor; eauto... econstructor. econstructor. admit.
    admit.
    admit.
  - _apply_IH_a_wl_red.
    admit.
  -
Admitted.
