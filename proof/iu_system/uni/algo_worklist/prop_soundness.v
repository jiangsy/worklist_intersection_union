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
      apply H in H1
    end.

Lemma a_wf_wl_wf_ss : forall θ Γ Ω,  
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> wf_ss θ.
Proof.
Admitted.


Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with auto with Hdb_a_wl_red_soundness.
  intros. induction H0; auto; unfold transfer in *.
  - exists dworklist_empty. intuition...
    exists nil... 
  - dependent destruction H.
    apply IHa_wl_red in H1.
    destruct H1 as [Ω [Htr Hd_red]].
    admit.
  - _apply_IH_a_wl_red.
    destruct H2 as [Ω [Htrans Hd_red]].
    destruct Htrans as [θ Htrans].
    exists (dworklist_constvar Ω X dbind_tvar_empty).
    split. exists ((X, ss_bind__tvar_empty) :: θ).
    apply inst_wl__cons_tvar; auto.
    econstructor...
  - admit.
  - _apply_IH_a_wl_red. 
    destruct H4 as [Ω [Htrans Hd_red]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    dependent destruction H5.
    admit.
  - admit.
  - admit.
  - _apply_IH_a_wl_red. 
    destruct H3 as [Ω [Htrans Hd_red]].
    destruct Htrans as [θ Htrans].
    exists (dworklist_conswork Ω (work_sub typ_unit typ_unit)).
    split... exists θ... econstructor; eauto... econstructor. econstructor. admit.

Admitted.
