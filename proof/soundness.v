Require Import Program.Equality.

Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.


Theorem soundness : forall Γ, la_worklist_reducible Γ -> exists Γ', transfer' Γ Γ' /\ ld_worklist_reducible Γ'.
Proof.
  intros. induction H.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl.
    exists (ld_wl_cons_tv dwl x5). split. 
    + dependent destruction H1. econstructor. econstructor. eauto.
    + econstructor; eauto. simpl. econstructor. admit. admit.
Admitted.