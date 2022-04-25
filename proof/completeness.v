Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.


Theorem completeness : forall Γ', ld_worklist_reducible Γ' -> exists Γ, transfer' Γ Γ' /\ la_worklist_reducible Γ.
Proof.
Admitted.