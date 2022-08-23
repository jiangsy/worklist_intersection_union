Require Import Program.Equality.

Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.


Theorem soundness : forall Γ, la_worklist_reducible Γ -> exists Γ', transfer Γ Γ' /\ ld_worklist_reducible Γ'.
Proof.
  intros. induction H.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl.
    exists (ld_wl_cons_tv dwl x5). split. 
    + dependent destruction H1. econstructor. econstructor. eauto.
    + econstructor; eauto. simpl. econstructor. admit. admit.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl. 
    destruct tl.
    + simpl in *. exists dwl. split. 
      * unfold transfer in H1. destruct H1 as [θ'].
        exists (cons (pair ex5 (sse_ev ld_t_int)) θ'). eapply inst_wl_ev; eauto.
        admit. constructor.
      * auto.
    +
Admitted.