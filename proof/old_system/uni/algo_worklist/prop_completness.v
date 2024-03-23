Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wl_red : Hdb_a_wl_red_completness.


Theorem d_a_wl_red_completness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃʷ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with auto with Hdb_a_wl_red_completness.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros;
    try destruct H1 as [θ Htrans].
  - dependent induction Htrans...
    + dependent destruction H0... 
  - dependent induction Htrans...
    + constructor. apply IHd_wl_red.
      dependent destruction H0... 
      exists θ'...
    + constructor. eapply IHHtrans; eauto.
      dependent destruction H0... 
  - dependent induction Htrans...
    + constructor. apply IHd_wl_red.
      dependent destruction H0... 
      exists θ'...
    + constructor. eapply IHHtrans; eauto.
      dependent destruction H0...
  - dependent induction Htrans...
      + constructor. apply IHd_wl_red.
        dependent destruction H0... 
        exists θ'...
      + constructor. eapply IHHtrans; eauto.
        dependent destruction H0...
  - dependent induction Htrans...
    + dependent destruction H1.
      dependent destruction H0.
      * admit.
      * constructor; auto. 
        apply IHd_wl_red; auto.
        dependent destruction H1... 
        exists θ...
    + constructor. eapply IHHtrans; eauto.
      dependent destruction H0...
  - dependent induction Htrans...
      + dependent destruction H1.
        dependent destruction H.
        * admit.
        * constructor; auto. 
          apply IHd_wl_red; auto.
          dependent destruction H1... 
          exists θ...
      + constructor. eapply IHHtrans; eauto.
        dependent destruction H0...
  - dependent induction Htrans...
    + dependent destruction H1.
      dependent destruction H; dependent destruction H1.
      assert (exists Γ1, exists Γ2, aworklist_subst Γ X0 ` X Γ1 Γ2) by admit.
      destruct H5 as [Γ1 [Γ2 Hws]].
      * econstructor.
        admit.
        admit.
        admit.
        eauto.
        apply IHd_wl_red.
        admit.
        admit.
      * admit.
      * dependent destruction H0.
      admit.
      admit.
    + constructor. eapply IHHtrans; eauto.
      dependent destruction H0...
  - dependent induction Htrans.
    + dependent destruction H1.
      dependent destruction H1...
      dependent destruction H0...
      * admit.
      * admit.
      * admit.
    + constructor;  eapply IHHtrans; eauto.
        dependent destruction H0...

Admitted.
