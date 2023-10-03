Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors d_wl_del_red : Hdb_a_wl_red_soundness.


Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with auto with Hdb_a_wl_red_soundness.
  intros. induction H0; auto; unfold transfer in *.
  - dependent destruction H.
    apply IHa_wl_red in H1.
    destruct H1 as [Ω [Htr Hd_red]].
    admit.
  - dependent destruction H. 
    apply IHa_wl_red in H0.
    destruct H0 as [Ω [Htrans Hd_red]].
    destruct Htrans as [θ Htrans].
    exists (dworklist_constvar Ω X dbind_tvar_empty).
    econstructor. exists ((X, ss_bind__tvar_empty) :: θ).
    apply inst_wl__cons_tvar; auto.
    econstructor...
  - admit.
  - admit.
  -
Admitted.
