Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wl_red : Hdb_a_wl_red_completness.

Inductive dworklist_equiv_trailing_sub : dworklist -> dworklist -> Prop :=
| dworklist_equiv_trailing_sub__refl : forall Ω, dworklist_equiv_trailing_sub Ω Ω
| dworklist_equiv_trailing_sub__cons : forall Ω Ω' A B,
    dworklist_equiv_trailing_sub Ω Ω' ->
    dworklist_equiv_trailing_sub Ω (dworklist_conswork Ω' (work_sub A B)).

    (* Aᵃ Bᵃ Aᵈ Bᵈ *)

Fixpoint dworklist_size (Ω:dworklist) : nat :=
  match Ω with 
  | dworklist_empty => 0
  | dworklist_consvar Ω' _ _ => S (dworklist_size Ω')
  | dworklist_constvar Ω' _ _ => S (dworklist_size Ω')
  | dworklist_conswork Ω' _ => S (dworklist_size Ω')
  end.

(* Theorem d_a_wl_red_completness: forall n Ω Γ,
  dworklist_size Ω < n -> Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_completness.
 intro n. induction n; intros. 
 - admit.
 - dependent destruction H0.
   +
Admitted. *)

Theorem d_a_wl_red_completness: forall Ω Γ,
   Ω ⟶ᵈʷ⁎⋅ -> ⊢ᵃ Γ -> transfer Γ Ω  -> Γ ⟶ᵃʷ⁎⋅.
Proof with eauto with Hdb_a_wl_red_completness.
  intros. generalize dependent Γ. induction H; auto; unfold transfer in *; intros.
  - intros. destruct H1 as [θ]. dependent induction H.
    econstructor.
    econstructor.
    admit.
  - destruct H1 as [θ]. dependent induction H1...
    econstructor... eapply IHd_wl_red... admit.
    + eapply IHd_wl_red...
      exists ((X, dbind_typ T)::θ')...
      econstructor... admit. admit. admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - destruct H1 as [θ]. dependent destruction H1...
    + dependent destruction H2. 
      * dependent destruction H2. 
        -- admit.
        -- admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
