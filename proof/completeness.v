Require Import Coq.Program.Equality.

Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.


Theorem completeness : forall Γᵈ Γᵃ θ, 
  ld_worklist_reducible Γᵈ -> 
  inst_worklist nil Γᵃ Γᵈ θ -> 
  la_worklist_reducible Γᵃ.
Proof.
  intros.
  induction H0; intros.
  - admit.
  (* - econstructor. admit. *)
  (* - intros. 
    unfold transfer in H1.
    destruct H1 as [θ].
    dependent induction H1.
    + econstructor. admit.
      apply IHld_worklist_reducible.
      unfold transfer. exists θ'.
      auto.
    + econstructor.
      admit. *)
  - intros. 
    unfold transfer in H1.
   + dependent induction H1.
      * admit.
      * dependent destruction H3.
        -- econstructor.
          ** admit. (* wf_wl *)
          ** econstructor. 
          ** admit. (* special case of reorder (not reorder) *)
          ** admit. 
        -- econstructor.
          ** admit.
          ** admit.
          ** admit.
Admitted.


Theorem completeness' : forall Γᵈ Γᵃ, 
  ld_worklist_reducible Γᵈ -> 
  transfer Γᵃ Γᵈ -> 
  la_worklist_reducible Γᵃ.
Proof.
  intros.
  generalize dependent Γᵃ.
  induction H; intros.

  (* ⊢ ⋅ *)
  - unfold transfer in H0.
    destruct H0 as [θ].
    dependent induction H.
    + admit. (* missing in the current rule *)
    + econstructor.
      assert (la_worklist_reducible Γᵃ).
      * auto.
      * admit.

  (* ⊢ G, x *)
  - unfold transfer in H1.
    destruct H1 as [θ].
    dependent induction H1.
    + econstructor.
      -- admit.
      -- apply IHld_worklist_reducible.
      unfold transfer.
      exists θ'.
      auto.
    + econstructor.
      assert (la_worklist_reducible Γᵃ).
      -- eapply IHinst_worklist; eauto.
      -- admit.

  (* ⊢ G, t1 <: t2 *)
  - unfold transfer in H1.
    destruct H1 as [θ].
    dependent destruction H1.
    + dependent destruction H2.
      * dependent destruction H3.
        -- dependent destruction H.
           econstructor.
           admit.
           apply IHld_worklist_reducible.
           unfold transfer. exists θ.
           auto.
        -- dependent destruction H.
           ++ eapply la_wlred_mono_evar. 
            ** admit. (* wf_wl *)
            ** econstructor. 
            ** admit. (* special case of reorder (not reorder) *)
            ** admit.
           ++ admit. (* impossible *)
          -- inversion H. 
          -- inversion H.
          -- admit. (* x < forall y. A *)
      * dependent destruction H4; admit.
      * dependent destruction H3.
        -- inversion H.
        -- dependent destruction H.
           ++ admit.
           ++ admit. (* impossible *) 
        -- econstructor. 
           apply IHld_worklist_reducible.
           unfold transfer.
           exists θ. auto.
        -- inversion H.
        -- admit. (* impossible *)
      (* arrow *)
      * dependent destruction H.
        -- dependent destruction H3.
          (* A -> B <: ^x *)
          ++ admit.

          (* A1 -> B1 <: A2 -> B2 *)
          ++ econstructor.

             admit.
        -- admit. (* impossible *)
      * admit.

    (* ⊢ G, [l] <: ^x <: [u] *)
    + econstructor.
      admit.
Admitted.
