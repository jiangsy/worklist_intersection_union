Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.
Require Import ln_utils.

Theorem completeness : forall Γᵈ Γᵃ, 
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
    + econstructor. 
    + econstructor.
      assert (la_worklist_reducible Γᵃ).
      * auto.
      * admit.

  (* ⊢ G, x *)
  - unfold transfer in H0.
    destruct H0 as [θ].
    dependent induction H0.
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

  (* ⊢ G, int <: int *)
  - unfold transfer in H0.
    destruct H0 as [θ].
    dependent destruction H0.
    + dependent destruction H1.
      * dependent destruction H3.
        -- econstructor.
           admit. (* wf *)
           admit.
           apply IHld_worklist_reducible.
           unfold transfer. exists θ.
           eauto.
        -- eapply la_wlred_evar_mono.
           ++ admit. (* wf_wl *)
           ++ econstructor. 
           ++ admit. (* special case of reorder (not reorder) *)
           ++ admit.
      * dependent destruction H2.
        -- econstructor; admit.
        -- econstructor. admit.
    (* last entry is another ex *)
    + econstructor.

  (* ⊢ G, x <: x *)
  - unfold transfer in H0.  
    destruct H0 as [θ].
    dependent destruction H0.
    + dependent destruction H1.
      * dependent destruction H2.
        -- econstructor.
           ++ admit. (* wf *)
           ++ apply IHld_worklist_reducible.
              unfold transfer. exists θ.
              auto.
        -- admit.
      * dependent destruction H3.
        -- admit.
        -- admit.
    + (* last entry is another ex *)
      admit.

  (* ⊢ G, forall x. A <: B *)
  - unfold transfer in H2.
    destruct H2 as [θ].
    dependent destruction H2.
    + dependent destruction H3.
      * specialize (wf_mono _ _ _ H3 H4).
        intros. inversion H6.
      * inst_cofinites_by (L `union` evar_dom Γᵃ). 
        eapply la_wlred_forall_l with (ex5:=x).
        -- admit.
        -- auto.
        -- apply IHld_worklist_reducible.
           unfold transfer. exists (θ; x: t).
           econstructor.
           ++ econstructor; auto.
              ** admit.
              ** econstructor.
           ++ admit.
           ++ admit. (* weakening *)

    (* last entry is another ex *)
    + admit.
  (* ⊢ Γ, A <: forall x. B *)
  - unfold transfer in H1.
    destruct H1 as [θ].
    dependent destruction H1.
    + dependent destruction H3. 
      * specialize (wf_mono _ _ _ H3 H4).
        intros. inversion H5.
      * eapply la_wlred_forall_r with (L:=L0 `union` L). 
        intros.
        inst_cofinites_with x5.
        eapply H0.
        unfold transfer. exists (θ; x5). econstructor.
        -- econstructor; auto.
        -- admit. (* inst weakening *)
        -- admit. (* inst weakening *)
    + (* last entry is another ex *)
      admit.
  - unfold transfer in H0.
    destruct H0 as [θ].
    dependent destruction H0.
    + dependent destruction H1.
      * dependent destruction H3.
        -- admit.
        -- assert ((la_mono_type (la_t_arrow A' B')) + ~ (la_mono_type (la_t_arrow A' B'))) by admit.
        destruct H3.
          ++ eapply la_wlred_evar_mono; auto.
      * dependent destruction H2.
        -- admit.
        -- econstructor.
          apply IHld_worklist_reducible.
          unfold transfer. exists θ.
          econstructor; auto.
          econstructor; auto.
    + (* last entry is another ex *)
      admit.
Admitted.
