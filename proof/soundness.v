Require Import Program.Equality.

Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.
Require Import decl.properties.


(* https://github.com/VinaLx/dependent-worklist-inference/blob/e55fe9e7ca6b5e0538313a8cf44a57469923ca02/src-lite/transfer/properties.v#L665 *)
(* Lemma inst_e_rev_subst' : forall v' v x Θ e'
  , lc_aexpr e'
  → x `notin` (fv_aexpr v' `union` fv_ss Θ) → Θ ⊩ v' ⇝ v
  → forall e0
  , Θ ⊩ [v' /′ x] e' ⇝ e0
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof.
Admitted. *)

Lemma reorder: forall awl1 awl2 ex lbs ubs t m awl',
  reorder (la_wl_app (la_wl_cons_ev awl1 lbs ex ubs) awl2) ex t m la_wl_nil awl' -> 
  exists awl'1 awl'2, awl' = la_wl_app awl'1 awl'2.
Admitted.

Lemma inst_forall_inv: forall t' (θ: subst_set) ex t A, 
  wf_ss θ 
  -> inst_type (θ; ex : t) (open_la_type_wrt_la_type A (la_t_evar ex)) t' 
  -> (exists A', inst_type θ (la_t_forall A) A').
Proof.
  intros. 
  dependent induction H0. 
  - dependent destruction A; try inversion x.
    + exists (ld_t_forall (ld_t_var_b n)). 
      econstructor. intros. destruct n; simpl.
      * constructor. auto.
      * unfold open_la_type_wrt_la_type. unfold open_ld_type_wrt_ld_type. simpl. admit.
        (* not closed type  *)
    + exists (ld_t_forall (ld_t_var_f x0)). econstructor. intros.
      unfold open_la_type_wrt_la_type. unfold open_ld_type_wrt_ld_type. simpl. subst. econstructor. auto.
  - dependent destruction A; try inversion x.
    + destruct n; inversion x.
      exists (ld_t_forall (ld_t_var_b 0)).
      econstructor; intros. unfold open_la_type_wrt_la_type. unfold open_ld_type_wrt_ld_type.  simpl. econstructor. auto.
    + subst. exists (ld_t_forall t0).
      econstructor. intros. unfold open_la_type_wrt_la_type. unfold open_ld_type_wrt_ld_type.
      assert (t0 = (open_ld_type_wrt_ld_type_rec 0 (ld_t_var_f x0) t0)) by admit.
      simpl. rewrite <- H3. econstructor. subst; auto. 
      (* need wf to ensure ex5 != ex*)
      admit.
  - dependent induction A; try inversion x.
    + exists (ld_t_forall ld_t_int). admit.
    + destruct n; inversion x.
  - dependent destruction A; try dependent destruction x.
    + admit. (* ** *)
    + destruct n; inversion x. 
  - dependent destruction A; try dependent destruction x.
    + admit.
    + destruct n; inversion x. 
Admitted.


Lemma dwl_red_ctx_wf : forall dwl, 
  ld_worklist_reducible dwl -> ld_wf_context (ld_wl_to_ctx dwl).
Proof.
  induction dwl; intros; auto; 
  dependent destruction H; auto.
Qed.

(* Lemma tl_not_empty_inv: forall tl,
  la_tl_not_empty tl -> exists t tl', tl = la_tl_cons tl' t.
Proof.
  induction tl. *)


Lemma inst_ld_type_exists: forall θ t,
  exists t', inst_type θ t t'.
Admitted.

Theorem soundness : forall Γ, la_worklist_reducible Γ -> exists Γ', transfer Γ Γ' /\ ld_worklist_reducible Γ'.
Proof.
  intros. induction H.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl.
    exists (ld_wl_cons_tv dwl x5). split. 
    + dependent destruction H1. econstructor. econstructor. eauto.
    + econstructor; eauto. simpl. econstructor. 
      * now apply dwl_red_ctx_wf. 
      * admit.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl. 
    destruct tl.
    + simpl in *. exists dwl. split. 
      * unfold transfer in H1. destruct H1 as [θ'].
        exists (cons (pair ex5 (sse_ev ld_t_int)) θ'). eapply inst_wl_ev; eauto.
        admit. (* * dom *)
        constructor.
      * auto.
    + simpl in *.
      exists dwl. destruct H1 as [θ'].
      specialize (inst_ld_type_exists θ' t). intros. destruct H3 as [t'].
      split. unfold transfer.
      exists (cons (pair ex5 (sse_ev t')) θ'). econstructor; auto.
      -- admit.
      -- admit.
      -- admit.
      -- eapply inst_ev_ubs with (ub':=t') (t':=t'). 
        ++ generalize dependent dwl. induction tl; intros. 
          ** econstructor.
          ** dependent destruction H1. 
              eapply inst_ev_ubs with (ub':=t2') (t':=t'); admit.
        ++ admit. (* inst_weakening *)
        ++ econstructor; admit.
        ++ apply ld_sub_refl. admit.
      -- auto.
  - admit. (* same as previous *)
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl. 
    destruct tl; destruct tl'.
    + inversion H0. + inversion H. +inversion H0.
    + clear H. clear H0. admit.
  - destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]]. 
    exists (ld_wl_cons_w dwl (ld_w_sub ld_t_int ld_t_int)). split; auto. unfold transfer in *. 
    unfold transfer in Hdwl_trans. destruct Hdwl_trans as [θ Hθ]. 
    exists θ. econstructor; eauto. admit. admit.
    econstructor; eauto. econstructor. admit.
  - destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]]. 
    exists (ld_wl_cons_w dwl (ld_w_sub (ld_t_var_f x5) (ld_t_var_f x5))). split; auto.
    + admit.
    + econstructor; eauto.
      econstructor; admit.
  - destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]]. 
  (* **ex in wl -> ex : t in ss *)
  admit.
  - (* forall_l *) destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ]. inversion Hθ. 
    dependent destruction H6. subst.
    exists (ld_wl_cons_w dwl0 (ld_w_sub (ld_t_forall t1') t2')). (* fix this *) split.
    + subst. unfold transfer. exists θ'0. econstructor; eauto.
      * admit. 
      * admit. (* *ss_weakening *)
    + admit.
  - (* forall_r *) admit.
  - (* arrow *) destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.  destruct Hdwl_trans as [θ Hθ]. dependent destruction Hθ. dependent destruction Hθ.
    exists (ld_wl_cons_w dwl (ld_w_sub (ld_t_arrow t2' t1'0) (ld_t_arrow t1' t2'0))). split.
    + unfold transfer. exists θ'. eapply inst_wl_sub; eauto.
      econstructor; eauto. econstructor; eauto.
    + admit.
  - (* -> R *)
    destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ]. 
    dependent destruction Hθ.
    dependent destruction H4.
    dependent destruction H5.
    exists (ld_wl_cons_w dwl
                  (ld_w_sub (ld_t_arrow A0 B0) (ld_t_arrow A1 B1))).
    split; auto.
    unfold transfer. exists θ. econstructor.
    + admit. (* reorder of awl does not change its instantiated awl *)
    + admit. (* ex still exists in the reordered awl, and should be instantiated to the same type *)
    + constructor; auto.
  - (* -> L *)
  (* exactly same as the previous one*) 
    destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ]. 
    dependent destruction Hθ.
    dependent destruction H4.
    dependent destruction H5.
    exists (ld_wl_cons_w dwl
                (ld_w_sub (ld_t_arrow A0 B0) (ld_t_arrow A1 B1))).
    split; auto.
    unfold transfer. exists θ. econstructor.
    + admit. 
    + constructor; auto.
    + admit.
  - (* EVar L*)
    admit.
  - (* EVar L*)
    admit.
  - destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ].
    admit. 
  - admit.
Admitted.