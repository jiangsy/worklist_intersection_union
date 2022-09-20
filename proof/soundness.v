Require Import Program.Equality.

Require Import algo.ott.
Require Import decl.ott.
Require Import transfer.


Lemma inst_forall_inv: forall t' (θ: subst_set) ex t A, inst_type (θ; ex : t) (open_la_type_wrt_la_type A (la_t_evar ex)) t' -> (exists A', inst_type θ (la_t_forall A) A').
Proof.
  intros. induction A.
Admitted.


(* Lemma inst_e_rev_subst' : forall v' v x Θ e'
  , lc_aexpr e'
  → x `notin` (fv_aexpr v' `union` fv_ss Θ) → Θ ⊩ v' ⇝ v
  → forall e0
  , Θ ⊩ [v' /′ x] e' ⇝ e0
  → exists e, [v /' x] e = e0 ∧ Θ ⊩ e' ⇝ e.
Proof. *)



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
    + admit.
  - admit. (* same as previous *)
  - destruct tl; destruct tl'.
    + inversion H0. + inversion H. +inversion H0.
    + admit.
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
  - (* e_var *) admit.
  - (* forall_l *) destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans. destruct Hdwl_trans as [θ Hθ]. inversion Hθ. 
    dependent destruction H6. subst.
    exists (ld_wl_cons_w dwl0 (ld_w_sub (ld_t_forall t1') t2')). (* fix this *) split.
    + subst. unfold transfer. exists θ'0. econstructor; eauto.
      * econstructor. admit.
      * admit.
    + admit.
  - (* forall_r *) admit.
  - (* arrow *) destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.  destruct Hdwl_trans as [θ Hθ]. dependent destruction Hθ. dependent destruction Hθ.
    exists (ld_wl_cons_w dwl (ld_w_sub (ld_t_arrow t2' t1'0) (ld_t_arrow t1' t2'0))). split.
    + unfold transfer. exists θ'. eapply inst_wl_sub; eauto.
      econstructor; eauto. econstructor; eauto.
    + admit.
  - destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans. destruct Hdwl_trans as [θ Hθ]. 
    exists dwl. split.
    + unfold transfer. exists θ. econstructor.
Admitted.