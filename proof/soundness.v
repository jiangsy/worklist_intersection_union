Require Import Program.Equality.

Require Import algo.ott.
Require Import algo.notations.
Require Import algo.ln_inf_extra.
Require Import decl.ott.
Require Import decl.notations.
Require Import decl.ln_inf.
Require Import decl.ln_inf_extra.
Require Import decl.properties.
Require Import transfer.
Require Import ln_utils.


Lemma reorder: forall awl1 awl2 ex lbs ubs t m awl',
  reorder (la_wl_app (la_wl_cons_ev awl1 lbs ex ubs) awl2) ex t m la_wl_nil awl' -> 
  exists awl'1 awl'2, awl' = la_wl_app awl'1 awl'2.
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


Theorem soundness : forall Γ,
  la_worklist_reducible Γ -> 
  exists Γ', transfer Γ Γ' /\ ld_worklist_reducible Γ'.
Proof.
  intros. induction H.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl.
    exists (ld_wl_cons_tv dwl x5). split. 
    + dependent destruction H1. econstructor. econstructor. eauto.
    + econstructor; eauto. simpl. econstructor. 
      * now apply dwl_red_ctx_wf. 
      * admit.
  - destruct IHla_worklist_reducible as [dwl Hdwl]. destruct Hdwl.
    unfold transfer in H0. destruct H0 as [θ'].
    (* induction tl'.
    + simpl in *. destruct tl.
      * simpl in *. exists dwl. split. exists (θ'; ex5: ld_t_int). econstructor; auto. admit.
      econstructor. auto.
      * simpl in *. induction tl; admit.
    + admit. *)
    remember (la_tl_app tl tl'). destruct l.
    + simpl in *. admit.
    + simpl in *. admit.
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
  - (* forall_l *) 
    destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ]. dependent destruction Hθ.
    dependent destruction Hθ.
    apply inst_subst in H5.
    replace ([ld_type_to_la_type tᵈ /^ᵃ ex5] A ^^ᵃ `^ ex5 ) with ([ld_type_to_la_type tᵈ /ᵃ ex5] A ^^ᵃ `ᵃex5 ) in H5.
    eapply inst_e_rev_subst with (tᵈ := tᵈ) in H5.
    destruct H5 as [t1'ᵈ Ht1'ᵈ].
    exists (ld_wl_cons_w Γᵈ (ld_w_sub (ld_t_forall (close_ld_type_wrt_ld_type ex5 t1'ᵈ)) t2ᵈ)). (* fix this *) split.
    + unfold transfer. exists θ'. econstructor; eauto.
      * eapply inst_t_forall. intros.
        assert (open_la_type_wrt_la_type A (la_t_tvar_f x) = [(`ᵃ x) /ᵃ ex5] (open_la_type_wrt_la_type A (la_t_tvar_f ex5))) by admit.
        assert (open_ld_type_wrt_ld_type (close_ld_type_wrt_ld_type ex5 t1'ᵈ) (ld_t_var_f x) = [(`ᵈ x) /ᵈ ex5] (open_ld_type_wrt_ld_type (close_ld_type_wrt_ld_type ex5 t1'ᵈ) (ld_t_var_f ex5))) by admit.
        rewrite H7. rewrite H8.
        apply inst_e_rename.
        rewrite open_ld_type_wrt_ld_type_close_ld_type_wrt_ld_type. intuition. 
        admit.
      * admit. (* *ss_weakening *)
    + dependent destruction Hdwl_red. econstructor.
      * eapply ld_sub_foralll with (t:= tᵈ). 
        admit.
        auto.
        replace (close_ld_type_wrt_ld_type ex5 t1'ᵈ ^^ᵈ tᵈ) with ([tᵈ /ᵈ ex5] close_ld_type_wrt_ld_type ex5 t1'ᵈ ^^ᵈ (`ᵈ ex5)).
        rewrite open_ld_type_wrt_ld_type_close_ld_type_wrt_ld_type. destruct Ht1'ᵈ.
        subst. auto.
        simpl.
        rewrite subst_ld_type_open_ld_type_wrt_ld_type.
        simpl.
        unfold eq_dec. destruct (EqDec_eq_of_X ex5 ex5).
        -- rewrite subst_ld_type_fresh_eq. auto.
           rewrite fv_ld_type_close_ld_type_wrt_ld_type.
           auto.
        -- contradiction.
        -- admit.
      * auto.
    + admit. (* lc *)
    + admit. (* fv *)
    + admit. (* ld_to_la tᵈ ⇝ tᵈ *)
    + admit. (* subst *)
    + admit. (* lc *)
    + admit. (* fv *)
  
  - (* forall_r *)
    inst_cofinites_by (L `union` fx_la_type B `union` fx_la_type A). 
    destruct H0 as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ]. dependent destruction Hθ.
    dependent destruction Hθ.
    exists (ld_wl_cons_w Γᵈ (ld_w_sub t1ᵈ (ld_t_forall (close_ld_type_wrt_ld_type x t2ᵈ)))).  split.
    + unfold transfer.
      exists θ'. econstructor; eauto. 
      eapply inst_t_forall with (L:=L). intros.
      replace (B ^ᵃ x0) with ([`ᵃ x0 /ᵃ x] (B ^ᵃ x)).
      replace (close_ld_type_wrt_ld_type x t2ᵈ ^ᵈ x0) with ( [`ᵈ x0 /ᵈ x] close_ld_type_wrt_ld_type x t2ᵈ ^ᵈ x).
      apply inst_e_rename.
      rewrite open_ld_type_wrt_ld_type_close_ld_type_wrt_ld_type. auto.
      * admit. (** something related to Γ and dom θ **)
      * rewrite subst_ld_type_open_ld_type_wrt_ld_type. simpl. 
        destruct (x == x).
        -- rewrite subst_ld_type_fresh_eq; auto.
           rewrite fv_ld_type_close_ld_type_wrt_ld_type. auto.
        -- contradiction.
        -- econstructor.
      * rewrite subst_la_type_open_la_type_wrt_la_type. simpl.
        unfold eq_dec. destruct ( EqDec_eq_of_X x x).
        -- rewrite subst_la_type_fresh_eq; auto.
        -- contradiction.
        -- econstructor.
    + dependent destruction Hdwl_red. 
      dependent destruction Hdwl_red. 
      econstructor.
      * eapply ld_sub_forallr with (L:=fv_ld_type t2ᵈ `union` fv_ld_type t1ᵈ `union` ld_ctx_dom (ld_wl_to_ctx Γᵈ)). 
        intros.
        replace ( close_ld_type_wrt_ld_type x t2ᵈ ^ᵈ x0) with ( [`ᵈ x0 /ᵈ x] close_ld_type_wrt_ld_type x t2ᵈ ^ᵈ x).
        replace t1ᵈ with ([`ᵈ x0 /ᵈ x] t1ᵈ).
        replace (ld_wl_to_ctx Γᵈ, x0 ) with (ld_wl_to_ctx Γᵈ, x0,, ld_ctx_nil) by auto.
        apply ld_sub_rename.
        rewrite open_ld_type_wrt_ld_type_close_ld_type_wrt_ld_type. auto.
        -- simpl in *. inversion H3. constructor; auto.
        -- rewrite subst_ld_type_fresh_eq; auto. 
           admit. (* fv and fx between instantiation *)
        -- rewrite subst_ld_type_open_ld_type_wrt_ld_type. simpl. 
           destruct (x == x).
           ++ rewrite subst_ld_type_fresh_eq; auto.
              rewrite fv_ld_type_close_ld_type_wrt_ld_type. auto.
           ++ contradiction.
           ++ econstructor.
      * auto.
  - (* arrow *) 
    destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.  destruct Hdwl_trans as [θ Hθ]. dependent destruction Hθ. dependent destruction Hθ.
    exists (ld_wl_cons_w Γᵈ (ld_w_sub (ld_t_arrow t2ᵈ t1ᵈ0 ) (ld_t_arrow t1ᵈ t2ᵈ0) )). split.
    + unfold transfer. exists θ'. eapply inst_wl_sub; eauto.
      econstructor; eauto. econstructor; eauto.
    + dependent destruction Hdwl_red.
      dependent destruction Hdwl_red.
      econstructor; auto. 
  - (* -> R *)
    destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.
    destruct Hdwl_trans as [θ Hθ]. 
    dependent destruction Hθ.
    dependent destruction H4.
    dependent destruction H5.
    exists (ld_wl_cons_w Γᵈ
                  (ld_w_sub (ld_t_arrow A0 B0) (ld_t_arrow A1 B1))).
    split; auto.
    unfold transfer. exists θ. econstructor.
    + admit. (* reorder of awl does not change its instantiated dwl *)
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
    exists (ld_wl_cons_w Γᵈ
                (ld_w_sub (ld_t_arrow A0 B0) (ld_t_arrow A1 B1))).
    split; auto.
    unfold transfer. exists θ. econstructor.
    + admit. 
    + constructor; auto.
    + admit.
  - (* EVar L*)
    destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
    unfold transfer in Hdwl_trans.

    destruct Hdwl_trans as [θ Hθ]. 
    (* [t1] <: ^a <: [t2] -> inst t1 <: inst ^a <: inst t2 *)
    (* exists (ld_wl_cons_w dwl  (inst_type ^a t) (inst ^b t)). split.
    exists θ.
    eapply inst_wl_sub.
    econstructor. econstructor. *)
    admit.
  - (* EVar L*)
    admit.


  - destruct IHla_worklist_reducible as [dwl [Hdwl_trans Hdwl_red]].
  destruct Hdwl_trans as [θ Hθ].
  exists dwl.
  (* exists (la_wl_cons_w dwl (w t' ex5)). *)

  (* (wl' [t, ...] <: ^x < [...] ⇝ dwl') ->
      inst θ t <: inst θ ^x  
  *)

    admit. 
  - admit.
Admitted.