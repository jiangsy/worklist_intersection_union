Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
Require Import Lia.

Require Import decl.def_ott.
Require Import decl.def_extra.
Require Import decl.prop_basic.
Require Import decl.nonoverlapping.def.
Require Import decl.prop_subtyping.

Require Import ln_utils.

Hint Constructors d_sub : nonoverlapping.
Hint Constructors d_sub_no : nonoverlapping.

Theorem d_sub_no_sound_wrt_d_sub : forall E S1 T1,
    d_sub_no E S1 T1 -> d_sub E S1 T1.
Proof with auto with nonoverlapping.
    intros; induction H; eauto...
Qed.

Fixpoint d_typ_size (T : dtyp) : nat :=
    match T with 
    | dtyp_arrow T1 T2 => ( d_typ_size T1 + d_typ_size T2 )
    | dtyp_intersection T1 T2 => S ( d_typ_size T1 + d_typ_size T2 )
    | dtyp_union T1 T2 => S ( d_typ_size T1 + d_typ_size T2 )
    | dtyp_all T1 => S ( d_typ_size T1 ) 
    | _ => 0
    end.

Fixpoint d_typ_order (T : dtyp) : nat :=
    match T with 
    | dtyp_arrow T1 T2 => ( d_typ_order T1 + d_typ_order T2 )
    | dtyp_intersection T1 T2 => ( d_typ_order T1 + d_typ_order T2 )
    | dtyp_union T1 T2 => ( d_typ_order T1 + d_typ_order T2 )
    | dtyp_all T1 => S ( d_typ_order T1 ) 
    | _ => 0
    end.

(* Inductive is_intersection_l : dtyp -> Prop :=
  | is_intersection_rec_unit : forall T, is_intersection_l (dtyp_intersection dtyp_unit T)
  | is_intersection_rec_top : forall T, is_intersection_l (dtyp_intersection dtyp_top T)
  | is_intersection_rec_bot : forall T, is_intersection_l (dtyp_intersection dtyp_bot T)
  | is_intersection_rec_arrow : forall T T1 T2, is_intersection_l (dtyp_intersection (dtyp_arrow T1 T2) T)
  | is_intersection_rec_all : forall T1 T, is_intersection_l (dtyp_intersection (dtyp_all T1) T)
  | is_intersection_rec_tvar : forall X T, is_intersection_l (dtyp_intersection (dtyp_var_f X) T)
  | is_intersection_rec_stvar : forall SX T, is_intersection_l (dtyp_intersection (dtyp_svar SX) T)
  | is_intersection_rec_union : forall T T1 T2, is_intersection_l (dtyp_intersection (dtyp_union T1 T2) T)
  | is_intersection_rec_inter : forall T T1, is_intersection_l T1 -> is_intersection_l (dtyp_intersection T1 T)
  .

Inductive is_intersection_rec : dtyp -> Prop :=
  | is_intersection_rec_both : forall T1 T2,
      dneq_intersection T1 ->
      dneq_intersection T2 ->
      is_intersection_rec (dtyp_intersection T1 T2)
  | is_intersection_rec_l : forall T1 T2,
      is_intersection_rec T1 -> 
      is_intersection_rec (dtyp_intersection T1 T2)
  | is_intersection_rec_r : forall T1 T2,
      is_intersection_rec T2 -> 
      is_intersection_rec (dtyp_intersection T1 T2)
  . *)

Inductive is_intersection_rec : dtyp -> Prop :=
  | is_intersection_rec_nb : forall T1 T2,
      dneq_intersection T1 ->
      dneq_intersection T2 ->
      is_intersection_rec (dtyp_intersection T1 T2)
  | is_intersection_rec_l : forall T1 T2,
      dneq_intersection T2 ->
      is_intersection_rec T1 -> 
      is_intersection_rec (dtyp_intersection T1 T2)
  | is_intersection_rec_r : forall T1 T2,
      dneq_intersection T1 -> 
      is_intersection_rec T2 -> 
      is_intersection_rec (dtyp_intersection T1 T2)
  | is_intersection_rec_b : forall T1 T2,
      is_intersection_rec T1 -> 
      is_intersection_rec T2 -> 
      is_intersection_rec (dtyp_intersection T1 T2)
  .


Inductive is_union_rec : dtyp -> Prop :=
  | is_union_rec_nb : forall T1 T2,
      dneq_union T1 ->
      dneq_union T2 ->
      is_union_rec (dtyp_union T1 T2)
  | is_union_rec_l : forall T1 T2,
      dneq_union T2 ->
      is_union_rec T1 -> 
      is_union_rec (dtyp_union T1 T2)
  | is_union_rec_r : forall T1 T2,
      dneq_union T1 -> 
      is_union_rec T2 -> 
      is_union_rec (dtyp_union T1 T2)
  | is_union_rec_b : forall T1 T2,
      is_union_rec T1 -> 
      is_union_rec T2 -> 
      is_union_rec (dtyp_union T1 T2)
  .

Inductive is_union_inter_rec : dtyp -> Prop :=
  | is_union_rec_nb_u : forall T1 T2,
      ( dneq_union T1 /\ dneq_intersection T1) ->
      ( dneq_union T2 /\ dneq_intersection T2) ->
      is_union_inter_rec (dtyp_union T1 T2)
  | is_union_rec_nb_i : forall T1 T2,
      ( dneq_union T1 /\ dneq_intersection T1) ->
      ( dneq_union T2 /\ dneq_intersection T2) ->
      is_union_inter_rec (dtyp_intersection T1 T2)
  | is_union_rec_l_u : forall T1 T2,
      ( dneq_union T2 /\ dneq_intersection T2) ->
      is_union_inter_rec T1 -> 
      is_union_inter_rec (dtyp_union T1 T2)
  | is_union_rec_l_i : forall T1 T2,
      ( dneq_union T2 /\ dneq_intersection T2) ->
      is_union_inter_rec T1 -> 
      is_union_inter_rec (dtyp_intersection T1 T2)
  | is_union_rec_r_u : forall T1 T2,
      ( dneq_union T1 /\ dneq_intersection T1)  -> 
      is_union_inter_rec T2 -> 
      is_union_inter_rec (dtyp_union T1 T2)
  | is_union_rec_r_i : forall T1 T2,
      ( dneq_union T1 /\ dneq_intersection T1)  -> 
      is_union_inter_rec T2 -> 
      is_union_inter_rec (dtyp_intersection T1 T2)
  | is_union_rec_b_u : forall T1 T2,
      is_union_inter_rec T1 -> 
      is_union_inter_rec T2 -> 
      is_union_inter_rec (dtyp_union T1 T2)
  | is_union_rec_b_i : forall T1 T2,
      is_union_inter_rec T1 -> 
      is_union_inter_rec T2 -> 
      is_union_inter_rec (dtyp_intersection T1 T2)
  .

Hint Constructors dneq_intersection : core.
Hint Constructors is_intersection_rec : core.

Theorem intersection_is_intersection_rec' : forall n T1 T2,
  d_typ_size T1 + d_typ_size T2 < n ->
  lc_dtyp T1 -> lc_dtyp T2 ->
  is_intersection_rec (dtyp_intersection T1 T2).
Proof.
  intro n. induction n; intros.
  - inversion H.
  - induction H0; induction H1; auto; simpl in H.
    + simpl in *.
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *.
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *.
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_r; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_l; auto. apply IHn; auto. lia.
    + simpl in *. 
      apply is_intersection_rec_b; auto.
      apply IHn; auto. lia.
      apply IHn; auto. lia.
Qed.

Theorem intersection_is_intersection_rec : forall T1 T2,
  lc_dtyp T1 -> lc_dtyp T2 -> is_intersection_rec (dtyp_intersection T1 T2).
Proof.
  intros. eapply intersection_is_intersection_rec'; eauto.
Qed. 

Theorem intersection_rec'_is_intersection : forall T,
  is_intersection_rec T -> exists T1 T2, T = dtyp_intersection T1 T2.
Proof.
  intros. induction H; eauto.
Qed.

Theorem not_intersection_rec_neq_intersection : forall T,
  lc_dtyp T -> ~ is_intersection_rec T -> dneq_intersection T.
Proof.
  intros. induction H; eauto.
  exfalso. apply H0.
  apply intersection_is_intersection_rec; auto. 
Qed.

Theorem d_neq_intersection_dec : forall T,
    lc_dtyp T -> dneq_intersection T \/ ~ (dneq_intersection T).
Proof.
    intros. induction H; auto.
    right. unfold not. intros.
    inversion H1.
Qed.

Theorem is_intersection_rec_dec : forall T,
    lc_dtyp T -> is_intersection_rec T \/ ~ (is_intersection_rec T).
Proof.
    intros. specialize (d_neq_intersection_dec T H); intro.
    inversion H0.
    - right. unfold not. intros. apply intersection_rec'_is_intersection in H2.
      destruct H2 as [T1 [T2]]. rewrite H2 in *; inversion H1.
    - left. destruct T; try solve [inversion H; exfalso; apply H1; auto].
        + inversion H. apply intersection_is_intersection_rec; auto. 
Qed.

Hint Resolve dwf_typ_dlc_type : core.
Hint Resolve d_sub_dwft : core.
Hint Resolve is_intersection_rec_dec : nonoverlapping.


(* Theorem d_sub_no_complete_wrt_d_sub : forall n E S1 T1,
    d_typ_order S1 + d_typ_order T1 < n ->
    d_sub E S1 T1 -> d_sub_no E S1 T1.
Proof with auto with nonoverlapping.   
  intro n. induction n; intros E S1 T1 Hord Hsub. 
  - inversion Hord.
  - dependent induction Hsub; simpl in Hord; eauto...
    + econstructor.
      apply IHHsub1; lia.
      apply IHHsub2; lia.
    + eapply d_subno_all with (L:=L); intros SX Hfr; inst_cofinites_with SX; auto...
      apply IHn. admit. auto.
    (* ∀ X . S < T *)
    + clear IHHsub.
      assert (is_union_inter_rec T1 \/ ~ (is_union_inter_rec T1)) by admit.
      inversion H5.
      * induction H6; auto; simpl in Hord.
        -- inversion H1.
        -- inversion H0.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- 
      
      * apply d_subno_alll with (L:=L) (T2:=T2); auto. admit.
        apply IHn. admit. auto.
    + econstructor.
      apply IHHsub1; lia.
      apply IHHsub2; lia.
    + clear IHHsub. 
      assert (is_intersection_rec T \/ ~ (is_intersection_rec T)). {
        apply is_intersection_rec_dec. eapply dwf_typ_dlc_type. eapply d_sub_dwft; eauto.
      }
      inversion H0.
      induction H1; auto; simpl in Hord; specialize (d_sub_intersection_inversion _ _ _ _ Hsub); intro Hintsub; destruct Hintsub.
      * apply d_subno_intersection1; apply d_subno_intersection2; auto.
        apply IHn. lia. auto.  apply IHn. lia. auto.
      * apply d_subno_intersection1; eauto...
        apply IHis_intersection_rec; auto. lia.
        apply d_subno_intersection2; auto. apply IHn. lia. auto.
      * apply d_subno_intersection1; auto...
        apply d_subno_intersection2; auto. apply IHn. lia. auto.
        apply IHis_intersection_rec; auto. lia.
      * apply d_subno_intersection1; auto...
        apply IHis_intersection_rec1; auto. lia.
        apply IHis_intersection_rec2; auto. lia.
      * apply d_subno_intersection2; eauto.
        apply not_intersection_rec_neq_intersection; eauto.
        eapply dwf_typ_dlc_type; eapply d_sub_dwft; eauto.
        apply IHn; auto. lia.
    (*  *)
    + clear IHHsub. 
      assert (is_intersection_rec T \/ ~ (is_intersection_rec T)). {
        apply is_intersection_rec_dec. eapply dwf_typ_dlc_type. eapply d_sub_dwft; eauto.
      }
      inversion H0.
      induction H1; auto; simpl in Hord; specialize (d_sub_intersection_inversion _ _ _ _ Hsub); intro Hintsub; destruct Hintsub.
      * apply d_subno_intersection1; apply d_subno_intersection3; auto.
        apply IHn. lia. auto.  apply IHn. lia. auto.
      * apply d_subno_intersection1; eauto...
        apply IHis_intersection_rec; auto. lia.
        apply d_subno_intersection3; auto. apply IHn. lia. auto.
      * apply d_subno_intersection1; auto...
        apply d_subno_intersection3; auto. apply IHn. lia. auto.
        apply IHis_intersection_rec; auto. lia.
      * apply d_subno_intersection1; auto...
        apply IHis_intersection_rec1; auto. lia.
        apply IHis_intersection_rec2; auto. lia.
      * apply d_subno_intersection3; eauto.
        apply not_intersection_rec_neq_intersection; eauto.
        eapply dwf_typ_dlc_type; eapply d_sub_dwft; eauto.
        apply IHn; auto. lia.
    + admit.
    + admit.
Admitted. *)