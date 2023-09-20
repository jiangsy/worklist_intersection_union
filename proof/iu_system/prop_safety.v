Require Import ln_utils.

Require Import decl.def_ott.
Require Import decl.def_extra.
Require Import decl.notations.
Require Import decl.prop_subtyping.

Require Import systemf.def_ott.
Require Import systemf.prop_ln.

Fixpoint trans_typ (T : dtyp) : ftyp :=
    match T with
    | dtyp_unit => ftyp_unit
    | dtyp_top => ftyp_unit
    | dtyp_bot => ftyp_all (ftyp_var_b 0)
    | dtyp_var_b n => ftyp_var_b n
    | dtyp_var_f X => ftyp_var_f X
    | dtyp_svar SX => ftyp_var_f SX
    | dtyp_arrow T1 T2 => ftyp_arrow (trans_typ T1) (trans_typ T2)
    | dtyp_all T => ftyp_all (trans_typ T)
    | dtyp_union T1 T2 => ftyp_sum (trans_typ T1) (trans_typ T2)
    | dtyp_intersection T1 T2 => ftyp_prod (trans_typ T1) (trans_typ T2) 
    end.

Fixpoint trans_env (E : denv) : fenv :=
    match E with
    | nil => nil
    | (X, dbind_tvar_empty) :: E' => (X, bind_tvar_empty) :: trans_env E'
    | (X, dbind_stvar_empty) :: E' => (X, bind_tvar_empty) :: trans_env E'
    | (X, (dbind_typ T)) :: E' => (X, (bind_typ (trans_typ T))) :: trans_env E'
    end.

Inductive sub_elab : denv -> dtyp -> dtyp -> fexp -> Prop :=
 | sub_elab_top : forall (E:denv) (S1:dtyp),
     dwf_env E ->
     dwf_typ E S1 ->
     sub_elab E S1 dtyp_top (fexp_abs (trans_typ S1) fexp_unit)
 | sub_elab_bot : forall (E:denv) (T1:dtyp),
     dwf_env E ->
     dwf_typ E T1 ->
     sub_elab E dtyp_bot T1 (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_tapp (fexp_var_b 0) (trans_typ T1)))
 | sub_elab_unit : forall (E:denv),
     dwf_env E ->
     sub_elab E dtyp_unit dtyp_unit (fexp_abs ftyp_unit (fexp_var_b 0))
 | sub_elab_tvar : forall (E:denv) (X:typvar),
     dwf_env E ->
     dwf_typ E (dtyp_var_f X) ->
     sub_elab E (dtyp_var_f X) (dtyp_var_f X) (fexp_abs (ftyp_var_f X) (fexp_var_b 0))
 | sub_elab_stvar : forall (E:denv) (SX:stypvar),
     dwf_env E ->
     dwf_typ E (dtyp_svar SX) ->
     sub_elab E (dtyp_svar SX) (dtyp_svar SX) (fexp_abs (ftyp_var_f SX) (fexp_var_b 0))
 | sub_elab_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp) (C1 C2:fexp),
     sub_elab E T1 S1 C1 ->
     sub_elab E S2 T2 C2 ->
     sub_elab E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
        (fexp_abs (ftyp_arrow (trans_typ T1) (trans_typ T2))
                  (fexp_abs (trans_typ T1)
                            (fexp_app C2
                                      (fexp_app (fexp_var_b 0)
                                                (fexp_app C1 (fexp_var_b 1))))))
 | sub_elab_all : forall (L:vars) (E:denv) (S1 T1:dtyp) (C:fexp),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> sub_elab  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) C ) ->
     sub_elab E (dtyp_all S1) (dtyp_all T1)
        (fexp_abs (trans_typ (dtyp_all T1)) (fexp_tabs (fexp_app C (fexp_tapp (fexp_var_b 0) (ftyp_var_b 1)))))
 | sub_elab_alll : forall (L:vars) (E:denv) (S1 T1 T2:dtyp) (C:fexp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 -> 
     ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S1   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     sub_elab E  (open_dtyp_wrt_dtyp  S1   T2 )  T1 C ->
     sub_elab E (dtyp_all S1) T1
        (fexp_abs (trans_typ (dtyp_all T1)) (fexp_app C (fexp_tapp (fexp_var_b 0) (trans_typ T2))))
 | sub_elab_intersection1 : forall (E:denv) (S1 T1 T2:dtyp) (C1 C2:fexp),
     sub_elab E S1 T1 C1 ->
     sub_elab E S1 T2 C2 ->
     sub_elab E S1 (dtyp_intersection T1 T2)
        (fexp_abs (trans_typ S1)
                  (fexp_pair (fexp_app C1 (fexp_var_b 0))
                             (fexp_app C2 (fexp_var_b 0))))
 | sub_elab_intersection2 : forall (E:denv) (S1 S2 T1:dtyp) (C:fexp),
     sub_elab E S1 T1 C ->
     dwf_typ E S2 ->
     sub_elab E (dtyp_intersection S1 S2) T1
        (fexp_abs (trans_typ (dtyp_intersection S1 S2)) (fexp_app C (fexp_proj1 (fexp_var_b 0))))
 | sub_elab_intersection3 : forall (E:denv) (S1 S2 T1:dtyp) (C:fexp),
     sub_elab E S2 T1 C ->
     dwf_typ E S1 ->
     sub_elab E (dtyp_intersection S1 S2) T1
        (fexp_abs (trans_typ (dtyp_intersection S1 S2)) (fexp_app C (fexp_proj2 (fexp_var_b 0))))
 | sub_elab_union1 : forall (E:denv) (S1 T1 T2:dtyp) (C:fexp),
     sub_elab E S1 T1 C ->
     dwf_typ E T2 ->
     sub_elab E S1 (dtyp_union T1 T2)
        (fexp_abs (trans_typ S1) (fexp_inl (fexp_app C (fexp_var_b 0))))
 | sub_elab_union2 : forall (E:denv) (S1 T1 T2:dtyp) (C:fexp),
     sub_elab E S1 T2 C ->
     dwf_typ E T1 ->
     sub_elab E S1 (dtyp_union T1 T2)
        (fexp_abs (trans_typ S1) (fexp_inr (fexp_app C (fexp_var_b 0))))
 | sub_elab_union3 : forall (E:denv) (S1 S2 T1:dtyp) (C1 C2:fexp),
     sub_elab E S1 T1 C1 ->
     sub_elab E S2 T1 C2 ->
     sub_elab E (dtyp_union S1 S2) T1
     (fexp_abs (trans_typ (dtyp_union S1 S2)) (fexp_case (fexp_var_b 0) (fexp_app C1 (fexp_var_b 0)) (fexp_app C2 (fexp_var_b 0)))).

Create HintDb safety.
Hint Constructors sub_elab : safety.
Hint Constructors typing : safety.

Theorem sub_elab_sound: forall E A B C,
    sub_elab E A B C -> d_sub E A B.
Proof.
    intros. induction H; eauto.
Qed.

Theorem sub_elab_complete: forall E A B,
    d_sub E A B -> exists C, sub_elab E A B C.
Proof.
    intros. induction H.
    - eauto with safety.
    - eauto with safety.
    - eauto with safety.
    - eauto with safety.
    - eauto with safety.
    - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
    - inst_cofinites_by L. inversion H2. eauto with safety.
      exists (fexp_abs (trans_typ (dtyp_all T1)) (fexp_tabs (fexp_app x0 (fexp_tapp (fexp_var_b 0) (ftyp_var_b 1))))).
      apply sub_elab_all with (L := L).
      + intros. admit.
      + intros. admit.
      + intros. admit.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub. eauto with safety.
    - inversion IHd_sub1. inversion IHd_sub2. eauto with safety.
Admitted.

Theorem sub_sound_f : forall E A B C,
    sub_elab E A B C -> typing (trans_env E) C (ftyp_arrow (trans_typ A) (trans_typ B)).
Proof.
    intros. induction H; simpl; eauto with safety.
Admitted.
