Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
Require Import Lia.

Require Import decl.def_ott.
Require Import decl.def_extra.
Require Import decl.prop_subtyping.

Require Import ln_utils.


(* TODO : fix *)
Inductive d_sub_no : denv -> dtyp -> dtyp -> Prop :=    (* defn d_sub_no *)
 | d_subno_top : forall (E:denv) (S1:dtyp),
     dwf_typ E S1 ->
     d_sub_no E S1 dtyp_top
 | d_subno_bot : forall (E:denv) (T1:dtyp),
     dwf_typ E T1 ->
     d_sub_no E dtyp_bot T1
 | d_subno_unit : forall (E:denv),
     d_sub_no E dtyp_unit dtyp_unit
 | d_subno_tvar : forall (E:denv) (X:typvar),
     dwf_typ E (dtyp_var_f X) ->
     d_sub_no E (dtyp_var_f X) (dtyp_var_f X)
 | d_subno_stvar : forall (E:denv) (SX:stypvar),
     dwf_typ E (dtyp_svar SX) ->
     d_sub_no E (dtyp_svar SX) (dtyp_svar SX)
 | d_subno_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp),
     d_sub_no E T1 S1 ->
     d_sub_no E S2 T2 ->
     d_sub_no E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
 | d_subno_all : forall (L:vars) (E:denv) (S1 T1:dtyp),
    ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) ) ) ->
    ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
    ( forall SX , SX \notin L -> d_sub_no  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
    d_sub_no E (dtyp_all S1) (dtyp_all T1)
 | d_subno_alll : forall (L:vars) (E:denv) (S1 T1 T2:dtyp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 ->
      ~ ( T1  = dtyp_top)  ->
      ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S1   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     d_sub_no E  (open_dtyp_wrt_dtyp  S1   T2 )  T1 ->
     d_sub_no E (dtyp_all S1) T1
 | d_subno_intersection1 : forall (E:denv) (S1 T1 T2:dtyp),
     d_sub_no E S1 T1 ->
     d_sub_no E S1 T2 ->
     d_sub_no E S1 (dtyp_intersection T1 T2)
 | d_subno_intersection2 : forall (E:denv) (S1 S2 T1:dtyp),
     dneq_intersection T1 ->
     d_sub_no E S1 T1 ->
     dwf_typ E S2 ->
     d_sub_no E (dtyp_intersection S1 S2) T1
 | d_subno_intersection3 : forall (E:denv) (S1 S2 T1:dtyp),
     dneq_intersection T1 ->
     d_sub_no E S2 T1 ->
     dwf_typ E S1 ->
     d_sub_no E (dtyp_intersection S1 S2) T1
 | d_subno_union1 : forall (E:denv) (S1 T1 T2:dtyp),
     dneq_union S1 ->
     d_sub_no E S1 T1 ->
     dwf_typ E T2 ->
     d_sub_no E S1 (dtyp_union T1 T2)
 | d_subno_union2 : forall (E:denv) (S1 T1 T2:dtyp),
     dneq_union S1 ->
     d_sub_no E S1 T2 ->
     dwf_typ E T1 ->
     d_sub_no E S1 (dtyp_union T1 T2)
 | d_subno_union3 : forall (E:denv) (S1 S2 T1:dtyp),
     d_sub_no E S1 T1 ->
     d_sub_no E S2 T1 ->
     d_sub_no E (dtyp_union S1 S2) T1.

