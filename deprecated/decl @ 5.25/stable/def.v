Require Import decl.def_ott.


(* defns Jdsub_stable *)
Inductive dsub_stable : denv -> dtyp -> dtyp -> Prop :=    (* defn dsub_stable *)
 | dsubstable_top : forall (E:denv) (S1:dtyp),
     dwf_typ E S1 ->
     dsub_stable E S1 dtyp_top
 | dsubstable_bot : forall (E:denv) (T1:dtyp),
     dwf_typ E T1 ->
     dsub_stable E dtyp_bot T1
 | dsubstable_refl : forall (E:denv) (T1:dtyp),
     dwf_typ E T1 ->
     dsub_stable E T1 T1
 | dsubstable_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp),
     dsub_stable E T1 S1 ->
     dsub_stable E S2 T2 ->
     dsub_stable E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
 | dsubstable_all : forall (E:denv) (S1 T1 U1:dtyp),
     dwf_typ E U1 ->
     dsub_stable E  (open_dtyp_wrt_dtyp  S1   U1 )   (open_dtyp_wrt_dtyp  T1   U1 )  ->
     dsub_stable E (dtyp_all S1) (dtyp_all T1)
 | dsubstable_alll : forall (E:denv) (S1 T1 U1:dtyp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 ->
     dwf_typ E U1 ->
     dmono_typ U1 ->
     dsub_stable E  (open_dtyp_wrt_dtyp  S1   U1 )  T1 ->
     dsub_stable E (dtyp_all S1) T1
 | dsubstable_intersection1 : forall (E:denv) (S1 T1 T2:dtyp),
     dsub_stable E S1 T1 ->
     dsub_stable E S1 T2 ->
     dsub_stable E S1 (dtyp_intersection T1 T2)
 | dsubstable_intersection2 : forall (E:denv) (S1 S2 T1:dtyp),
     dsub_stable E S1 T1 ->
     dwf_typ E S2 ->
     dsub_stable E (dtyp_intersection S1 S2) T1
 | dsubstable_intersection3 : forall (E:denv) (S1 S2 T1:dtyp),
     dsub_stable E S2 T1 ->
     dwf_typ E S1 ->
     dsub_stable E (dtyp_intersection S1 S2) T1
 | dsubstable_union1 : forall (E:denv) (S1 T1 T2:dtyp),
     dsub_stable E S1 T1 ->
     dwf_typ E T2 ->
     dsub_stable E S1 (dtyp_union T1 T2)
 | dsubstable_union2 : forall (E:denv) (S1 T1 T2:dtyp),
     dsub_stable E S1 T2 ->
     dwf_typ E T1 ->
     dsub_stable E S1 (dtyp_union T1 T2)
 | dsubstable_union3 : forall (E:denv) (S1 S2 T1:dtyp),
     dsub_stable E S1 T1 ->
     dsub_stable E S2 T1 ->
     dsub_stable E (dtyp_union S1 S2) T1.
