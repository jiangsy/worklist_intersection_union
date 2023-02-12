Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import decl.ott.

(* defns Jdwf_typ_s *)
Inductive dwf_typ_s : denv -> dtyp -> Prop :=    (* defn dwf_typ_s *)
 | dwftyps_unit : forall (E:denv),
     dwf_typ_s E dtyp_unit
 | dwftyps_bot : forall (E:denv),
     dwf_typ_s E dtyp_bot
 | dwftyps_top : forall (E:denv),
     dwf_typ_s E dtyp_top
 | dwftyps_var : forall (E:denv) (X:typvar),
      binds ( X )  ( dbind_tvar_empty ) ( E )  ->
     dwf_typ_s E (dtyp_var_f X)
 | dwftyps_stvar : forall (E:denv) (SX:stypvar),
      binds ( SX ) ( dbind_stvar_empty ) ( E )  ->
     dwf_typ_s E (dtyp_svar SX)
 | dwftyps_arrow : forall (E:denv) (T1 T2:dtyp),
     dwf_typ_s E T1 ->
     dwf_typ_s E T2 ->
     dwf_typ_s E (dtyp_arrow T1 T2)
 | dwftyps_all : forall (L:vars) (E:denv) (T:dtyp),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> dwf_typ_s  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
     dwf_typ_s E (dtyp_all T)
 | dwftyps_union : forall (E:denv) (T1 T2:dtyp),
     dwf_typ_s E T1 ->
     dwf_typ_s E T2 ->
     dwf_typ_s E (dtyp_union T1 T2)
 | dwftyps_intersection : forall (E:denv) (T1 T2:dtyp),
     dwf_typ_s E T1 ->
     dwf_typ_s E T2 ->
     dwf_typ_s E (dtyp_intersection T1 T2).

Inductive desub : denv -> denv -> Prop := 
| desub_empty: desub nil nil  
| desub_tvar : forall E1 E2 X, 
    desub E1 E2 -> 
    desub (X ~ dbind_tvar_empty  ++  E1) 
        (X ~ dbind_tvar_empty  ++  E2)
| desub_stvar : forall E1 E2 SX, 
    desub E1 E2 -> 
    desub (SX ~ dbind_stvar_empty  ++  E1) 
        (SX ~ dbind_stvar_empty  ++  E2)
| desub_var : forall E1 E2 x S T,
    desub E1 E2 ->
    dsub E2 S T ->
    desub (x ~ dbind_typ S ++ E1) 
        (x ~ dbind_typ T ++ E2)        
.
   