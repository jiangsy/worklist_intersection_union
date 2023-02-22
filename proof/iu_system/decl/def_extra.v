Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import decl.def_ott.


Fixpoint ftv_sin_dtyp (T:dtyp) : vars :=
  match T with
  | dtyp_unit => {}
  | dtyp_top => {}
  | dtyp_bot => {}
  | (dtyp_var_b nat) => {}
  | (dtyp_var_f X) => {{X}}
  | (dtyp_svar SX) => {}
  | (dtyp_arrow T1 T2) => (ftv_sin_dtyp T1) \u (ftv_sin_dtyp T2)
  | (dtyp_all T) => (ftv_sin_dtyp T)
  | (dtyp_union T1 T2) => AtomSetImpl.inter (ftv_sin_dtyp T1) (ftv_sin_dtyp T2)
  | (dtyp_intersection T1 T2) => AtomSetImpl.inter (ftv_sin_dtyp T1) (ftv_sin_dtyp T2)
end.

Fixpoint fstv_sin_dtyp (T:dtyp) : vars :=
  match T with
  | dtyp_unit => {}
  | dtyp_top => {}
  | dtyp_bot => {}
  | (dtyp_var_b nat) => {}
  | (dtyp_var_f X) => {}
  | (dtyp_svar SX) => {{SX}}
  | (dtyp_arrow T1 T2) => (fstv_sin_dtyp T1) \u (fstv_sin_dtyp T2)
  | (dtyp_all T1) => (fstv_sin_dtyp T1)
  | (dtyp_union T1 T2) =>  AtomSetImpl.inter (fstv_sin_dtyp T1)  (fstv_sin_dtyp T2)
  | (dtyp_intersection T1 T2) => AtomSetImpl.inter (fstv_sin_dtyp T1) (fstv_sin_dtyp T2)
end.

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

Inductive dsub : denv -> dtyp -> dtyp -> Prop :=    (* defn dsub *)
 | dsub_top : forall (E:denv) (S:dtyp),
     dwf_typ E S ->
     dsub E S dtyp_top
 | dsub_bot : forall (E:denv) (T:dtyp),
     dwf_typ E T ->
     dsub E dtyp_bot T
 | dsub_unit : forall (E:denv),
     dsub E dtyp_unit dtyp_unit
 | dsub_tvar : forall (E:denv) (X:typvar),
     dwf_typ E (dtyp_var_f X) ->
     dsub E (dtyp_var_f X) (dtyp_var_f X)
 | dsub_stvar : forall (E:denv) (SX:stypvar),
     dwf_typ E (dtyp_svar SX) ->
     dsub E (dtyp_svar SX) (dtyp_svar SX)
 | dsub_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp),
     dsub E T1 S1 ->
     dsub E S2 T2 ->
     dsub E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
 | dsub_all : forall (L:vars) (E:denv) (S T:dtyp),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> dsub  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
     dsub E (dtyp_all S) (dtyp_all T)
 | dsub_alll : forall (L:vars) (E:denv) (S T1 T2:dtyp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 -> 
     ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     dsub E  (open_dtyp_wrt_dtyp  S   T2 )  T1 ->
     dsub E (dtyp_all S) T1
 | dsub_intersection1 : forall (E:denv) (S T1 T2:dtyp),
     dsub E S T1 ->
     dsub E S T2 ->
     dsub E S (dtyp_intersection T1 T2)
 | dsub_intersection2 : forall (E:denv) (S1 S2 T:dtyp),
     dsub E S1 T ->
     dwf_typ E S2 ->
     dsub E (dtyp_intersection S1 S2) T
 | dsub_intersection3 : forall (E:denv) (S1 S2 T:dtyp),
     dsub E S2 T ->
     dwf_typ E S1 ->
     dsub E (dtyp_intersection S1 S2) T
 | dsub_union1 : forall (E:denv) (S T1 T2:dtyp),
     dsub E S T1 ->
     dwf_typ E T2 ->
     dsub E S (dtyp_union T1 T2)
 | dsub_union2 : forall (E:denv) (S T1 T2:dtyp),
     dsub E S T2 ->
     dwf_typ E T1 ->
     dsub E S (dtyp_union T1 T2)
 | dsub_union3 : forall (E:denv) (S1 S2 T:dtyp),
     dsub E S1 T ->
     dsub E S2 T ->
     dsub E (dtyp_union S1 S2) T.

Inductive dtyping_mode :=
    | dtypingmode_inf 
    | dtypingmode_chk
    | dtypingmode_infapp (t : dtyp).

Definition dsubst_tv_in_dtypingmode (T1:dtyp) (X:typvar) (m:dtyping_mode):=
    match m with 
    | dtypingmode_chk => dtypingmode_chk
    | dtypingmode_inf => dtypingmode_inf
    | dtypingmode_infapp T2 => dtypingmode_infapp (dsubst_tv_in_dtyp T1 X T2)
    end.

Inductive dtyping : denv -> dexp -> dtyping_mode -> dtyp -> Prop :=
| dtyping_infvar : forall (E:denv) (x:expvar) (T:dtyp),
    dwf_env E ->
    binds ( x )  ( (dbind_typ T) ) ( E )  ->
    dtyping E (dexp_var_f x) dtypingmode_inf T
| dtyping_infanno : forall (E:denv) (e:dexp) (T:dtyp),
    dwf_typ E T ->
    dtyping E e dtypingmode_chk T ->
    dtyping E  ( (dexp_anno e T) )  dtypingmode_inf T
| dtypinginf_unit : forall (E:denv),
    dwf_env E ->
    dtyping E dexp_unit dtypingmode_inf dtyp_unit
| dtyping_infapp : forall (E:denv) (e1 e2:dexp) (T1 T2:dtyp),
    dtyping E e1 dtypingmode_inf T2 ->
    dtyping E e2 (dtypingmode_infapp T2) T1 ->
    dtyping E  ( (dexp_app e1 e2) ) dtypingmode_inf T1
| dtyping_inftabs : forall (L:vars) (E:denv) (e:dexp) (T:dtyp),
dwf_typ E (dtyp_all T) ->
    ( forall X , X \notin  L  -> dtyping  ( X ~ dbind_tvar_empty  ++  E ) (dexp_anno  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )  ( open_dtyp_wrt_dtyp T (dtyp_var_f X) ) ) dtypingmode_chk ( open_dtyp_wrt_dtyp T (dtyp_var_f X) )  )  ->
    dtyping E (dexp_tabs (dbody_anno e T)) dtypingmode_inf (dtyp_all T)
| dtyping_inftappbot : forall (E:denv) (e:dexp) (T:dtyp),
    dwf_typ E T ->
    dtyping E e dtypingmode_inf dtyp_bot ->
    dtyping E (dexp_tapp e T) dtypingmode_inf dtyp_bot
| dtyping_inftappall : forall (E:denv) (e1:dexp) (T2 T1:dtyp),
    dwf_typ E T2 ->
    dtyping E e1 dtypingmode_inf (dtyp_all T1) ->
    dtyping E (dexp_tapp e1 T2) dtypingmode_inf (open_dtyp_wrt_dtyp  T1 T2 ) 
| dtyping_chkabstop : forall (L:vars) (E:denv) (e:dexp),
    ( forall x , x \notin  L  -> dtyping  ( x ~ (dbind_typ dtyp_bot)  ++  E )   ( open_dexp_wrt_dexp e (dexp_var_f x) ) dtypingmode_chk dtyp_top )  ->
    dtyping E (dexp_abs e) dtypingmode_chk dtyp_top
| dtyping_chkabs : forall (L:vars) (E:denv) (e:dexp) (T1 T2:dtyp),
    dwf_typ E T1 ->
    ( forall x , x \notin  L  -> dtyping  ( x ~ (dbind_typ T1)  ++  E )  ( open_dexp_wrt_dexp e (dexp_var_f x) ) dtypingmode_chk T2 )  ->
    dtyping E (dexp_abs e) dtypingmode_chk (dtyp_arrow T1 T2)
| dtyping_chkall : forall (L:vars) (E:denv) (e:dexp) (T:dtyp),
    dwf_typ E (dtyp_all T) ->
    ( forall X , X \notin  L  -> dtyping  ( X ~ dbind_tvar_empty  ++  E )  e  dtypingmode_chk ( open_dtyp_wrt_dtyp T (dtyp_var_f X) )  )  ->
    dtyping E e dtypingmode_chk (dtyp_all T)
| dtyping_chksub : forall (E:denv) (e:dexp) (T S:dtyp),
    dtyping E e dtypingmode_inf S ->
    dsub E S T ->
    dtyping E e dtypingmode_chk T
| dtyping_chkintersection : forall (E:denv) (e:dexp) (S T:dtyp),
    dtyping E e dtypingmode_chk S ->
    dtyping E e dtypingmode_chk T ->
    dtyping E e dtypingmode_chk (dtyp_intersection S T)
| dtyping_chkunion1 : forall (E:denv) (e:dexp) (S T:dtyp),
    dtyping E e dtypingmode_chk S ->
    dwf_typ E T ->
    dtyping E e dtypingmode_chk (dtyp_union S T)
| dtyping_chkunion2 : forall (E:denv) (e:dexp) (S T:dtyp),
    dtyping E e dtypingmode_chk T ->
    dwf_typ E S ->
    dtyping E e dtypingmode_chk (dtyp_union S T)
| dtyping_infapparrow : forall (E:denv) (T1 T2:dtyp) (e:dexp),
    dwf_typ E T2 ->
    dtyping E e dtypingmode_chk T1 ->
    dtyping E e ( dtypingmode_infapp ( (dtyp_arrow T1 T2) ) ) T2
| dtyping_infappall : forall (E:denv) (T1:dtyp) (e:dexp) (T2 T3:dtyp),
    dmono_typ T3 ->
    dwf_typ E T3 ->
    dwf_typ E (dtyp_all T1) ->
    dtyping E e ( dtypingmode_infapp (open_dtyp_wrt_dtyp  T1   T3 ) )T2 ->
    dtyping E e ( dtypingmode_infapp ( (dtyp_all T1) ) ) T2
| dtyping_infappbot : forall (E:denv) (e:dexp),
    dtyping E e dtypingmode_chk dtyp_top ->
    dtyping E e ( dtypingmode_infapp dtyp_bot ) dtyp_bot
| dtyping_infappintersection1 : forall (E:denv) (e:dexp) (S1 S2 T:dtyp),
    dtyping E e ( dtypingmode_infapp S1 ) T ->
    dtyping E e ( dtypingmode_infapp (dtyp_intersection S1 S2) ) T
| dtyping_infappintersection2 : forall (E:denv) (e:dexp) (S1 S2 T:dtyp),
    dtyping E e ( dtypingmode_infapp S2 ) T ->
    dtyping E e ( dtypingmode_infapp (dtyp_intersection S1 S2) ) T 
| dtyping_infappunion : forall (E:denv) (e:dexp) (S1 S2 T:dtyp),
    dtyping E e ( dtypingmode_infapp S1 ) T ->
    dtyping E e ( dtypingmode_infapp S2 ) T ->
    dtyping E e ( dtypingmode_infapp (dtyp_union S1 S2) ) T
    .


