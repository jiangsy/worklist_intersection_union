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


(* a non-overlapping version is not needed? *)
(* defns Jdsub_nonoverlap *)
(* Inductive dsub_no : denv -> dtyp -> dtyp -> Prop :=    (* defn dsub_no *)
 | dsubno_top : forall (E:denv) (S:dtyp),
     dwf_typ E S ->
     dsub_no E S dtyp_top
 | dsubno_bot : forall (E:denv) (T:dtyp),
     dwf_typ E T ->
     dsub_no E dtyp_bot T
 | dsubno_unit : forall (E:denv),
     dsub_no E dtyp_unit dtyp_unit
 | dsubno_tvar : forall (E:denv) (X:typvar),
     dwf_typ E (dtyp_var_f X) ->
     dsub_no E (dtyp_var_f X) (dtyp_var_f X)
 | dsubno_stvar : forall (E:denv) (SX:stypvar),
     dwf_typ E (dtyp_svar SX) ->
     dsub_no E (dtyp_svar SX) (dtyp_svar SX)
 | dsubno_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp),
     dsub_no E T1 S1 ->
     dsub_no E S2 T2 ->
     dsub_no E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
 | dsubno_all : forall (L:vars) (E:denv) (S T:dtyp),
    ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S   (dtyp_svar SX) ) ) ->
    ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
    ( forall SX , SX \notin L -> dsub_no  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T   (dtyp_svar SX) ) ) ->
    dsub_no E (dtyp_all S) (dtyp_all T)
 | dsubno_alll : forall (L:vars) (E:denv) (S T1 T2:dtyp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 ->
      ~ ( T1  = dtyp_top)  ->
      ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     dsub_no E  (open_dtyp_wrt_dtyp  S   T2 )  T1 ->
     dsub_no E (dtyp_all S) T1
 | dsubno_intersection1 : forall (E:denv) (S T1 T2:dtyp),
     dsub_no E S T1 ->
     dsub_no E S T2 ->
     dsub_no E S (dtyp_intersection T1 T2)
 | dsubno_intersection2 : forall (E:denv) (S1 S2 T:dtyp),
     dneq_intersection T ->
     dsub_no E S1 T ->
     dwf_typ E S2 ->
     dsub_no E (dtyp_intersection S1 S2) T
 | dsubno_intersection3 : forall (E:denv) (S1 S2 T:dtyp),
     dneq_intersection T ->
     dsub_no E S2 T ->
     dwf_typ E S1 ->
     dsub_no E (dtyp_intersection S1 S2) T
 | dsubno_union1 : forall (E:denv) (S T1 T2:dtyp),
     dneq_union S ->
     dsub_no E S T1 ->
     dwf_typ E T2 ->
     dsub_no E S (dtyp_union T1 T2)
 | dsubno_union2 : forall (E:denv) (S T1 T2:dtyp),
     dneq_union S ->
     dsub_no E S T2 ->
     dwf_typ E T1 ->
     dsub_no E S (dtyp_union T1 T2)
 | dsubno_union3 : forall (E:denv) (S1 S2 T:dtyp),
     dsub_no E S1 T ->
     dsub_no E S2 T ->
     dsub_no E (dtyp_union S1 S2) T. *)


(* defns Jdtyping *)
(* Inductive dinf : denv -> dexp -> dtyp -> Prop :=    (* defn dinf *)
 | dinf_var : forall (E:denv) (x:expvar) (T:dtyp),
     dwf_env E ->
      binds ( x )  ( (dbind_typ T) ) ( E )  ->
     dinf E (dexp_var_f x) T
 | dinf_anno : forall (E:denv) (e:dexp) (T:dtyp),
     dwf_typ E T ->
     dchk E e T ->
     dinf E  ( (dexp_anno e T) )  T
 | dinf_unit : forall (E:denv),
     dwf_env E ->
     dinf E dexp_unit dtyp_unit
 | dinf_app : forall (E:denv) (e1 e2:dexp) (T1 T2:dtyp),
     dinf E e1 T2 ->
     dinfapp E T2 e2 T1 ->
     dinf E  ( (dexp_app e1 e2) )  T1
 | dinf_tabs : forall (L:vars) (E:denv) (e:dexp) (T1 T2:dtyp),
    dwf_typ E (dtyp_all T2) ->
      ( forall X , X \notin  L  -> dchk  ( X ~ dbind_tvar_empty  ++  E )  (dexp_anno  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )   ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) )  ( open_dtyp_wrt_dtyp T2 (dtyp_var_f X) )  )  ->
     dinf E (dexp_tabs (dbody_anno e T1)) (dtyp_all T2)
| dinf_tappbot : forall (E:denv) (e:dexp) (T:dtyp),
     dwf_typ E T ->
     dinf E e dtyp_bot ->
     dinf E (dexp_tapp e T) dtyp_bot
 | dinf_tappall : forall (E:denv) (e1:dexp) (T2 T1:dtyp),
     dinf E e1 (dtyp_all T1) ->
     dwf_typ E T2 ->
     dinf E (dexp_tapp e1 T2)  (open_dtyp_wrt_dtyp  T1   T2 ) 
with dchk : denv -> dexp -> dtyp -> Prop :=    (* defn dchk *)
 | dchk_top_abs : forall (L:vars) (E:denv) (e:dexp),
      ( forall x , x \notin  L  -> dchk  ( x ~ (dbind_typ dtyp_bot)  ++  E )   ( open_dexp_wrt_dexp e (dexp_var_f x) )  dtyp_top )  ->
     dchk E (dexp_abs e) dtyp_top
 | dchk_abs : forall (L:vars) (E:denv) (e:dexp) (T1 T2:dtyp),
     dwf_typ E T1 ->
      ( forall x , x \notin  L  -> dchk  ( x ~ (dbind_typ T1)  ++  E )   ( open_dexp_wrt_dexp e (dexp_var_f x) )  T2 )  ->
     dchk E (dexp_abs e) (dtyp_arrow T1 T2)
 | dchk_app : forall (E:denv) (e1 e2:dexp) (T2 T1:dtyp),
     dinf E e1 T1 ->
     dinfapp E T1 e2 T2 ->
     dchk E (dexp_app e1 e2) T2
 | dchk_all : forall (L:vars) (E:denv) (e:dexp) (T:dtyp),
     dwf_typ E (dtyp_all T) ->
      ( forall X , X \notin  L  -> dchk  ( X ~ dbind_tvar_empty  ++  E )  e  ( open_dtyp_wrt_dtyp T (dtyp_var_f X) )  )  ->
     dchk E e (dtyp_all T)
 | dchk_sub : forall (E:denv) (e:dexp) (T S:dtyp),
     dinf E e S ->
     dsub E S T ->
     dchk E e T
 | dchk_intersection : forall (E:denv) (e:dexp) (S T:dtyp),
     dchk E e S ->
     dchk E e T ->
     dchk E e (dtyp_intersection S T)
 | dchk_union1 : forall (E:denv) (e:dexp) (S T:dtyp),
     dchk E e S ->
     dwf_typ E T ->
     dchk E e (dtyp_union S T)
 | dchk_union2 : forall (E:denv) (e:dexp) (S T:dtyp),
     dchk E e T ->
     dwf_typ E S ->
     dchk E e (dtyp_union S T)
with dinfapp : denv -> dtyp -> dexp -> dtyp -> Prop :=    (* defn dinfapp *)
 | dinfapp_arrow : forall (E:denv) (T1 T2:dtyp) (e:dexp),
     dwf_typ E T2 ->
     dchk E e T1 ->
     dinfapp E  ( (dtyp_arrow T1 T2) )  e T2
 | dinfapp_all : forall (E:denv) (T1:dtyp) (e:dexp) (T2 T3:dtyp),
     dmono_typ T3 ->
     dwf_typ E T3 ->
     dwf_typ E (dtyp_all T1) ->
     dinfapp E  (open_dtyp_wrt_dtyp  T1   T3 )  e T2 ->
     dinfapp E  ( (dtyp_all T1) )  e T2
 | dinfapp_bot : forall (E:denv) (e:dexp),
     dchk E e dtyp_top ->
     dinfapp E dtyp_bot e dtyp_bot. *)

Inductive dtyping_mode :=
    | dtypingmode_inf 
    | dtypingmode_chk
    | dtypingmode_infapp (t : dtyp).

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
| dtyping_inftabs : forall (L:vars) (E:denv) (e:dexp) (T1 T2:dtyp),
dwf_typ E (dtyp_all T2) ->
    ( forall X , X \notin  L  -> dtyping  ( X ~ dbind_tvar_empty  ++  E ) (dexp_anno  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) ) dtypingmode_chk ( open_dtyp_wrt_dtyp T2 (dtyp_var_f X) )  )  ->
    dtyping E (dexp_tabs (dbody_anno e T1)) dtypingmode_inf (dtyp_all T2)
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

Fixpoint dtyp_order (t : dtyp) : nat :=
  match t with
  | dtyp_arrow A B => dtyp_order A + dtyp_order B
  | dtyp_all A  => S (dtyp_order A)
  | dtyp_intersection A B => dtyp_order A + dtyp_order B
  | dtyp_union A B => dtyp_order A + dtyp_order B
  | _ => 0
  end.

  
(* 

Reserved Notation "G ⊢ t1 <: t2 | n "
(at level 65, t1 at next level, t2 at next level, no associativity).
Inductive sized_ld_sub : ld_context -> ld_type -> ld_type -> nat -> Prop :=
| sls_var : forall G x n,
    ⊢ G ->  ld_in_context x G -> G ⊢ (ld_t_var_f x) <: (ld_t_var_f x) | n
| sls_int : forall G n,
    ⊢ G -> G ⊢ ld_t_int <: ld_t_int | n
| sls_arrow : forall G A B C D n1 n2,
    G ⊢ C <: A | n1 ->
    G ⊢ B <: D | n2 ->
    G ⊢ (ld_t_arrow A B) <: (ld_t_arrow C D) | S (n1 + n2)
| sls_intersection_r : forall G A B1 B2 n1 n2,
    G ⊢ A <: B1 | n1 ->
    G ⊢ A <: B2 | n2 -> 
    G ⊢ A <: (ld_t_intersection B1 B2) | S (n1 + n2)
| sls_intersection_l1 : forall G A1 A2 B n1,
    G ⊢ A1 <: B | n1 ->
    ld_wf_type G A2 -> 
    G ⊢ (ld_t_intersection A1 A2) <: B | S n1
| sls_intersection_l2 : forall G A1 A2 B n2,
    G ⊢ A2 <: B | n2 ->
    ld_wf_type G A1 -> 
    G ⊢ (ld_t_intersection A1 A2) <: B | S n2
| sls_union_r1 : forall G A B1 B2 n1,
    G ⊢ A <: B1 | n1 ->
    ld_wf_type G B2 ->
    G ⊢ A <: (ld_t_union B1 B2) | S n1
| sls_union_r2 : forall G A B1 B2 n2,
    G ⊢ A <: B2 | n2 ->
    ld_wf_type G B1 ->
    G ⊢ A <: (ld_t_union B1 B2) | S n2
| sls_union_l : forall G A1 A2 B n1 n2,
    G ⊢ A1 <: B | n1 ->
    G ⊢ A2 <: B | n2 ->
    G ⊢ (ld_t_union A1 A2) <: B | S ( n1 + n2)
| sls_foralll : forall G A B t n,
    ld_wf_mtype G t ->
    G ⊢ (open_ld_type_wrt_ld_type A t) <: B | n ->
    G ⊢ (ld_t_forall A) <: B | S n
| sls_forallr : forall L G A B n,
    (forall x, x \notin L -> (ld_ctx_cons G x) ⊢ A <: (open_ld_type_wrt_ld_type B (ld_t_var_f x)) | n) ->
    G ⊢ A <: (ld_t_forall B) | S n
where "G ⊢ t1 <: t2 | n" := (sized_ld_sub G t1 t2 n). *)
