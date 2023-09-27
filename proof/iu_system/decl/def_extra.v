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
 | dwftyps_all : forall (L:vars) (E:denv) (T1:dtyp),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> dwf_typ_s  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     dwf_typ_s E (dtyp_all T1)
 | dwftyps_union : forall (E:denv) (T1 T2:dtyp),
     dwf_typ_s E T1 ->
     dwf_typ_s E T2 ->
     dwf_typ_s E (dtyp_union T1 T2)
 | dwftyps_intersection : forall (E:denv) (T1 T2:dtyp),
     dwf_typ_s E T1 ->
     dwf_typ_s E T2 ->
     dwf_typ_s E (dtyp_intersection T1 T2).

Inductive d_sub : denv -> dtyp -> dtyp -> Prop :=    (* defn d_sub *)
 | d_sub_top : forall (E:denv) (S1:dtyp),
     dwf_env E ->
     dwf_typ E S1 ->
     d_sub E S1 dtyp_top
 | d_sub_bot : forall (E:denv) (T1:dtyp),
     dwf_env E ->
     dwf_typ E T1 ->
     d_sub E dtyp_bot T1
 | d_sub_unit : forall (E:denv),
     dwf_env E ->
     d_sub E dtyp_unit dtyp_unit
 | d_sub_tvar : forall (E:denv) (X:typvar),
     dwf_env E ->
     dwf_typ E (dtyp_var_f X) ->
     d_sub E (dtyp_var_f X) (dtyp_var_f X)
 | d_sub_stvar : forall (E:denv) (SX:stypvar),
     dwf_env E ->
     dwf_typ E (dtyp_svar SX) ->
     d_sub E (dtyp_svar SX) (dtyp_svar SX)
 | d_sub_arrow : forall (E:denv) (S1 S2 T1 T2:dtyp),
     d_sub E T1 S1 ->
     d_sub E S2 T2 ->
     d_sub E (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
 | d_sub_all : forall (L:vars) (E:denv) (S1 T1:dtyp),
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> ds_in_s SX  (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     ( forall SX , SX \notin L -> d_sub  ( SX ~ dbind_stvar_empty  ++  E )   (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ) ->
     d_sub E (dtyp_all S1) (dtyp_all T1)
 | d_sub_alll : forall (L:vars) (E:denv) (S1 T1 T2:dtyp),
     dneq_all T1 ->
     dneq_intersection T1 ->
     dneq_union T1 -> 
     ( forall X , X \notin L -> ds_in X  (open_dtyp_wrt_dtyp  S1   (dtyp_var_f X) ) ) ->
     dwf_typ E T2 ->
     dmono_typ T2 ->
     d_sub E  (open_dtyp_wrt_dtyp  S1   T2 )  T1 ->
     d_sub E (dtyp_all S1) T1
 | d_sub_intersection1 : forall (E:denv) (S1 T1 T2:dtyp),
     d_sub E S1 T1 ->
     d_sub E S1 T2 ->
     d_sub E S1 (dtyp_intersection T1 T2)
 | d_sub_intersection2 : forall (E:denv) (S1 S2 T1:dtyp),
     d_sub E S1 T1 ->
     dwf_typ E S2 ->
     d_sub E (dtyp_intersection S1 S2) T1
 | d_sub_intersection3 : forall (E:denv) (S1 S2 T1:dtyp),
     d_sub E S2 T1 ->
     dwf_typ E S1 ->
     d_sub E (dtyp_intersection S1 S2) T1
 | d_sub_union1 : forall (E:denv) (S1 T1 T2:dtyp),
     d_sub E S1 T1 ->
     dwf_typ E T2 ->
     d_sub E S1 (dtyp_union T1 T2)
 | d_sub_union2 : forall (E:denv) (S1 T1 T2:dtyp),
     d_sub E S1 T2 ->
     dwf_typ E T1 ->
     d_sub E S1 (dtyp_union T1 T2)
 | d_sub_union3 : forall (E:denv) (S1 S2 T1:dtyp),
     d_sub E S1 T1 ->
     d_sub E S2 T1 ->
     d_sub E (dtyp_union S1 S2) T1.


Inductive d_inftapp_false : dtyp -> Prop := 
| d__inftappfalse__var : forall (X:atom),
    d_inftapp_false (dtyp_var_f X)
| d__inftappfalse__svar : forall (SX:atom),
    d_inftapp_false (dtyp_svar SX)
| d__inftappfalse__top :
    d_inftapp_false (dtyp_top)
| d__inftappfalse__unit :
    d_inftapp_false (dtyp_unit)
| d__inftappfalse__arr : forall (A1 A2:dtyp),
    d_inftapp_false (dtyp_arrow A1 A2)
| d__inftappfalse__intersection : forall (A1 A2:dtyp),
    d_inftapp_false A1 -> 
    d_inftapp_false A2 -> 
    d_inftapp_false (dtyp_intersection A1 A2)
| d__inftappfalse__union1 : forall (A1 A2:dtyp),
    d_inftapp_false A1 -> 
    d_inftapp_false (dtyp_union A1 A2)
| d__inftappfalse__union2 : forall (A1 A2:dtyp),
    d_inftapp_false A2 -> 
    d_inftapp_false (dtyp_union A1 A2)
.

Inductive d_inftapp : denv -> dtyp -> dtyp -> dtyp -> Prop := 
| d_inftapp_bot : forall (E:denv) (T1:dtyp),
    dwf_env E -> 
    dwf_typ E T1 ->
    d_inftapp E dtyp_bot T1 dtyp_bot
| d_inftapp_all : forall (E:denv) (T1 T2:dtyp),
    dwf_env E -> 
    dwf_typ E (dtyp_all T1) ->
    dwf_typ E T2 ->
    d_inftapp E (dtyp_all T1) T2 (open_dtyp_wrt_dtyp  T1   T2 )
| d_inftapp_intersection1 : forall (E:denv) (A1 A2 B C1:dtyp),
    dwf_typ E A2 ->
    d_inftapp E A1 B C1 ->
    d_inftapp E (dtyp_intersection A1 A2) B C1
| d_inftapp_intersection2 : forall (E:denv) (A1 A2 B C2:dtyp),
    dwf_typ E A1 ->
    d_inftapp E A2 B C2 ->
    d_inftapp E (dtyp_intersection A1 A2) B C2
| d_inftapp_union : forall (E:denv) (A1 A2 B C1 C2:dtyp),
    d_inftapp E A1 B C1 ->
    d_inftapp E A2 B C2 ->
    d_inftapp E (dtyp_union A1 A2) B (dtyp_union C1 C2)
.


Inductive d_infabs : denv -> dtyp -> dtyp -> dtyp -> Prop := 
| d_infabs_bot : forall (E:denv),
    dwf_env E ->
    d_infabs E dtyp_bot dtyp_top dtyp_bot
| d_infabs_arr : forall (E:denv) (T1 T2:dtyp),
    dwf_env E ->
    dwf_typ E T1 ->
    dwf_typ E T2 ->
    d_infabs E (dtyp_arrow T1 T2) T1 T2
| d_infabs_all : forall (E:denv) (T1 T2 T3 T4:dtyp),
    dmono_typ T2 -> 
    dwf_typ E T2 ->
    dwf_typ E (dtyp_all T1) ->
    d_infabs E  (open_dtyp_wrt_dtyp  T1   T2 ) T3 T4 ->
    d_infabs E (dtyp_all T1) T3 T4
| d_infabs_intersection1 : forall (E:denv) (T1 T2 T3 T4:dtyp),
    dwf_typ E T2 ->
    d_infabs E T1 T3 T4->
    d_infabs E (dtyp_intersection T1 T2) T3 T4
| d_infabs_intersection2 : forall (E:denv) (T1 T2 T3 T4:dtyp),
    dwf_typ E T1 ->
    d_infabs E T2 T3 T4->
    d_infabs E (dtyp_intersection T1 T2) T3 T4
| d_infabs_union : forall (E:denv) (T1 T2 T3 T4 T5 T6:dtyp),
    d_infabs E T1 T3 T4->
    d_infabs E T2 T5 T6->
    d_infabs E (dtyp_union T1 T2) (dtyp_intersection T3 T5) (dtyp_union T4 T6)
.

Inductive d_typing_mode :=
| d_typingmode_inf 
| d_typingmode_chk.

Inductive d_typing : denv -> dexp -> d_typing_mode -> dtyp -> Prop :=
| d_typing_infvar : forall (E:denv) (x:expvar) (T1:dtyp),
    dwf_env E ->
    binds ( x )  ( (dbind_typ T1) ) ( E )  ->
    d_typing E (dexp_var_f x) d_typingmode_inf T1
| d_typing_infanno : forall (E:denv) (e:dexp) (T1:dtyp),
    dwf_typ E T1 ->
    d_typing E e d_typingmode_chk T1 ->
    d_typing E  ( (dexp_anno e T1) )  d_typingmode_inf T1
| d_typinginf_unit : forall (E:denv),
    dwf_env E ->
    d_typing E dexp_unit d_typingmode_inf dtyp_unit
| d_typing_infapp : forall (E:denv) (e1 e2:dexp) (T1 T2 T3:dtyp),
    d_typing E e1 d_typingmode_inf T1 ->
    d_infabs E T1 T2 T3 ->
    d_typing E e2 d_typingmode_chk T2 ->
    d_typing E  ( (dexp_app e1 e2) ) d_typingmode_inf T3
| d_typing_inftabs : forall (L:vars) (E:denv) (e:dexp) (T1:dtyp),
dwf_typ E (dtyp_all T1) ->
    ( forall X , X \notin  L  -> d_typing  ( X ~ dbind_tvar_empty  ++  E ) (dexp_anno  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) ) d_typingmode_chk ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) )  )  ->
    d_typing E (dexp_tabs (dbody_anno e T1)) d_typingmode_inf (dtyp_all T1)
| d_typing_inftapp : forall (E:denv) (e1:dexp) (T1 T2 T3:dtyp),
    dwf_typ E T2 ->
    d_typing E e1 d_typingmode_inf T1 ->
    d_inftapp E T1 T2 T3 ->
    d_typing E (dexp_tapp e1 T2) d_typingmode_inf T3
| d_typing_chkabstop : forall (L:vars) (E:denv) (e:dexp),
    ( forall x , x \notin  L  -> d_typing  ( x ~ (dbind_typ dtyp_bot)  ++  E )   ( open_dexp_wrt_dexp e (dexp_var_f x) ) d_typingmode_chk dtyp_top )  ->
    d_typing E (dexp_abs e) d_typingmode_chk dtyp_top
| d_typing_chkabs : forall (L:vars) (E:denv) (e:dexp) (T1 T2:dtyp),
    dwf_typ E T1 ->
    ( forall x , x \notin  L  -> d_typing  ( x ~ (dbind_typ T1)  ++  E )  ( open_dexp_wrt_dexp e (dexp_var_f x) ) d_typingmode_chk T2 )  ->
    d_typing E (dexp_abs e) d_typingmode_chk (dtyp_arrow T1 T2)
(* | d_typing_chkall : forall (L:vars) (E:denv) (e:dexp) (T1:dtyp),
    dwf_typ E (dtyp_all T1) ->
    ( forall X , X \notin  L  -> d_typing  ( X ~ dbind_tvar_empty  ++  E )  e  d_typingmode_chk ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) )  )  ->
    d_typing E e d_typingmode_chk (dtyp_all T1) *)
| d_typing_chksub : forall (E:denv) (e:dexp) (T1 S1:dtyp),
    d_typing E e d_typingmode_inf S1 ->
    d_sub E S1 T1 ->
    d_typing E e d_typingmode_chk T1
| d_typing_chkintersection : forall (E:denv) (e:dexp) (S1 T1:dtyp),
    d_typing E e d_typingmode_chk S1 ->
    d_typing E e d_typingmode_chk T1 ->
    d_typing E e d_typingmode_chk (dtyp_intersection S1 T1)
| d_typing_chkunion1 : forall (E:denv) (e:dexp) (S1 T1:dtyp),
    d_typing E e d_typingmode_chk S1 ->
    dwf_typ E T1 ->
    d_typing E e d_typingmode_chk (dtyp_union S1 T1)
| d_typing_chkunion2 : forall (E:denv) (e:dexp) (S1 T1:dtyp),
    d_typing E e d_typingmode_chk T1 ->
    dwf_typ E S1 ->
    d_typing E e d_typingmode_chk (dtyp_union S1 T1)
.
