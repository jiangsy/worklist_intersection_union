Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import decl.def_ott.
Require Import decl.def_extra.

Inductive dexp_red : dexp -> dexp -> Prop :=    (* defn dexp_red *)
 | dexpred_app1 : forall (e1 e2 e1':dexp),
     lc_dexp e2 ->
     dexp_red e1 e1' ->
     dexp_red (dexp_app e1 e2) (dexp_app e1' e2)
 | dexpred_app2 : forall (e1 e2 e2':dexp),
     d_isval e1 ->
     dexp_red e2 e2' ->
     dexp_red (dexp_app e1 e2) (dexp_app e1 e2')
 | dexpred_tapp : forall (e1:dexp) (T:dtyp) (e1':dexp),
     lc_dtyp T ->
     dexp_red e1 e1' ->
     dexp_red (dexp_tapp e1 T) (dexp_tapp e1' T)
 | dexpred_abs : forall (e1 e2:dexp),
     lc_dexp (dexp_abs e1) ->
     d_isval e2 ->
     dexp_red (dexp_app  ( (dexp_abs e1) )  e2)  (open_dexp_wrt_dexp  e1   e2 ) 
 | dexpred_abs2 : forall (e1:dexp) (T1:dtyp) (e2:dexp),
     lc_dexp (dexp_abs e1) ->
     lc_dtyp T1 ->
     d_isval e2 ->
     dexp_red (dexp_app  ( (dexp_anno  ( (dexp_abs e1) )  T1) )  e2)  (  (open_dexp_wrt_dexp  e1   e2 )  ) 
 | dexpred_anno : forall (e:dexp) (T:dtyp) (e':dexp),
     lc_dtyp T ->
     dexp_red e e' ->
     dexp_red (dexp_anno e T) (dexp_anno e' T)
 | dexpred_tapptabs : forall (e:dexp) (T1 T2:dtyp),
     lc_dexp (dexp_tabs (dbody_anno e T1)) ->
     lc_dtyp T2 ->
     dexp_red (dexp_tapp  ( (dexp_tabs (dbody_anno e T1)) )  T2)  (open_dexp_wrt_dtyp   ( (dexp_anno e T1) )    T2 ) 
 | dexpred_tappabs : forall (e:dexp) (T1 T2:dtyp),
     lc_dtyp (dtyp_all T1) ->
     lc_dexp (dexp_abs e) ->
     lc_dtyp T2 ->
     dexp_red (dexp_tapp  ( (dexp_anno  ( (dexp_abs e) )  (dtyp_all T1)) )  T2) (dexp_anno  ( (dexp_abs e) )   (open_dtyp_wrt_dtyp  T1   T2 ) )
 | dexpred_tappbot : forall (e1:dexp) (T:dtyp),
     lc_dtyp T ->
     d_isval e1 ->
     dexp_red (dexp_tapp  ( (dexp_anno e1 dtyp_bot) )  T)  ( (dexp_anno e1 dtyp_bot) ) 
 | dexpred_deanno : forall (e1:dexp) (T1:dtyp),
     lc_dtyp T1 ->
     d_neq_abs e1 ->
     d_isval e1 ->
     dexp_red  ( (dexp_anno e1 T1) )  e1.



Inductive d_typing_exptapp : denv -> dexp -> d_typing_mode -> dtyp -> Prop :=
| d_exptyping_infvar : forall (E:denv) (x:expvar) (T1:dtyp),
    dwf_env E ->
    binds ( x )  ( (dbind_typ T1) ) ( E )  ->
    d_typing_exptapp E (dexp_var_f x) d_typingmode_inf T1
| d_exptyping_infanno : forall (E:denv) (e:dexp) (T1:dtyp),
    dwf_typ E T1 ->
    d_typing_exptapp E e d_typingmode_chk T1 ->
    d_typing_exptapp E  ( (dexp_anno e T1) )  d_typingmode_inf T1
| d_typinginf_unit : forall (E:denv),
    dwf_env E ->
    d_typing_exptapp E dexp_unit d_typingmode_inf dtyp_unit
| d_exptyping_infapp : forall (E:denv) (e1 e2:dexp) (T1 T2:dtyp),
    d_typing_exptapp E e1 d_typingmode_inf T2 ->
    d_typing_exptapp E e2 (d_typingmode_infapp T2) T1 ->
    d_typing_exptapp E  ( (dexp_app e1 e2) ) d_typingmode_inf T1
| d_exptyping_inftabs : forall (L:vars) (E:denv) (e:dexp) (T1:dtyp),
dwf_typ E (dtyp_all T1) ->
    ( forall X , X \notin  L  -> d_typing_exptapp  ( X ~ dbind_tvar_empty  ++  E ) (dexp_anno  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) ) d_typingmode_chk ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) )  )  ->
    d_typing_exptapp E (dexp_tabs (dbody_anno e T1)) d_typingmode_inf (dtyp_all T1)
| d_exptyping_inftappbot : forall (E:denv) (e:dexp) (T1:dtyp),
    dwf_typ E T1 ->
    d_typing_exptapp E e d_typingmode_inf dtyp_bot ->
    d_typing_exptapp E (dexp_tapp e T1) d_typingmode_inf dtyp_bot
| d_exptyping_inftappall : forall (E:denv) (e1:dexp) (T2 T1:dtyp),
    dwf_typ E T2 ->
    d_typing_exptapp E e1 d_typingmode_inf (dtyp_all T1) ->
    d_typing_exptapp E (dexp_tapp e1 T2) d_typingmode_inf (open_dtyp_wrt_dtyp  T1 T2 ) 
| d_exptyping_chkabstop : forall (L:vars) (E:denv) (e:dexp),
    ( forall x , x \notin  L  -> d_typing_exptapp  ( x ~ (dbind_typ dtyp_bot)  ++  E )   ( open_dexp_wrt_dexp e (dexp_var_f x) ) d_typingmode_chk dtyp_top )  ->
    d_typing_exptapp E (dexp_abs e) d_typingmode_chk dtyp_top
| d_exptyping_chkabs : forall (L:vars) (E:denv) (e:dexp) (T1 T2:dtyp),
    dwf_typ E T1 ->
    ( forall x , x \notin  L  -> d_typing_exptapp  ( x ~ (dbind_typ T1)  ++  E )  ( open_dexp_wrt_dexp e (dexp_var_f x) ) d_typingmode_chk T2 )  ->
    d_typing_exptapp E (dexp_abs e) d_typingmode_chk (dtyp_arrow T1 T2)
| d_exptyping_chkall : forall (L:vars) (E:denv) (e:dexp) (T1:dtyp),
    dwf_typ E (dtyp_all T1) ->
    ( forall X , X \notin  L  -> d_typing_exptapp  ( X ~ dbind_tvar_empty  ++  E )  e  d_typingmode_chk ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) )  )  ->
    d_typing_exptapp E e d_typingmode_chk (dtyp_all T1)
| d_exptyping_chksub : forall (E:denv) (e:dexp) (T1 S1:dtyp),
    d_sub E S1 T1 ->
    d_typing_exptapp E e d_typingmode_inf S1 ->
    d_typing_exptapp E e d_typingmode_chk T1
| d_exptyping_chkintersection : forall (E:denv) (e:dexp) (S1 T1:dtyp),
    d_typing_exptapp E e d_typingmode_chk S1 ->
    d_typing_exptapp E e d_typingmode_chk T1 ->
    d_typing_exptapp E e d_typingmode_chk (dtyp_intersection S1 T1)
| d_exptyping_chkunion1 : forall (E:denv) (e:dexp) (S1 T1:dtyp),
    dwf_typ E T1 ->
    d_typing_exptapp E e d_typingmode_chk S1 ->
    d_typing_exptapp E e d_typingmode_chk (dtyp_union S1 T1)
| d_exptyping_chkunion2 : forall (E:denv) (e:dexp) (S1 T1:dtyp),
    dwf_typ E S1 ->
    d_typing_exptapp E e d_typingmode_chk T1 ->
    d_typing_exptapp E e d_typingmode_chk (dtyp_union S1 T1)
| d_exptyping_infapparrow : forall (E:denv) (T1 T2:dtyp) (e:dexp),
    dwf_typ E T2 ->
    d_typing_exptapp E e d_typingmode_chk T1 ->
    d_typing_exptapp E e ( d_typingmode_infapp ( (dtyp_arrow T1 T2) ) ) T2
| d_exptyping_infappbot : forall (E:denv) (e:dexp),
    d_typing_exptapp E e d_typingmode_chk dtyp_top ->
    d_typing_exptapp E e ( d_typingmode_infapp dtyp_bot ) dtyp_bot
| d_exptyping_infappintersection1 : forall (E:denv) (e:dexp) (S1 S2 T1:dtyp),
    dwf_typ E S2 ->
    d_typing_exptapp E e ( d_typingmode_infapp S1 ) T1 ->
    d_typing_exptapp E e ( d_typingmode_infapp (dtyp_intersection S1 S2) ) T1
| d_exptyping_infappintersection2 : forall (E:denv) (e:dexp) (S1 S2 T1:dtyp),
    dwf_typ E S1 ->
    d_typing_exptapp E e ( d_typingmode_infapp S2 ) T1 ->
    d_typing_exptapp E e ( d_typingmode_infapp (dtyp_intersection S1 S2) ) T1 
| d_exptyping_infappunion : forall (E:denv) (e:dexp) (S1 S2 T1:dtyp),
    d_typing_exptapp E e ( d_typingmode_infapp S1 ) T1 ->
    d_typing_exptapp E e ( d_typingmode_infapp S2 ) T1 ->
    d_typing_exptapp E e ( d_typingmode_infapp (dtyp_union S1 S2) ) T1
    .


