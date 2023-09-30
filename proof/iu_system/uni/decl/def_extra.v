Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.prop_ln.
Require Export uni.def_ott.


Fixpoint ftv_sin_typ (T:typ) : vars :=
  match T with
  | typ_unit => {}
  | typ_top => {}
  | typ_bot => {}
  | (typ_var_b nat) => {}
  | (typ_var_f X) => {{X}}
  | (typ_arrow T1 T2) => (ftv_sin_typ T1) \u (ftv_sin_typ T2)
  | (typ_all T) => (ftv_sin_typ T)
  | (typ_union T1 T2) => AtomSetImpl.inter (ftv_sin_typ T1) (ftv_sin_typ T2)
  | (typ_intersection T1 T2) => AtomSetImpl.inter (ftv_sin_typ T1) (ftv_sin_typ T2)
end.


(* defns Jd_wf_typ_s *)
Inductive d_wf_typ_s : denv -> typ -> Prop :=    (* defn d_wf_typ_s *)
 | dwftyps_unit : forall (E:denv),
     d_wf_typ_s E typ_unit
 | dwftyps_bot : forall (E:denv),
     d_wf_typ_s E typ_bot
 | dwftyps_top : forall (E:denv),
     d_wf_typ_s E typ_top
 | dwftyps_var : forall (E:denv) (X:typvar),
      binds ( X )  ( dbind_tvar_empty ) ( E )  ->
     d_wf_typ_s E (typ_var_f X)
 | dwftyps_stvar : forall (E:denv) (X:typvar),
      binds ( X ) ( dbind_stvar_empty ) ( E )  ->
     d_wf_typ_s E (typ_var_f X)
 | dwftyps_arrow : forall (E:denv) (T1 T2:typ),
     d_wf_typ_s E T1 ->
     d_wf_typ_s E T2 ->
     d_wf_typ_s E (typ_arrow T1 T2)
 | dwftyps_all : forall (L:vars) (E:denv) (T1:typ),
     ( forall X , X \notin L -> ds_in X  (open_typ_wrt_typ  T1   (typ_var_f X) ) ) ->
     ( forall X , X \notin L -> d_wf_typ_s  ( X ~ dbind_stvar_empty  ++  E )   (open_typ_wrt_typ  T1   (typ_var_f X) ) ) ->
     d_wf_typ_s E (typ_all T1)
 | dwftyps_union : forall (E:denv) (T1 T2:typ),
     d_wf_typ_s E T1 ->
     d_wf_typ_s E T2 ->
     d_wf_typ_s E (typ_union T1 T2)
 | dwftyps_intersection : forall (E:denv) (T1 T2:typ),
     d_wf_typ_s E T1 ->
     d_wf_typ_s E T2 ->
     d_wf_typ_s E (typ_intersection T1 T2).


Inductive d_inftapp : denv -> typ -> typ -> typ -> Prop := 
| d_inftapp_bot : forall (E:denv) (T1:typ),
    d_wf_env E -> 
    d_wf_typ E T1 ->
    d_inftapp E typ_bot T1 typ_bot
| d_inftapp_all : forall (E:denv) (T1 T2:typ),
    d_wf_env E -> 
    d_wf_typ E (typ_all T1) ->
    d_wf_typ E T2 ->
    d_inftapp E (typ_all T1) T2 (open_typ_wrt_typ  T1   T2 )
| d_inftapp_intersection1 : forall (E:denv) (A1 A2 B C1:typ),
    d_wf_typ E A2 ->
    d_inftapp E A1 B C1 ->
    d_inftapp E (typ_intersection A1 A2) B C1
| d_inftapp_intersection2 : forall (E:denv) (A1 A2 B C2:typ),
    d_wf_typ E A1 ->
    d_inftapp E A2 B C2 ->
    d_inftapp E (typ_intersection A1 A2) B C2
| d_inftapp_union : forall (E:denv) (A1 A2 B C1 C2:typ),
    d_inftapp E A1 B C1 ->
    d_inftapp E A2 B C2 ->
    d_inftapp E (typ_union A1 A2) B (typ_union C1 C2)
.


Inductive d_infabs : denv -> typ -> typ -> typ -> Prop := 
| d_infabs_bot : forall (E:denv),
    d_wf_env E ->
    d_infabs E typ_bot typ_top typ_bot
| d_infabs_arr : forall (E:denv) (T1 T2:typ),
    d_wf_env E ->
    d_wf_typ E T1 ->
    d_wf_typ E T2 ->
    d_infabs E (typ_arrow T1 T2) T1 T2
| d_infabs_all : forall (E:denv) (T1 T2 T3 T4:typ),
    d_mono_typ E T2 -> 
    d_wf_typ E T2 ->
    d_wf_typ E (typ_all T1) ->
    d_infabs E  (open_typ_wrt_typ  T1   T2 ) T3 T4 ->
    d_infabs E (typ_all T1) T3 T4
| d_infabs_intersection1 : forall (E:denv) (T1 T2 T3 T4:typ),
    d_wf_typ E T2 ->
    d_infabs E T1 T3 T4->
    d_infabs E (typ_intersection T1 T2) T3 T4
| d_infabs_intersection2 : forall (E:denv) (T1 T2 T3 T4:typ),
    d_wf_typ E T1 ->
    d_infabs E T2 T3 T4->
    d_infabs E (typ_intersection T1 T2) T3 T4
| d_infabs_union : forall (E:denv) (T1 T2 T3 T4 T5 T6:typ),
    d_infabs E T1 T3 T4->
    d_infabs E T2 T5 T6->
    d_infabs E (typ_union T1 T2) (typ_intersection T3 T5) (typ_union T4 T6)
.

Inductive typing_mode :=
| typingmode__inf 
| typingmode__chk.

Inductive d_typing : denv -> exp -> typing_mode -> typ -> Prop :=
| d_typing_infvar : forall (E:denv) (x:expvar) (T1:typ),
    d_wf_env E ->
    binds ( x )  ( (dbind_typ T1) ) ( E )  ->
    d_typing E (exp_var_f x) typingmode__inf T1
| d_typing_infanno : forall (E:denv) (e:exp) (T1:typ),
    d_wf_typ E T1 ->
    d_typing E e typingmode__chk T1 ->
    d_typing E  ( (exp_anno e T1) )  typingmode__inf T1
| d_typinginf_unit : forall (E:denv),
    d_wf_env E ->
    d_typing E exp_unit typingmode__inf typ_unit
| d_typing_infapp : forall (E:denv) (e1 e2:exp) (T1 T2 T3:typ),
    d_typing E e1 typingmode__inf T1 ->
    d_infabs E T1 T2 T3 ->
    d_typing E e2 typingmode__chk T2 ->
    d_typing E  ( (exp_app e1 e2) ) typingmode__inf T3
| d_typing_inftabs : forall (L:vars) (E:denv) (e:exp) (T1:typ),
d_wf_typ E (typ_all T1) ->
    ( forall X , X \notin  L  -> d_typing  ( X ~ dbind_tvar_empty  ++  E ) (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) )  ( open_typ_wrt_typ T1 (typ_var_f X) ) ) typingmode__chk ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
    d_typing E (exp_tabs (body_anno e T1)) typingmode__inf (typ_all T1)
| d_typing_inftapp : forall (E:denv) (e1:exp) (T1 T2 T3:typ),
    d_wf_typ E T2 ->
    d_typing E e1 typingmode__inf T1 ->
    d_inftapp E T1 T2 T3 ->
    d_typing E (exp_tapp e1 T2) typingmode__inf T3
| d_typing_chkabstop : forall (L:vars) (E:denv) (e:exp),
    ( forall x , x \notin  L  -> d_typing  ( x ~ (dbind_typ typ_bot)  ++  E )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk typ_top )  ->
    d_typing E (exp_abs e) typingmode__chk typ_top
| d_typing_chkabs : forall (L:vars) (E:denv) (e:exp) (T1 T2:typ),
    d_wf_typ E T1 ->
    ( forall x , x \notin  L  -> d_typing  ( x ~ (dbind_typ T1)  ++  E )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk T2 )  ->
    d_typing E (exp_abs e) typingmode__chk (typ_arrow T1 T2)
(* | d_typing_chkall : forall (L:vars) (E:denv) (e:exp) (T1:typ),
    d_wf_typ E (typ_all T1) ->
    ( forall X , X \notin  L  -> d_typing  ( X ~ dbind_tvar_empty  ++  E )  e  typingmode__chk ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
    d_typing E e typingmode__chk (typ_all T1) *)
| d_typing_chksub : forall (E:denv) (e:exp) (T1 S1:typ),
    d_typing E e typingmode__inf S1 ->
    d_sub E S1 T1 ->
    d_typing E e typingmode__chk T1
| d_typing_chkintersection : forall (E:denv) (e:exp) (S1 T1:typ),
    d_typing E e typingmode__chk S1 ->
    d_typing E e typingmode__chk T1 ->
    d_typing E e typingmode__chk (typ_intersection S1 T1)
| d_typing_chkunion1 : forall (E:denv) (e:exp) (S1 T1:typ),
    d_typing E e typingmode__chk S1 ->
    d_wf_typ E T1 ->
    d_typing E e typingmode__chk (typ_union S1 T1)
| d_typing_chkunion2 : forall (E:denv) (e:exp) (S1 T1:typ),
    d_typing E e typingmode__chk T1 ->
    d_wf_typ E S1 ->
    d_typing E e typingmode__chk (typ_union S1 T1)
.
