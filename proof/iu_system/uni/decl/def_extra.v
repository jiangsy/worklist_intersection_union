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
 | d_wf_typ_s__unit : forall (Ψ:denv),
     d_wf_typ_s Ψ typ_unit
 | d_wf_typ_s__bot : forall (Ψ:denv),
     d_wf_typ_s Ψ typ_bot
 | d_wf_typ_s__top : forall (Ψ:denv),
     d_wf_typ_s Ψ typ_top
 | d_wf_typ_s__var : forall (Ψ:denv) (X:typvar),
      binds ( X )  ( dbind_tvar_empty ) ( Ψ )  ->
     d_wf_typ_s Ψ (typ_var_f X)
 | d_wf_typ_s__stvar : forall (Ψ:denv) (X:typvar),
      binds ( X ) ( dbind_stvar_empty ) ( Ψ )  ->
     d_wf_typ_s Ψ (typ_var_f X)
 | d_wf_typ_s__arrow : forall (Ψ:denv) (A1 A2:typ),
     d_wf_typ_s Ψ A1 ->
     d_wf_typ_s Ψ A2 ->
     d_wf_typ_s Ψ (typ_arrow A1 A2)
 | d_wf_typ_s__all : forall (L:vars) (Ψ:denv) (A:typ),
     ( forall X , X \notin L -> ds_in X  (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
     ( forall X , X \notin L -> d_wf_typ_s  ( X ~ dbind_stvar_empty  ++  Ψ )   (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
     d_wf_typ_s Ψ (typ_all A)
 | d_wf_typ_s__union : forall (Ψ:denv) (A1 A2:typ),
    d_wf_typ_s Ψ A1 ->
    d_wf_typ_s Ψ A2 ->
     d_wf_typ_s Ψ (typ_union A1 A2)
 | d_wf_typ_s__intersection : forall (Ψ:denv) (A1 A2:typ),
     d_wf_typ_s Ψ A1 ->
     d_wf_typ_s Ψ A2 ->
     d_wf_typ_s Ψ (typ_intersection A1 A2).


Inductive d_inftapp : denv -> typ -> typ -> typ -> Prop := 
| d_inftapp__bot : forall (Ψ:denv) (B:typ),
    d_wf_env Ψ -> 
    d_wf_typ Ψ B ->
    d_inftapp Ψ typ_bot B typ_bot
| d_inftapp__all : forall (Ψ:denv) (A B:typ),
    d_wf_env Ψ -> 
    d_wf_typ Ψ (typ_all A) ->
    d_wf_typ Ψ B ->
    d_inftapp Ψ (typ_all A) B (open_typ_wrt_typ  A B )
| d_inftapp__intersection1 : forall (Ψ:denv) (A1 A2 B C:typ),
    d_wf_typ Ψ A2 ->
    d_inftapp Ψ A1 B C ->
    d_inftapp Ψ (typ_intersection A1 A2) B C
| d_inftapp__intersection2 : forall (Ψ:denv) (A1 A2 B C:typ),
    d_wf_typ Ψ A1 ->
    d_inftapp Ψ A2 B C ->
    d_inftapp Ψ (typ_intersection A1 A2) B C
| d_typing__union : forall (Ψ:denv) (A1 A2 B C1 C2:typ),
    d_inftapp Ψ A1 B C1 ->
    d_inftapp Ψ A2 B C2 ->
    d_inftapp Ψ (typ_union A1 A2) B (typ_union C1 C2)
.


Inductive d_infabs : denv -> typ -> typ -> typ -> Prop := 
| d_infabs__bot : forall (Ψ:denv),
    d_wf_env Ψ ->
    d_infabs Ψ typ_bot typ_top typ_bot
| d_infabs__arr : forall (Ψ:denv) (A B:typ),
    d_wf_env Ψ ->
    d_wf_typ Ψ A ->
    d_wf_typ Ψ B ->
    d_infabs Ψ (typ_arrow A B) A B
| d_infabs__all : forall (Ψ:denv) (A B C T:typ),
    d_mono_typ Ψ T -> 
    d_wf_typ Ψ T ->
    d_wf_typ Ψ (typ_all A) ->
    d_infabs Ψ  (open_typ_wrt_typ  A  T ) B C ->
    d_infabs Ψ (typ_all A) B C
| d_infabs__intersection1 : forall (Ψ:denv) (A1 A2 B C:typ),
    d_wf_typ Ψ A2 ->
    d_infabs Ψ A1 B C ->
    d_infabs Ψ (typ_intersection A1 A2) B C 
| d_infabs__intersection2 : forall (Ψ:denv) (A1 A2 B C:typ),
    d_wf_typ Ψ A1 ->
    d_infabs Ψ A2 B C->
    d_infabs Ψ (typ_intersection A1 A2) B C
| d_infabs__union : forall (Ψ:denv) (A1 A2 B1 B2 C1 C2:typ),
    d_infabs Ψ A1 B1 C1 ->
    d_infabs Ψ A2 B2 C2 ->
    d_infabs Ψ (typ_union A1 A2) (typ_intersection B1 B2) (typ_union C1 C2)
.

Inductive typing_mode :=
| typingmode__inf 
| typingmode__chk.

Inductive d_typing : denv -> exp -> typing_mode -> typ -> Prop :=
| d_typing__infvar : forall (Ψ:denv) (x:expvar) (A:typ),
    d_wf_env Ψ ->
    binds ( x )  ( (dbind_typ A) ) ( Ψ )  ->
    d_typing Ψ (exp_var_f x) typingmode__inf A
| d_typing__infanno : forall (Ψ:denv) (e:exp) (A:typ),
    d_wf_typ Ψ A ->
    d_typing Ψ e typingmode__chk A ->
    d_typing Ψ  ( (exp_anno e A) )  typingmode__inf A
| d_typinginf_unit : forall (Ψ:denv),
    d_wf_env Ψ ->
    d_typing Ψ exp_unit typingmode__inf typ_unit
| d_typing__infapp : forall (Ψ:denv) (e1 e2:exp) (A B C:typ),
    d_typing Ψ e1 typingmode__inf A ->
    d_infabs Ψ A B C ->
    d_typing Ψ e2 typingmode__chk B ->
    d_typing Ψ  ( (exp_app e1 e2) ) typingmode__inf C
| d_typing__inftabs : forall (L:vars) (Ψ:denv) (e:exp) (A:typ),
    d_wf_typ Ψ (typ_all A) ->
    ( forall X , X \notin  L  -> d_typing  ( X ~ dbind_tvar_empty  ++  Ψ ) (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) )  ( open_typ_wrt_typ A (typ_var_f X) ) ) typingmode__chk ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
    d_typing Ψ (exp_tabs (body_anno e A)) typingmode__inf (typ_all A)
| d_typing__inftapp : forall (Ψ:denv) (e1:exp) (A B C:typ),
    d_wf_typ Ψ B ->
    d_typing Ψ e1 typingmode__inf A ->
    d_inftapp Ψ A B C ->
    d_typing Ψ (exp_tapp e1 B) typingmode__inf C
| d_typing__chkabstop : forall (L:vars) (Ψ:denv) (e:exp),
    ( forall x , x \notin  L  -> d_typing  ( x ~ (dbind_typ typ_bot)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk typ_top )  ->
    d_typing Ψ (exp_abs e) typingmode__chk typ_top
| d_typing__chkabs : forall (L:vars) (Ψ:denv) (e:exp) (A1 A2:typ),
    d_wf_typ Ψ A1 ->
    ( forall x , x \notin  L  -> d_typing  ( x ~ (dbind_typ A1)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk A2 )  ->
    d_typing Ψ (exp_abs e) typingmode__chk (typ_arrow A1 A2)
(* | d_typing__chkall : forall (L:vars) (Ψ:denv) (e:exp) (T1:typ),
    d_wf_typ Ψ (typ_all T1) ->
    ( forall X , X \notin  L  -> d_typing  ( X ~ dbind_tvar_empty  ++  Ψ )  e  typingmode__chk ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
    d_typing Ψ e typingmode__chk (typ_all T1) *)
| d_typing__chksub : forall (Ψ:denv) (e:exp) (A B:typ),
    d_typing Ψ e typingmode__inf B ->
    d_sub Ψ B A ->
    d_typing Ψ e typingmode__chk A
| d_typing__chkintersection : forall (Ψ:denv) (e:exp) (A1 A2:typ),
    d_typing Ψ e typingmode__chk A1 ->
    d_typing Ψ e typingmode__chk A2 ->
    d_typing Ψ e typingmode__chk (typ_intersection A1 A2)
| d_typing__chkunion1 : forall (Ψ:denv) (e:exp) (A1 A2:typ),
    d_typing Ψ e typingmode__chk A1 ->
    d_wf_typ Ψ A2 ->
    d_typing Ψ e typingmode__chk (typ_union A1 A2)
| d_typing__chkunion2 : forall (Ψ:denv) (e:exp) (A1 A2:typ),
    d_typing Ψ e typingmode__chk A2 ->
    d_wf_typ Ψ A1 ->
    d_typing Ψ e typingmode__chk (typ_union A1 A2)
.
