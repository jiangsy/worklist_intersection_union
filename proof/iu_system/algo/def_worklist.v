Require Import Metalib.Metatheory.

Require Import algo.def_ott.

Inductive a_wl_red : a_worklist -> Prop :=    (* defn a_wl_red *)
 | a_wlred_subtop : forall (W:a_worklist) (S1:a_typ),
     a_wl_red W ->
     a_wf_typ W S1 ->
     a_wl_red (a_wl_consw W (a_work_sub S1 a_typ_top))
 | a_wlred_subbot : forall (W:a_worklist) (T:a_typ),
     a_wl_red W ->
     a_wf_typ W T ->
     a_wl_red (a_wl_consw W (a_work_sub a_typ_bot T))
 | a_wlred_subunit : forall (W:a_worklist),
     a_wl_red W ->
     a_wl_red (a_wl_consw W (a_work_sub a_typ_unit a_typ_unit))
 | a_wlred_subtvar : forall (W:a_worklist) (X:typvar),
     a_wl_red W ->
     a_wf_typ W (a_typ_tvar_f X) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_tvar_f X) (a_typ_tvar_f X)))
 | a_wlred_subevar : forall (W:a_worklist) (EX:etypvar),
     a_wl_red W ->
     a_wf_typ W (a_typ_etvar EX) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_etvar EX) (a_typ_etvar EX)))
 | a_wlred_subarrow : forall (W:a_worklist) (S1 S2 T1 T2:a_typ),
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_sub T1 S1)) (a_work_sub S2 T2)) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_arrow S1 S2) (a_typ_arrow T1 T2)))
 | a_wlred_suballl : forall (L:vars) (W:a_worklist) (S1 T1:a_typ) (EX:etypvar),
      ~ ( T1  = a_typ_top)  ->
     a_typ_neq_all T1 ->
     a_typ_neq_intersection T1 ->
     a_typ_neq_union T1 ->
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ S1 (a_typ_tvar_f X) )  )  ->
     a_wl_red (a_wl_consw (a_wl_consetvar W EX (a_bind_bound a_typ_bot a_typ_top)) (a_work_sub  (open_a_typ_wrt_a_typ  S1   (a_typ_etvar EX) )  T1)) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_all S1) T1))
 | a_wlred_suball : forall (L:vars) (W:a_worklist) (S1 T1:a_typ) (SX:stypvar),
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ S1 (a_typ_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X) )  )  ->
     a_wl_red (a_wl_consw (a_wl_consstvar W SX a_bind_stvarempty) (a_work_sub  (open_a_typ_wrt_a_typ  S1   (a_typ_stvar SX) )   (open_a_typ_wrt_a_typ  T1   (a_typ_stvar SX) ) )) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_all S1) (a_typ_all T1)))
 | a_wlred_subarrowr : forall (W:a_worklist) (EX:etypvar) (T1 T2:a_typ) (EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      ( a_smono_typ   ( (a_typ_arrow T1 T2) )   -> False )  ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_upper  W2   W3 )  ->
     a_wl_red (a_wl_consw  (  ( a_wl_app  W3   W2  )  )  (a_work_sub (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2)) (a_typ_arrow T1 T2))) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_etvar EX) (a_typ_arrow T1 T2)))
 | a_wlred_subarrowl : forall (W:a_worklist) (T1 T2:a_typ) (EX EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      ( a_smono_typ   ( (a_typ_arrow T1 T2) )   -> False )  ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_lower  W2   W3 )  ->
     a_wl_red (a_wl_consw  (  ( a_wl_app  W3   W2  )  )  (a_work_sub (a_typ_arrow T1 T2) (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2)))) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_arrow T1 T2) (a_typ_etvar EX)))
 | a_wlred_subetvarr : forall (W:a_worklist) (EY EX:etypvar) (W2 W3:a_worklist) (E:a_env),
      (a_add_to_bound_and_reorder  W   E   EX   (a_typ_etvar EY)  a_modeab_lower  W2   W3 )  ->
     a_evs_in_wl W EX EY ->
     a_wl_red  (  ( a_wl_app  W3   W2  )  )  ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_etvar EY) (a_typ_etvar EX)))
 | a_wlred_subetvarl : forall (W:a_worklist) (EX EY:etypvar) (W2 W3:a_worklist) (E:a_env),
      (a_add_to_bound_and_reorder  W   E   EX   (a_typ_etvar EY)  a_modeab_upper  W2   W3 )  ->
     a_evs_in_wl W EX EY ->
     a_wl_red  (  ( a_wl_app  W3   W2  )  )  ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_etvar EX) (a_typ_etvar EY)))
 | a_wlred_subetvarmonol : forall (W:a_worklist) (S1:a_typ) (EX:etypvar) (W2 W3:a_worklist) (E:a_env),
     a_smono_typ S1 ->
      (a_add_to_bound_and_reorder  W   E   EX   S1  a_modeab_lower  W2   W3 )  ->
     a_wl_red  (  ( a_wl_app  W3   W2  )  )  ->
     a_wl_red (a_wl_consw W (a_work_sub S1 (a_typ_etvar EX)))
 | a_wlred_subetvarmonor : forall (W:a_worklist) (EX:etypvar) (T1:a_typ) (W2 W3:a_worklist) (E:a_env),
     a_smono_typ T1 ->
      (a_add_to_bound_and_reorder  W   E   EX   T1  a_modeab_upper  W2   W3 )  ->
     a_wl_red  (  ( a_wl_app  W3   W2  )  )  ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_etvar EX) T1))
 | a_wlred_subintersection1 : forall (W:a_worklist) (S1 T1 T2:a_typ),
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_sub S1 T1)) (a_work_sub S1 T2)) ->
     a_wl_red (a_wl_consw W (a_work_sub S1 (a_typ_intersection T1 T2)))
 | a_wlred_subintersection2 : forall (W:a_worklist) (S1 S2 T:a_typ),
     a_wf_typ W S2 ->
     a_wl_red (a_wl_consw W (a_work_sub S1 T)) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_intersection S1 S2) T))
 | a_wlred_subintersection3 : forall (W:a_worklist) (S1 S2 T:a_typ),
     a_wf_typ W S1 ->
     a_wl_red (a_wl_consw W (a_work_sub S2 T)) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_intersection S1 S2) T))
 | a_wlred_subunion1 : forall (W:a_worklist) (S1 T1 T2:a_typ),
     a_wf_typ W T2 ->
     a_wl_red (a_wl_consw W (a_work_sub S1 T1)) ->
     a_wl_red (a_wl_consw W (a_work_sub S1 (a_typ_union T1 T2)))
 | a_wlred_subunion2 : forall (W:a_worklist) (S1 T1 T2:a_typ),
     a_wf_typ W T1 ->
     a_wl_red (a_wl_consw W (a_work_sub S1 T2)) ->
     a_wl_red (a_wl_consw W (a_work_sub S1 (a_typ_union T1 T2)))
 | a_wlred_subunion3 : forall (W:a_worklist) (S1 S2 T1:a_typ),
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_sub S1 T1)) (a_work_sub S2 T1)) ->
     a_wl_red (a_wl_consw W (a_work_sub (a_typ_union S1 S2) T1))
 | a_wlred_chksub : forall (W:a_worklist) (e:a_exp) (T1:a_typ),
     da_exp_neq_abs e ->
      ~ ( T1  = a_typ_top)  ->
     a_typ_neq_all T1 ->
     a_typ_neq_intersection T1 ->
     a_typ_neq_union T1 ->
     a_wl_red (a_wl_consw W (a_work_infer e (a_cont_sub T1))) ->
     a_wl_red (a_wl_consw W (a_work_check e T1))
 | a_wlred_chkall : forall (L:vars) (W:a_worklist) (e:a_exp) (T1:a_typ),
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> a_wl_red (a_wl_consw (a_wl_constvar W X a_bind_tvarempty) (a_work_check e  ( open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X) ) )) )  ->
     a_wl_red (a_wl_consw W (a_work_check e (a_typ_all T1)))
 | a_wlred_chkabsarrow : forall (L:vars) (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
      ( forall x , x \notin  L  -> a_wl_red (a_wl_consw (a_wl_consvar W x (a_bind_typ T1)) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  T2)) )  ->
     a_wl_red (a_wl_consw W (a_work_check (a_exp_abs e) (a_typ_arrow T1 T2)))
 | a_wlred_chkabsevar : forall (L:vars) (W:a_worklist) (e:a_exp) (EX EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_both  W2   W3 )  ->
      ( forall x , x \notin  L  -> a_wl_red (a_wl_consw (a_wl_consvar  (  ( a_wl_app  W3   W2  )  )  x (a_bind_typ (a_typ_etvar EX1))) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  (a_typ_etvar EX2))) )  ->
     a_wl_red (a_wl_consw W (a_work_check (a_exp_abs e) (a_typ_etvar EX)))
 | a_wlred_chkabstop : forall (L:vars) (W:a_worklist) (e:a_exp),
      ( forall x , x \notin  L  -> a_wl_red (a_wl_consw (a_wl_consvar W x (a_bind_typ a_typ_bot)) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  a_typ_top)) )  ->
     a_wl_red (a_wl_consw W (a_work_check (a_exp_abs e) a_typ_top))
 | a_wlred_chkintersection : forall (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_check e T1)) (a_work_check e T2)) ->
     a_wl_red (a_wl_consw W (a_work_check e (a_typ_intersection T1 T2)))
 | a_wlred_chkunion1 : forall (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
     a_wf_typ W T2 ->
     a_wl_red (a_wl_consw W (a_work_check e T1)) ->
     a_wl_red (a_wl_consw W (a_work_check e (a_typ_union T1 T2)))
 | a_wlred_chkunion2 : forall (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
     a_wf_typ W T1 ->
     a_wl_red (a_wl_consw W (a_work_check e T2)) ->
     a_wl_red (a_wl_consw W (a_work_check e (a_typ_union T1 T2)))
 | a_wlred_infvar : forall (W:a_worklist) (x:expvar) (c:a_cont) (T:a_typ),
      binds ( x )  ( (a_bind_typ T) ) (  ( a_wl_to_env  W  )  )  ->
     a_wl_red (a_wl_consw W (a_work_apply c T)) ->
     a_wl_red (a_wl_consw W (a_work_infer (a_exp_var_f x) c))
 | a_wlred_infanno : forall (W:a_worklist) (e:a_exp) (T:a_typ) (c:a_cont),
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_apply c T)) (a_work_check e T)) ->
     a_wl_red (a_wl_consw W (a_work_infer  ( (a_exp_anno e T) )  c))
 | a_wlred_inftabs : forall (L:vars) (W:a_worklist) (e:a_exp) (T:a_typ) (c:a_cont),
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ T (a_typ_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> a_wl_red (a_wl_consw (a_wl_constvar (a_wl_consw W (a_work_apply c  ( (a_typ_all T) ) )) X a_bind_tvarempty) (a_work_check  ( open_a_exp_wrt_a_typ e (a_typ_tvar_f X) )   ( open_a_typ_wrt_a_typ T (a_typ_tvar_f X) ) )) )  ->
     a_wl_red (a_wl_consw W (a_work_infer (a_exp_tabs (a_body_anno e T)) c))
 | a_wlred_infunit : forall (W:a_worklist) (c:a_cont),
     a_wl_red (a_wl_consw W (a_work_apply c a_typ_unit)) ->
     a_wl_red (a_wl_consw W (a_work_infer a_exp_unit c))
 | a_wlred_infapp : forall (W:a_worklist) (e1 e2:a_exp) (c:a_cont),
     a_wl_red (a_wl_consw W (a_work_infer e1 (a_cont_app e2 c))) ->
     a_wl_red (a_wl_consw W (a_work_infer  ( (a_exp_app e1 e2) )  c))
 | a_wlred_inftapp : forall (W:a_worklist) (e:a_exp) (T:a_typ) (c:a_cont),
     a_wf_typ W T ->
     a_wl_red (a_wl_consw W (a_work_infer e (a_cont_tapp T c))) ->
     a_wl_red (a_wl_consw W (a_work_infer (a_exp_tapp e T) c))
 | a_wlred_inftappall : forall (W:a_worklist) (T1 T2:a_typ) (c:a_cont),
     a_wf_typ W (a_typ_all T1) ->
     a_wl_red (a_wl_consw W (a_work_apply c  (open_a_typ_wrt_a_typ  T1   T2 ) )) ->
     a_wl_red (a_wl_consw W (a_work_inftapp (a_typ_all T1) T2 c))
 | a_wlred_inftappbot : forall (W:a_worklist) (T:a_typ) (c:a_cont),
     a_wf_typ W T ->
     a_wl_red (a_wl_consw W (a_work_apply c a_typ_bot)) ->
     a_wl_red (a_wl_consw W (a_work_inftapp a_typ_bot T c))
 | a_wlred_infapparrow : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
     a_wf_typ W T2 ->
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_apply c T2)) (a_work_check e T1)) ->
     a_wl_red (a_wl_consw W (a_work_infapp (a_typ_arrow T1 T2) e c))
 | a_wlred_infappevar : forall (W:a_worklist) (EX:etypvar) (e:a_exp) (c:a_cont) (EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_both  W2   W3 )  ->
     a_wl_red (a_wl_consw  (  ( a_wl_app  W3   W2  )  )  (a_work_infapp (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2)) e c)) ->
     a_wl_red (a_wl_consw W (a_work_infapp (a_typ_etvar EX) e c))
 | a_wlred_infappbot : forall (W:a_worklist) (e:a_exp) (c:a_cont),
     lc_a_exp e ->
     a_wl_red (a_wl_consw W (a_work_apply c a_typ_bot)) ->
     a_wl_red (a_wl_consw W (a_work_infapp a_typ_bot e c))
 | a_wlred_infappinter1 : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
     a_wf_typ W T2 ->
     a_wl_red (a_wl_consw W (a_work_infapp T1 e c)) ->
     a_wl_red (a_wl_consw W (a_work_infapp (a_typ_intersection T1 T2) e c))
 | a_wlred_infappinter2 : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
     a_wf_typ W T1 ->
     a_wl_red (a_wl_consw W (a_work_infapp T2 e c)) ->
     a_wl_red (a_wl_consw W (a_work_infapp (a_typ_intersection T1 T2) e c))
 | a_wlred_infappunion : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
     a_wl_red (a_wl_consw (a_wl_consw W (a_work_infapp T1 e c)) (a_work_infapp T2 e c)) ->
     a_wl_red (a_wl_consw W (a_work_infapp (a_typ_union T1 T2) e c)).


Inductive a_wl_red' : a_worklist -> Prop :=    (* defn a_wl_red' *)
  | a_wlred_subtop' : forall (W:a_worklist) (S1:a_typ),
      a_wl_red' W ->
      a_wf_typ W S1 ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 a_typ_top))
  | a_wlred_subbot' : forall (W:a_worklist) (T:a_typ),
      a_wl_red' W ->
      a_wf_typ W T ->
      a_wl_red' (a_wl_consw W (a_work_sub a_typ_bot T))
  | a_wlred_subunit' : forall (W:a_worklist),
      a_wl_red' W ->
      a_wl_red' (a_wl_consw W (a_work_sub a_typ_unit a_typ_unit))
  | a_wlred_subtvar' : forall (W:a_worklist) (X:typvar),
      a_wl_red' W ->
      a_wf_typ W (a_typ_tvar_f X) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_tvar_f X) (a_typ_tvar_f X)))
  | a_wlred_subevar' : forall (W:a_worklist) (EX:etypvar),
      a_wl_red' W ->
      a_wf_typ W (a_typ_etvar EX) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_etvar EX) (a_typ_etvar EX)))
  | a_wlred_subarrow' : forall (W:a_worklist) (S1 S2 T1 T2:a_typ),
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_sub T1 S1)) (a_work_sub S2 T2)) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_arrow S1 S2) (a_typ_arrow T1 T2)))
  | a_wlred_suballl' : forall (L:vars) (W:a_worklist) (S1 T1:a_typ),
      ~ ( T1  = a_typ_top)  ->
      a_typ_neq_all T1 ->
      ( forall EX , EX \notin  L  -> a_etvar_strongin EX  ( open_a_typ_wrt_a_typ S1 (a_typ_etvar EX) )  )  ->
      ( forall EX , EX \notin  L  ->  a_wl_red' (a_wl_consw (a_wl_consetvar W EX (a_bind_bound a_typ_bot a_typ_top)) (a_work_sub  (open_a_typ_wrt_a_typ  S1   (a_typ_etvar EX) )  T1)) ) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_all S1) T1))
  | a_wlred_suball' : forall (L:vars) (W:a_worklist) (S1 T1:a_typ),
      ( forall SX , SX \notin  L  -> a_stvar_strongin SX  ( open_a_typ_wrt_a_typ S1 (a_typ_stvar SX) )  )  ->
      ( forall SX , SX \notin  L  -> a_stvar_strongin SX  ( open_a_typ_wrt_a_typ T1 (a_typ_stvar SX) )  )  ->
      ( forall SX , SX \notin  L  -> a_wl_red' (a_wl_consw (a_wl_consstvar W SX a_bind_stvarempty) (a_work_sub  (open_a_typ_wrt_a_typ  S1   (a_typ_stvar SX) )   (open_a_typ_wrt_a_typ  T1   (a_typ_stvar SX) ) ))) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_all S1) (a_typ_all T1)))
  | a_wlred_subarrowr' : forall (W:a_worklist) (EX:etypvar) (T1 T2:a_typ) (EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      EX1 `notin` (dom (a_wl_to_env W)) ->
      EX2 `notin` (dom (a_wl_to_env W) `union` singleton EX1) ->
      ( a_smono_typ   ( (a_typ_arrow T1 T2) )   -> False )  ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_upper  W2   W3 )  ->
      a_wl_red' (a_wl_consw  (  ( a_wl_app  W3   W2  )  )  (a_work_sub (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2)) (a_typ_arrow T1 T2))) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_etvar EX) (a_typ_arrow T1 T2)))
  | a_wlred_subarrowl' : forall (W:a_worklist) (T1 T2:a_typ) (EX EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      EX1 `notin` (dom (a_wl_to_env W)) ->
      EX2 `notin` (dom (a_wl_to_env W) `union` singleton EX1) ->
      ( a_smono_typ   ( (a_typ_arrow T1 T2) )   -> False )  ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_lower  W2   W3 )  ->
      a_wl_red' (a_wl_consw  (  ( a_wl_app  W3   W2  )  )  (a_work_sub (a_typ_arrow T1 T2) (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2)))) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_arrow T1 T2) (a_typ_etvar EX)))
  | a_wlred_subetvarr' : forall (W:a_worklist) (EY EX:etypvar) (W2 W3:a_worklist) (E:a_env),
      (a_add_to_bound_and_reorder  W   E   EX   (a_typ_etvar EY)  a_modeab_lower  W2   W3 )  ->
      a_evs_in_wl W EX EY ->
      a_wl_red'  (  ( a_wl_app  W3   W2  )  )  ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_etvar EY) (a_typ_etvar EX)))
  | a_wlred_subetvarl' : forall (W:a_worklist) (EX EY:etypvar) (W2 W3:a_worklist) (E:a_env),
      a_evs_in_wl W EX EY ->
      (a_add_to_bound_and_reorder  W   E   EX   (a_typ_etvar EY)  a_modeab_upper  W2   W3 )  ->
      a_wl_red'  (  ( a_wl_app  W3   W2  )  )  ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_etvar EX) (a_typ_etvar EY)))
  | a_wlred_subetvarmonol' : forall (W:a_worklist) (S1:a_typ) (EX:etypvar) (W2 W3:a_worklist) (E:a_env),
      a_smono_typ S1 ->
      (a_add_to_bound_and_reorder  W   E   EX   S1  a_modeab_lower  W2   W3 )  ->
      a_wl_red'  (  ( a_wl_app  W3   W2  )  )  ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 (a_typ_etvar EX)))
  | a_wlred_subetvarmonor' : forall (W:a_worklist) (EX:etypvar) (T1:a_typ) (W2 W3:a_worklist) (E:a_env),
      a_smono_typ T1 ->
      (a_add_to_bound_and_reorder  W   E   EX   T1  a_modeab_upper  W2   W3 )  ->
      a_wl_red'  (  ( a_wl_app  W3   W2  )  )  ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_etvar EX) T1))
  | a_wlred_subintersection1' : forall (W:a_worklist) (S1 T1 T2:a_typ),
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_sub S1 T1)) (a_work_sub S1 T2)) ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 (a_typ_intersection T1 T2)))
  | a_wlred_subintersection2' : forall (W:a_worklist) (S1 S2 T:a_typ),
      a_wf_typ W S2 ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 T)) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_intersection S1 S2) T))
  | a_wlred_subintersection3' : forall (W:a_worklist) (S1 S2 T:a_typ),
      a_wf_typ W S1 ->
      a_wl_red' (a_wl_consw W (a_work_sub S2 T)) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_intersection S1 S2) T))
  | a_wlred_subunion1' : forall (W:a_worklist) (S1 T1 T2:a_typ),
      a_wf_typ W T2 ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 T1)) ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 (a_typ_union T1 T2)))
  | a_wlred_subunion2' : forall (W:a_worklist) (S1 T1 T2:a_typ),
      a_wf_typ W T1 ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 T2)) ->
      a_wl_red' (a_wl_consw W (a_work_sub S1 (a_typ_union T1 T2)))
  | a_wlred_subunion3' : forall (W:a_worklist) (S1 S2 T1:a_typ),
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_sub S1 T1)) (a_work_sub S2 T1)) ->
      a_wl_red' (a_wl_consw W (a_work_sub (a_typ_union S1 S2) T1))
  | a_wlred_chksub' : forall (W:a_worklist) (e:a_exp) (T1:a_typ),
      da_exp_neq_abs e ->
      ~ ( T1  = a_typ_top)  ->
      a_typ_neq_all T1 ->
      a_typ_neq_intersection T1 ->
      a_typ_neq_union T1 ->
      a_wl_red' (a_wl_consw W (a_work_infer e (a_cont_sub T1))) ->
      a_wl_red' (a_wl_consw W (a_work_check e T1))
  | a_wlred_chkall' : forall (L:vars) (W:a_worklist) (e:a_exp) (T1:a_typ),
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> a_wl_red' (a_wl_consw (a_wl_constvar W X a_bind_tvarempty) (a_work_check e  ( open_a_typ_wrt_a_typ T1 (a_typ_tvar_f X) ) )) )  ->
      a_wl_red' (a_wl_consw W (a_work_check e (a_typ_all T1)))
  | a_wlred_chkabsarrow' : forall (L:vars) (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
      ( forall x , x \notin  L  -> a_wl_red' (a_wl_consw (a_wl_consvar W x (a_bind_typ T1)) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  T2)) )  ->
      a_wl_red' (a_wl_consw W (a_work_check (a_exp_abs e) (a_typ_arrow T1 T2)))
  | a_wlred_chkabsevar' : forall (L:vars) (W:a_worklist) (e:a_exp) (EX EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      EX1 \notin dom (a_wl_to_env W) ->
      EX2 \notin ( dom (a_wl_to_env W) `union` singleton EX1) ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_both  W2   W3 )  ->
      ( forall x , x \notin  L  -> a_wl_red' (a_wl_consw (a_wl_consvar  (  ( a_wl_app  W3   W2  )  )  x (a_bind_typ (a_typ_etvar EX1))) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  (a_typ_etvar EX2))) )  ->
      a_wl_red' (a_wl_consw W (a_work_check (a_exp_abs e) (a_typ_etvar EX)))
  | a_wlred_chkabstop' : forall (L:vars) (W:a_worklist) (e:a_exp),
      ( forall x , x \notin  L  -> a_wl_red' (a_wl_consw (a_wl_consvar W x (a_bind_typ a_typ_bot)) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  a_typ_top)) )  ->
      a_wl_red' (a_wl_consw W (a_work_check (a_exp_abs e) a_typ_top))
  | a_wlred_chkintersection' : forall (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_check e T1)) (a_work_check e T2)) ->
      a_wl_red' (a_wl_consw W (a_work_check e (a_typ_intersection T1 T2)))
  | a_wlred_chkunion1' : forall (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
      a_wf_typ W T2 ->
      a_wl_red' (a_wl_consw W (a_work_check e T1)) ->
      a_wl_red' (a_wl_consw W (a_work_check e (a_typ_union T1 T2)))
  | a_wlred_chkunion2' : forall (W:a_worklist) (e:a_exp) (T1 T2:a_typ),
      a_wf_typ W T1 ->
      a_wl_red' (a_wl_consw W (a_work_check e T2)) ->
      a_wl_red' (a_wl_consw W (a_work_check e (a_typ_union T1 T2)))
  | a_wlred_infvar' : forall (W:a_worklist) (x:expvar) (c:a_cont) (T:a_typ),
      binds ( x )  ( (a_bind_typ T) ) (  ( a_wl_to_env  W  )  )  ->
      a_wl_red' (a_wl_consw W (a_work_apply c T)) ->
      a_wl_red' (a_wl_consw W (a_work_infer (a_exp_var_f x) c))
  | a_wlred_infanno' : forall (W:a_worklist) (e:a_exp) (T:a_typ) (c:a_cont),
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_apply c T)) (a_work_check e T)) ->
      a_wl_red' (a_wl_consw W (a_work_infer  ( (a_exp_anno e T) )  c))
  | a_wlred_inftabs' : forall (L:vars) (W:a_worklist) (e:a_exp) (T:a_typ) (c:a_cont),
      ( forall X , X \notin  L  -> a_tvar_strongin X  ( open_a_typ_wrt_a_typ T (a_typ_tvar_f X) )  )  ->
      ( forall X , X \notin  L  -> a_wl_red' (a_wl_consw (a_wl_constvar (a_wl_consw W (a_work_apply c  ( (a_typ_all T) ) )) X a_bind_tvarempty) (a_work_check  ( open_a_exp_wrt_a_typ e (a_typ_tvar_f X) )   ( open_a_typ_wrt_a_typ T (a_typ_tvar_f X) ) )) )  ->
      a_wl_red' (a_wl_consw W (a_work_infer (a_exp_tabs (a_body_anno e T)) c))
  | a_wlred_infunit' : forall (W:a_worklist) (c:a_cont),
      a_wl_red' (a_wl_consw W (a_work_apply c a_typ_unit)) ->
      a_wl_red' (a_wl_consw W (a_work_infer a_exp_unit c))
  | a_wlred_infapp' : forall (W:a_worklist) (e1 e2:a_exp) (c:a_cont),
      a_wl_red' (a_wl_consw W (a_work_infer e1 (a_cont_app e2 c))) ->
      a_wl_red' (a_wl_consw W (a_work_infer  ( (a_exp_app e1 e2) )  c))
  | a_wlred_inftapp' : forall (W:a_worklist) (e:a_exp) (T:a_typ) (c:a_cont),
      a_wf_typ W T ->
      a_wl_red' (a_wl_consw W (a_work_infer e (a_cont_tapp T c))) ->
      a_wl_red' (a_wl_consw W (a_work_infer (a_exp_tapp e T) c))
  | a_wlred_inftappall' : forall (W:a_worklist) (T1 T2:a_typ) (c:a_cont),
      a_wf_typ W (a_typ_all T1) ->
      a_wl_red' (a_wl_consw W (a_work_apply c  (open_a_typ_wrt_a_typ  T1   T2 ) )) ->
      a_wl_red' (a_wl_consw W (a_work_inftapp (a_typ_all T1) T2 c))
  | a_wlred_inftappbot' : forall (W:a_worklist) (T:a_typ) (c:a_cont),
      a_wf_typ W T ->
      a_wl_red' (a_wl_consw W (a_work_apply c a_typ_bot)) ->
      a_wl_red' (a_wl_consw W (a_work_inftapp a_typ_bot T c))
  | a_wlred_infapparrow' : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
      a_wf_typ W T2 ->
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_apply c T2)) (a_work_check e T1)) ->
      a_wl_red' (a_wl_consw W (a_work_infapp (a_typ_arrow T1 T2) e c))
  | a_wlred_infappevar' : forall (W:a_worklist) (EX:etypvar) (e:a_exp) (c:a_cont) (EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      EX1 \notin dom (a_wl_to_env W) ->
      EX2 \notin ( dom (a_wl_to_env W) `union` singleton EX1) ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_both  W2   W3 )  ->
      a_wl_red' (a_wl_consw  (  ( a_wl_app  W3   W2  )  )  (a_work_infapp (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2)) e c)) ->
      a_wl_red' (a_wl_consw W (a_work_infapp (a_typ_etvar EX) e c))
  | a_wlred_infappbot' : forall (W:a_worklist) (e:a_exp) (c:a_cont),
      lc_a_exp e ->
      a_wl_red' (a_wl_consw W (a_work_apply c a_typ_bot)) ->
      a_wl_red' (a_wl_consw W (a_work_infapp a_typ_bot e c))
  | a_wlred_infappinter1' : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
      a_wf_typ W T2 ->
      a_wl_red' (a_wl_consw W (a_work_infapp T1 e c)) ->
      a_wl_red' (a_wl_consw W (a_work_infapp (a_typ_intersection T1 T2) e c))
  | a_wlred_infappinter2' : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
      a_wf_typ W T1 ->
      a_wl_red' (a_wl_consw W (a_work_infapp T2 e c)) ->
      a_wl_red' (a_wl_consw W (a_work_infapp (a_typ_intersection T1 T2) e c))
  | a_wlred_infappunion' : forall (W:a_worklist) (T1 T2:a_typ) (e:a_exp) (c:a_cont),
      a_wl_red' (a_wl_consw (a_wl_consw W (a_work_infapp T1 e c)) (a_work_infapp T2 e c)) ->
      a_wl_red' (a_wl_consw W (a_work_infapp (a_typ_union T1 T2) e c)).
  (* | a_wlred_chkabsevar' : forall (L:vars) (W:a_worklist) (e:a_exp) (EX EX1 EX2:etypvar) (W2 W3:a_worklist) (E:a_env),
      EX1 \notin dom (a_wl_to_env W) ->
      EX2 \notin ( dom (a_wl_to_env W) `union` singleton EX1) ->
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_both  W2   W3 )  ->
      ( forall x , x \notin  L  -> a_wl_red' (a_wl_consw (a_wl_consvar  (  ( a_wl_app  W3   W2  )  )  x (a_bind_typ (a_typ_etvar EX1))) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  (a_typ_etvar EX2))) )  ->
      a_wl_red' (a_wl_consw W (a_work_check (a_exp_abs e) (a_typ_etvar EX)))
  | a_wlred_chkabsevar' : forall (L L1 L2:vars) (W:a_worklist) (e:a_exp) (EX:etypvar) (E:a_env),
      (forall EX1 , EX1 \notin L1 -> forall EX2 , EX2 \notin L2 -> exists W2 W3, 
      (a_add_to_bound_and_reorder  (a_wl_consetvar (a_wl_consetvar W EX1 (a_bind_bound a_typ_bot a_typ_top)) EX2 (a_bind_bound a_typ_bot a_typ_top))   E   EX   (a_typ_arrow (a_typ_etvar EX1) (a_typ_etvar EX2))  a_modeab_both  W2   W3 )  /\
      ( forall x , x \notin  L  -> a_wl_red' (a_wl_consw (a_wl_consvar  (  ( a_wl_app  W3   W2  )  )  x (a_bind_typ (a_typ_etvar EX1))) (a_work_check  ( open_a_exp_wrt_a_exp e (a_exp_var_f x) )  (a_typ_etvar EX2))) ) ) ->
      a_wl_red' (a_wl_consw W (a_work_check (a_exp_abs e) (a_typ_etvar EX)))

       *)