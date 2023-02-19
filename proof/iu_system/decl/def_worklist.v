Require Import Program.Equality.

Require Import decl.notations.


Fixpoint dwl_app (Γ1 Γ2 : dworklist) :=
  match Γ1 with 
  | dworklist_empty => Γ2 
  | dworklist_constvar Γ1' X b => dworklist_constvar (dwl_app Γ1' Γ2) X b
  | dworklist_consstvar Γ1' SX b => dworklist_consstvar (dwl_app Γ1' Γ2) SX b
  | dworklist_consvar Γ1' x b => dworklist_consvar (dwl_app Γ1' Γ2) x b
  | dworklist_conswork Γ1' w => dworklist_conswork (dwl_app Γ1' Γ2) w
  end.


(* TODO : check *)
Inductive apply_dcont : dcont -> dtyp -> dworklist -> Prop :=
  | applydcont_done : forall T1,  
      apply_dcont dcont_done T1 dworklist_empty
  | applydcont_app : forall T1 e c,
      apply_dcont (dcont_app e c) T1 (dworklist_conswork dworklist_empty (dwork_infapp T1 e c))
  | applydcont_tapp : forall T1 T2 c,
      apply_dcont (dcont_tapp T2 c) T1 (dworklist_conswork dworklist_empty (dwork_inftapp T1 T2 c))
  | applydcont_sub : forall T1 S1,
      apply_dcont (dcont_sub S1) T1 (dworklist_conswork dworklist_empty (dwork_sub T1 S1))
.

(* TODO : check *)
(* decl worklist delegated reduction, corresponds to Jimmy's dc *)
Inductive dwl_del_red : dworklist -> Prop :=
  | dwldelred_empty : dwl_del_red dworklist_empty
  | dwldelred_inf : forall Γ e T c,
      dtyping (dwl_to_denv Γ) e dtypingmode_inf T ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c T)) ->
      dwl_del_red (dworklist_conswork Γ (dwork_infer e c))
  | dwldelred_chk : forall Γ e T,
      dtyping (dwl_to_denv Γ) e dtypingmode_chk T ->
      dwl_del_red Γ ->
      dwl_del_red (dworklist_conswork Γ (dwork_check e T))
  | dwldelred_infapp : forall Γ e T1 T2 c,
      dtyping (dwl_to_denv Γ) e (dtypingmode_infapp T1) T2 ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c T1)) ->
      dwl_del_red (dworklist_conswork Γ (dwork_infapp T2 e c))
  | dwldelred_inftappall : forall Γ T T1 c,
      dwl_del_red (dworklist_conswork Γ (dwork_apply c (open_dtyp_wrt_dtyp T1 T))) -> 
      dwl_del_red (dworklist_conswork Γ (dwork_inftapp (dtyp_all T1) T c))
  | dwldelred_inftappbot : forall Γ T c,
      dwl_del_red (dworklist_conswork Γ (dwork_apply c dtyp_bot)) -> 
      dwl_del_red (dworklist_conswork Γ (dwork_inftapp dtyp_bot T c))
  | dwldelred_sub : forall Γ S T,
      dsub (dwl_to_denv Γ) S T ->
      dwl_del_red Γ ->
      dwl_del_red (dworklist_conswork Γ (dwork_sub S T))
  | dwldelred_applycont : forall Γ c T Γ',
      apply_dcont c T Γ' ->
      dwl_del_red (dwl_app Γ' Γ) ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c T))
  .

(* defns Jdworklist_reduction *)
Inductive dwl_red : dworklist -> Prop :=    (* defn dwl_red *)
 | dwlred_subtop : forall (W:dworklist) (S:dtyp),
     dwl_red W ->
     dwf_typ  ( dwl_to_denv  W  )  S ->
     dwl_red (dworklist_conswork W (dwork_sub S dtyp_top))
 | dwlred_subbot : forall (W:dworklist) (T:dtyp),
     dwl_red W ->
     dwf_typ  ( dwl_to_denv  W  )  T ->
     dwl_red (dworklist_conswork W (dwork_sub dtyp_bot T))
 | dwlred_subunit : forall (W:dworklist),
     dwl_red W ->
     dwl_red (dworklist_conswork W (dwork_sub dtyp_unit dtyp_unit))
 | dwlred_subtvar : forall (W:dworklist) (X:typvar),
     dwl_red W ->
     dwf_typ  ( dwl_to_denv  W  )  (dtyp_var_f X) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_var_f X) (dtyp_var_f X)))
 | dwlred_substvar : forall (W:dworklist) (SX:stypvar),
     dwl_red W ->
     dwf_typ  ( dwl_to_denv  W  )  (dtyp_svar SX) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_svar SX) (dtyp_svar SX)))
 | dwlred_subarrow : forall (W:dworklist) (S1 S2 T1 T2:dtyp),
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_sub T1 S1)) (dwork_sub S2 T2)) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)))
 | dwlred_suball : forall (L:vars) (W:dworklist) (S1 T1:dtyp),
     ( forall SX , SX `notin` L -> dwl_red (dworklist_conswork (dworklist_consstvar W SX dbind_stvar_empty) (dwork_sub  (open_dtyp_wrt_dtyp  S1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  T1   (dtyp_svar SX) ) ))) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_all S1) (dtyp_all T1)))
 | dwlred_suballl : forall (W:dworklist) (S1 T1 T2:dtyp),
     dneq_union T1 ->
     dneq_intersection T1 ->
     dneq_all T1 ->
     dmono_typ T2 ->
     dwf_typ  ( dwl_to_denv  W  )  T2 ->
     dwl_red (dworklist_conswork W (dwork_sub  (open_dtyp_wrt_dtyp  S1   T2 )  T1)) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_all S1) T1))
 | dwlred_subintersection1 : forall (W:dworklist) (S1 T1 T2:dtyp),
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_sub S1 T1)) (dwork_sub S1 T2)) ->
     dwl_red (dworklist_conswork W (dwork_sub S1 (dtyp_intersection T1 T2)))
 | dwlred_subintersection2 : forall (W:dworklist) (S1 S2 T:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  S2 ->
     dwl_red (dworklist_conswork W (dwork_sub S1 T)) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_intersection S1 S2) T))
 | dwlred_subintersection3 : forall (W:dworklist) (S1 S2 T:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  S1 ->
     dwl_red (dworklist_conswork W (dwork_sub S2 T)) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_intersection S1 S2) T))
 | dwlred_subunion1 : forall (W:dworklist) (S1 T1 T2:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  T2 ->
     dwl_red (dworklist_conswork W (dwork_sub S1 T1)) ->
     dwl_red (dworklist_conswork W (dwork_sub S1 (dtyp_union T1 T2)))
 | dwlred_subunion2 : forall (W:dworklist) (S1 T1 T2:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  T1 ->
     dwl_red (dworklist_conswork W (dwork_sub S1 T2)) ->
     dwl_red (dworklist_conswork W (dwork_sub S1 (dtyp_union T1 T2)))
 | dwlred_subunion3 : forall (W:dworklist) (S1 S2 T1:dtyp),
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_sub S1 T1)) (dwork_sub S2 T1)) ->
     dwl_red (dworklist_conswork W (dwork_sub (dtyp_union S1 S2) T1))
 | dwlred_chksub : forall (W:dworklist) (e:dexp) (T1:dtyp),
     dneq_abs e ->
      ~ ( T1  = dtyp_top)  ->
     dneq_all T1 ->
     dwl_red (dworklist_conswork W (dwork_infer e (dcont_sub T1))) ->
     dwl_red (dworklist_conswork W (dwork_check e T1))
 | dwlred_chkall : forall (L:vars) (W:dworklist) (e:dexp) (T1:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  (dtyp_all T1) ->
      ( forall X , X \notin  L  -> dwl_red (dworklist_conswork (dworklist_constvar W X dbind_tvar_empty) (dwork_check e  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) )) )  ->
     dwl_red (dworklist_conswork W (dwork_check e (dtyp_all T1)))
 | dwlred_chkabsarrow : forall (L:vars) (W:dworklist) (e:dexp) (S1 T1:dtyp),
      ( forall x , x \notin  L  -> dwl_red (dworklist_conswork (dworklist_consvar W x (dbind_typ S1)) (dwork_check  ( open_dexp_wrt_dexp e (dexp_var_f x) )  T1)) )  ->
     dwl_red (dworklist_conswork W (dwork_check (dexp_abs e) (dtyp_arrow S1 T1)))
 | dwlred_chkabstop : forall (L:vars) (W:dworklist) (e:dexp),
      ( forall x , x \notin  L  -> dwl_red (dworklist_conswork (dworklist_consvar W x (dbind_typ dtyp_bot)) (dwork_check  ( open_dexp_wrt_dexp e (dexp_var_f x) )  dtyp_top)) )  ->
     dwl_red (dworklist_conswork W (dwork_check (dexp_abs e) dtyp_top))
 | dwlred_chkintersection : forall (W:dworklist) (e:dexp) (T1 T2:dtyp),
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_check e T1)) (dwork_check e T2)) ->
     dwl_red (dworklist_conswork W (dwork_check e (dtyp_intersection T1 T2)))
 | dwlred_chkunion1 : forall (W:dworklist) (e:dexp) (T1 T2:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  T2 ->
     dwl_red (dworklist_conswork W (dwork_check e T1)) ->
     dwl_red (dworklist_conswork W (dwork_check e (dtyp_union T1 T2)))
 | dwlred_chkunion2 : forall (W:dworklist) (e:dexp) (T1 T2:dtyp),
     dwf_typ  ( dwl_to_denv  W  )  T1 ->
     dwl_red (dworklist_conswork W (dwork_check e T2)) ->
     dwl_red (dworklist_conswork W (dwork_check e (dtyp_union T1 T2)))
 | dwlred_infvar : forall (W:dworklist) (x:expvar) (c:dcont) (T:dtyp),
      binds ( x )  ( (dbind_typ T) ) (  ( dwl_to_denv  W  )  )  ->
     dwl_red (dworklist_conswork W (dwork_apply c T)) ->
     dwl_red (dworklist_conswork W (dwork_infer (dexp_var_f x) c))
 | dwlred_infanno : forall (W:dworklist) (e:dexp) (T:dtyp) (c:dcont),
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_apply c T)) (dwork_check e T)) ->
     dwl_red (dworklist_conswork W (dwork_infer  ( (dexp_anno e T) )  c))
 | dwlred_inftabs : forall (L:vars) (W:dworklist) (e:dexp) (T:dtyp) (c:dcont),
     dwf_typ  ( dwl_to_denv  W  )  (dtyp_all T) ->
      ( forall X , X \notin  L  -> dwl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork W (dwork_apply c  ( (dtyp_all T) ) )) X dbind_tvar_empty) (dwork_check  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )   ( open_dtyp_wrt_dtyp T (dtyp_var_f X) ) )) )  ->
     dwl_red (dworklist_conswork W (dwork_infer (dexp_tabs (dbody_anno e T)) c))
 | dwlred_infunit : forall (W:dworklist) (c:dcont),
     dwl_red (dworklist_conswork W (dwork_apply c dtyp_unit)) ->
     dwl_red (dworklist_conswork W (dwork_infer dexp_unit c))
 | dwlred_infapp : forall (W:dworklist) (e1 e2:dexp) (c:dcont),
     dwl_red (dworklist_conswork W (dwork_infer e1 (dcont_app e2 c))) ->
     dwl_red (dworklist_conswork W (dwork_infer  ( (dexp_app e1 e2) )  c))
 | dwlred_inftapp : forall (W:dworklist) (e:dexp) (T:dtyp) (c:dcont),
     dwf_typ  ( dwl_to_denv  W  )  T ->
     dwl_red (dworklist_conswork W (dwork_infer e (dcont_tapp T c))) ->
     dwl_red (dworklist_conswork W (dwork_infer (dexp_tapp e T) c))
 | dwlred_inftappall : forall (W:dworklist) (T1 T2:dtyp) (c:dcont),
     dwf_typ  ( dwl_to_denv  W  )  (dtyp_all T1) ->
     dwl_red (dworklist_conswork W (dwork_apply c  (open_dtyp_wrt_dtyp  T1   T2 ) )) ->
     dwl_red (dworklist_conswork W (dwork_inftapp (dtyp_all T1) T2 c))
 | dwlred_inftappbot : forall (W:dworklist) (T:dtyp) (c:dcont),
     lc_dtyp T ->
     dwl_red (dworklist_conswork W (dwork_apply c dtyp_bot)) ->
     dwl_red (dworklist_conswork W (dwork_inftapp dtyp_bot T c))
 | dwlred_infapparrow : forall (W:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     dwf_typ  ( dwl_to_denv  W  )  T2 ->
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_apply c T2)) (dwork_check e T1)) ->
     dwl_red (dworklist_conswork W (dwork_infapp (dtyp_arrow T1 T2) e c))
 | dwlred_infappbot : forall (W:dworklist) (e:dexp) (c:dcont),
     lc_dexp e ->
     dwl_red (dworklist_conswork W (dwork_apply c dtyp_bot)) ->
     dwl_red (dworklist_conswork W (dwork_infapp dtyp_bot e c))
 | dwlred_infappintersection1 : forall (W:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     lc_dtyp T2 ->
     dwl_red (dworklist_conswork W (dwork_infapp T1 e c)) ->
     dwl_red (dworklist_conswork W (dwork_infapp (dtyp_intersection T1 T2) e c))
 | dwlred_infappintersection2 : forall (W:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     lc_dtyp T1 ->
     dwl_red (dworklist_conswork W (dwork_infapp T2 e c)) ->
     dwl_red (dworklist_conswork W (dwork_infapp (dtyp_intersection T1 T2) e c))
 | dwlred_infappunion : forall (W:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     dwl_red (dworklist_conswork (dworklist_conswork W (dwork_infapp T1 e c)) (dwork_infapp T2 e c)) ->
     dwl_red (dworklist_conswork W (dwork_infapp (dtyp_union T1 T2) e c))
 | dwlred_applycont : forall (W W':dworklist) (T:dtyp) (c:dcont),
     apply_dcont c T W' ->
     dwl_red (dwl_app W' W) ->
     dwl_red (dworklist_conswork W (dwork_apply c T))
.
