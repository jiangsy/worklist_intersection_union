Require Import Program.Equality.

Require Import decl.prop_ln.
Require Export decl.def_ott.
Require Export decl.def_extra.


Fixpoint dwl_app (Γ1 Γ2 : dworklist) :=
  match Γ1 with 
  | dworklist_empty => Γ2 
  | dworklist_constvar Γ1' X b => dworklist_constvar (dwl_app Γ1' Γ2) X b
  | dworklist_consstvar Γ1' SX b => dworklist_consstvar (dwl_app Γ1' Γ2) SX b
  | dworklist_consvar Γ1' x b => dworklist_consvar (dwl_app Γ1' Γ2) x b
  | dworklist_conswork Γ1' w => dworklist_conswork (dwl_app Γ1' Γ2) w
  end.

(* TODO : check *)
Inductive d_apply_cont : dcont -> dtyp -> dworklist -> Prop :=
  (* | d__ac__done : forall T1,  
      d_apply_cont dcont_done (some T1) dworklist_empty *)
  | d__ac__infabs: forall T1 c,
      d_apply_cont (dcont_infabs c) 
                   T1
                   (dworklist_conswork dworklist_empty (dwork_infabs T1 c))
  | d__ac__infabsunion : forall A1 B2 c, 
      d_apply_cont (dcont_infabsunion A1 c) 
                   B2
                   (dworklist_conswork dworklist_empty (dwork_infabsunion A1 B2 c))
  | d__ac__unioninfabs : forall A2 B1 C1 c,
      d_apply_cont (dcont_unioninfabs A2 c) 
                   (dtyp_arrow B1 C1)
                   (dworklist_conswork dworklist_empty (dwork_unioninfabs (dtyp_arrow B1 C1) A2 c))
  | d__ac_infapp : forall A1 e c,
      d_apply_cont (dcont_infapp e c) 
                   A1
                   (dworklist_conswork dworklist_empty (dwork_infapp A1 e c))
  | d__ac__tapp : forall A1 B1 c,
      d_apply_cont (dcont_inftapp B1 c) 
                   A1
                   (dworklist_conswork dworklist_empty (dwork_inftapp A1 B1 c))
  | d__ac__tappunion : forall A1 B1 C2 c,
      d_apply_cont (dcont_inftappunion A1 B1 c) 
                   C2 
                   (dworklist_conswork dworklist_empty (dwork_inftappunion C2 A1 B1 c))
  | d__ac__unioninftapp : forall A1 A2 c,
      d_apply_cont (dcont_unioninftapp A1 c) 
                   A2
                   (dworklist_conswork dworklist_empty (dwork_unioninftapp A1 A2 c))
  | d__ac__sub : forall A1 B1,
      d_apply_cont (dcont_sub A1) 
                   B1
                   (dworklist_conswork dworklist_empty (dwork_sub B1 A1))
.

(* decl worklist delegated reduction, corresponds to Jimmy's dc *)
Inductive d_wl_del_red : dworklist -> Prop :=
  | d__wldelred__empty : d_wl_del_red dworklist_empty
  | d__wldelred__var : forall Γ x A,
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_consvar Γ x (dbind_typ A))
  | d__wldelred__tvar : forall Γ X,
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_constvar Γ X dbind_tvar_empty)
  | d__wldelred__stvar : forall Γ SX,
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_consstvar Γ SX dbind_stvar_empty)
  | d__wldelred__chk : forall Γ e T1,
      d_typing (dwl_to_denv Γ) e d_typingmode_chk T1 ->
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_conswork Γ (dwork_check e T1))
  | d__wldelred__inf : forall Γ e T1 c,
      d_typing (dwl_to_denv Γ) e d_typingmode_inf T1 ->
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c T1)) ->
      d_wl_del_red (dworklist_conswork Γ (dwork_infer e c))
  | d__wldelred__infabs : forall Γ T1 T2 T3 c,
      d_infabs (dwl_to_denv Γ) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c (dtyp_arrow T2 T3))) ->
      d_wl_del_red (dworklist_conswork Γ (dwork_infabs T1 c))
  | d__wldelred__infabsunion : forall Γ A2 B1 B2 C1 C2 c,
      d_infabs (dwl_to_denv Γ) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c (dtyp_arrow (dtyp_intersection B1 B2) (dtyp_union C1 C2)))) ->
      d_wl_del_red (dworklist_conswork Γ (dwork_infabsunion (dtyp_arrow B1 C1) A2 c))
  | d__wldelred__unioninfabs : forall Γ B1 B2 C1 C2 c,
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c (dtyp_arrow (dtyp_intersection B1 B2) (dtyp_union C1 C2)))) -> 
      d_wl_del_red (dworklist_conswork Γ (dwork_unioninfabs (dtyp_arrow B1 C1) (dtyp_arrow B2 C2) c))  
  | d__wldelred__infapp : forall Γ e T1 T2 c,
      d_typing (dwl_to_denv Γ) e d_typingmode_chk T1 ->
      d_wl_del_red (dworklist_conswork (dworklist_conswork Γ (dwork_check e T1)) (dwork_apply c T2)) ->
      d_wl_del_red (dworklist_conswork Γ (dwork_infapp (dtyp_arrow T1 T2) e c))
  | d__wldelred__inftapp : forall Γ T1 T2 T3 c,
      d_inftapp (dwl_to_denv Γ) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c T3)) -> 
      d_wl_del_red (dworklist_conswork Γ (dwork_inftapp T1 T2 c))
  | d__wldelred__inftappunion : forall Γ A2 B2 C1 C2 c,
      d_inftapp (dwl_to_denv Γ) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c (dtyp_union C1 C2))) -> 
      d_wl_del_red (dworklist_conswork Γ (dwork_inftappunion C1 A2 B2 c))
  | d__wldelred_unioninftapp : forall Γ A1 A2 c,
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c (dtyp_union A1 A2))) -> 
      d_wl_del_red (dworklist_conswork Γ (dwork_unioninftapp A1 A2 c))
  | d__wldelred__sub : forall Γ S1 T1,
      d_sub (dwl_to_denv Γ) S1 T1 ->
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_conswork Γ (dwork_sub S1 T1))
  | d__wldelred__applycont : forall Γ c T1 Γ',
      d_apply_cont c T1 Γ' ->
      d_wl_del_red (dwl_app Γ' Γ) ->
      d_wl_del_red (dworklist_conswork Γ (dwork_apply c T1))
  .

(* defns Jdworklist_reduction *)
Inductive d_wl_red : dworklist -> Prop :=    (* defn d_wl_red *)
 | d__wlred__empty : d_wl_red dworklist_empty
 | d__wlred__var : forall (Γ:dworklist) (x:atom) (A:dtyp),
    d_wl_red Γ ->
    d_wl_red (dworklist_consvar Γ x (dbind_typ A))
 | d__wlred__tvar : forall (Γ:dworklist) (X:atom),
    d_wl_red Γ ->
    d_wl_red (dworklist_constvar Γ X dbind_tvar_empty)
 | d__wlred__stvar : forall (Γ:dworklist) (SX:atom),
    d_wl_red Γ ->
    d_wl_red (dworklist_consstvar Γ SX dbind_stvar_empty)
 | d__wlred__subtop : forall (Γ:dworklist) (A1:dtyp),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 dtyp_top))
 | d__wlred__subbot : forall (Γ:dworklist) (A1:dtyp),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub dtyp_bot A1))
 | d__wlred__subunit : forall (Γ:dworklist),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub dtyp_unit dtyp_unit))
 | d__wlred__subtvar : forall (Γ:dworklist) (X:typvar),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_var_f X) (dtyp_var_f X)))
 | d__wlred__substvar : forall (Γ:dworklist) (SX:stypvar),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_svar SX) (dtyp_svar SX)))
 | d__wlred__subarrow : forall (Γ:dworklist) (A1 A2 B1 B2:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_sub B1 A1)) (dwork_sub A2 B2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)))
 | d__wlred__suball : forall (L:vars) (Γ:dworklist) (A1 B1:dtyp),
     ( forall SX , SX `notin` L -> d_wl_red (dworklist_conswork (dworklist_consstvar Γ SX dbind_stvar_empty) (dwork_sub  (open_dtyp_wrt_dtyp  A1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  B1   (dtyp_svar SX) ) ))) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_all A1) (dtyp_all B1)))    
 | d__wlred__sub_alll : forall (Γ:dworklist) (A1 B1 T1:dtyp),
     dneq_all B1 ->
     dneq_intersection B1 ->
     dneq_union B1 -> 
     dmono_typ T1 ->
     dwf_typ  ( dwl_to_denv  Γ  )  T1 ->
     d_wl_red (dworklist_conswork Γ (dwork_sub  (open_dtyp_wrt_dtyp  A1   T1 )  B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_all A1) B1))
 | d__wlred__sub_intersection1 : forall (Γ:dworklist) (A1 B1 B2:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_sub A1 B1)) (dwork_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 (dtyp_intersection B1 B2)))
 | d__wlred__sub_intersection2 : forall (Γ:dworklist) (A1 A2 B1:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_intersection A1 A2) B1))
 | d__wlred__sub_intersection3 : forall (Γ:dworklist) (A1 A2 B1:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_intersection A1 A2) B1))
 | d__wlred__sub_union1 : forall (Γ:dworklist) (A1 B1 B2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 (dtyp_union B1 B2)))
 | d__wlred__sub_union2 : forall (Γ:dworklist) (A1 B1 B2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 (dtyp_union B1 B2)))
 | d__wlred__sub_union3 : forall (Γ:dworklist) (A1 A2 B1:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_sub A1 B1)) (dwork_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_union A1 A2) B1))
 | d__wlred__chk_sub : forall (Γ:dworklist) (e:dexp) (A1:dtyp),
     dneq_intersection A1 ->
     dneq_union A1 ->
     d_wl_red (dworklist_conswork Γ (dwork_infer e (dcont_sub A1))) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e A1))
 (* | d__wlred__chkall : forall (L:vars) (Γ:dworklist) (e:dexp) (T1:dtyp),
      ( forall X , X \notin  L  -> ds_in X  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar Γ X dbind_tvar_empty) (dwork_check e  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_all T1))) *)
 | d__wlred__chk_absarrow : forall (L:vars) (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Γ x (dbind_typ A1)) (dwork_check  ( open_dexp_wrt_dexp e (dexp_var_f x) )  A2)) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_check (dexp_abs e) (dtyp_arrow A1 A2)))
 | d__wlred__chk_abstop : forall (L:vars) (Γ:dworklist) (e:dexp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Γ x (dbind_typ dtyp_bot)) (dwork_check  ( open_dexp_wrt_dexp e (dexp_var_f x) )  dtyp_top)) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_check (dexp_abs e) dtyp_top))
 | d__wlred__chk_inter : forall (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_check e A1)) (dwork_check e A2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_intersection A1 A2)))
 | d__wlred__chk_union1 : forall (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_check e A1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_union A1 A2)))
 | d__wlred__chk_union2 : forall (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_check e A2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_union A1 A2)))
 | d__wlred__inf_var : forall (Γ:dworklist) (x:expvar) (c:dcont) (A1:dtyp),
      binds ( x )  ( (dbind_typ A1) ) (  ( dwl_to_denv  Γ  )  )  ->
     d_wl_red (dworklist_conswork Γ (dwork_apply c A1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer (dexp_var_f x) c))
 | d__wlred__inf_anno : forall (Γ:dworklist) (e:dexp) (A1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_apply c  A1)) (dwork_check e A1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer  ( (dexp_anno e A1) )  c))
 | d__wlred__inf_tabs : forall (L:vars) (Γ:dworklist) (e:dexp) (A1:dtyp) (c:dcont),
      (* ( forall X , X \notin  L  -> ds_in X  ( open_dtyp_wrt_dtyp A1 (dtyp_var_f X) )  )  -> *)
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork Γ (dwork_apply c  (dtyp_all A1) )) X dbind_tvar_empty) (dwork_check  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )   ( open_dtyp_wrt_dtyp A1 (dtyp_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_infer (dexp_tabs (dbody_anno e A1)) c))
 | d__wlred__inf_unit : forall (Γ:dworklist) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c dtyp_unit)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer dexp_unit c))
 | d__wlred__inf_app : forall (Γ:dworklist) (e1 e2:dexp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infer e1 (dcont_infabs (dcont_infapp e2 c)))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer  ( (dexp_app e1 e2) )  c))
 | d__wlred__inf_tapp : forall (Γ:dworklist) (e:dexp) (T:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infer e (dcont_inftapp T c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer (dexp_tapp e T) c))
 | d__wlred__inftapp_all : forall (Γ:dworklist) (T1 T2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c (open_dtyp_wrt_dtyp  T1   T2 ) )) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_all T1) T2 c))
 | d__wlred__inftapp_bot : forall (Γ:dworklist) (T:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c dtyp_bot)) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp dtyp_bot T c))
 | d__wlred__inftapp_inter1 : forall (Γ:dworklist) (A1 A2 B1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A1 B1 c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_intersection A1 A2) B1 c))
 | d__wlred__inftapp_inter2: forall (Γ:dworklist) (A1 A2 B1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A2 B1 c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_intersection A1 A2) B1 c))
 | d__wlred__inftapp_union : forall (Γ:dworklist) (A1 A2 B1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A1 B1 (dcont_inftappunion A2 B1 c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_union A1 A2) B1 c))
 | d__wlred__inftappunion : forall (Γ:dworklist) (A2 B2 C1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A2 B2 (dcont_unioninftapp C1 c) ))->
     d_wl_red (dworklist_conswork Γ (dwork_inftappunion C1 A2 B2 c))
 | d__wlred__unioninftapp : forall (Γ:dworklist) (A1 A2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c (dtyp_union A1 A2)))->
     d_wl_red (dworklist_conswork Γ (dwork_unioninftapp A1 A2 c))
 | d__wlred__infabs_arrow : forall (Γ:dworklist) (T1 T2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c (dtyp_arrow T1 T2))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (dtyp_arrow T1 T2) c))
 | d__wlred__infabs_bot : forall (Γ:dworklist) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c (dtyp_arrow dtyp_top dtyp_bot))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs dtyp_bot c))
 | d__wlred__infabs_all : forall (Γ:dworklist) (A1 T1:dtyp) (c:dcont),
     dwf_typ (dwl_to_denv Γ) T1 ->
     dmono_typ T1 ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (open_dtyp_wrt_dtyp A1 T1) c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (dtyp_all A1) c))
 | d__wlred__infabs_inter1 : forall (Γ:dworklist) (A1 A2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infabs A1 c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (dtyp_intersection A1 A2) c))
 | d__wlred__infabs_inter2: forall (Γ:dworklist) (A1 A2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infabs A2 c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (dtyp_intersection A1 A2) c))
 | d__wlred__infabs_union : forall (Γ:dworklist) (A1 A2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infabs A1 (dcont_infabsunion A2 c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (dtyp_union A1 A2) c))  
 | d__wlred__unioninfabs: forall (Γ:dworklist) (A1 A2 B1 B2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c (dtyp_arrow (dtyp_intersection A1 A2) (dtyp_union B1 B2)))) ->
     d_wl_red (dworklist_conswork Γ (dwork_unioninfabs (dtyp_arrow A1 B1) (dtyp_arrow A2 B2) c))
 | d__wlred__infabsunion: forall (Γ:dworklist) (A2 B1 C1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infabs A2 (dcont_unioninfabs (dtyp_arrow B1 C1) c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabsunion (dtyp_arrow B1 C1) A2 c))
 | d__wlred__applycont : forall (Γ Γ':dworklist) (T1:dtyp) (c:dcont),
     d_apply_cont c T1 Γ' ->
     d_wl_red (dwl_app Γ' Γ) ->
     d_wl_red (dworklist_conswork Γ (dwork_apply c T1))   
    .
