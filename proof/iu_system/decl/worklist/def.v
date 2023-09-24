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
Inductive d_apply_cont : dcont -> dmaybetyp -> dworklist -> Prop :=
  (* | d__ac__done : forall T1,  
      d_apply_cont dcont_done (some T1) dworklist_empty *)
  | d__ac__infabs: forall T1 c,
      d_apply_cont (dcont_infabs c) (dmaybetyp_some T1) (dworklist_conswork dworklist_empty (dwork_infabs T1 c))
  | d__ac__infabs_union : forall A1 B2 c, 
      d_apply_cont (dcont_infabsunion A1 c) (dmaybetyp_some B2) (dworklist_conswork dworklist_empty (dwork_infabsunion A1 B2 c))
  | d__ac__tapp : forall A1 B1 c,
      d_apply_cont (dcont_inftapp B1 c) (dmaybetyp_some A1) (dworklist_conswork dworklist_empty (dwork_inftapp A1 B1 c))
  | d__ac__tappintersome : forall A1 B1 C2 c,
      d_apply_cont (dcont_inftappinter A1 B1 c) (dmaybetyp_some C2) (dworklist_conswork dworklist_empty (dwork_inftappinter C2 A1 B1 c))
  | d__ac__tappinternone : forall A1 B1 c,
      d_apply_cont (dcont_inftappinter A1 B1 c) dmaybetyp_none (dworklist_conswork dworklist_empty (dwork_inftapp A1 B1 c))
  | d__ac__tappunion : forall A1 B1 C2 c,
      d_apply_cont (dcont_inftappunion A1 B1 c) (dmaybetyp_some C2) (dworklist_conswork dworklist_empty (dwork_inftappunion C2 A1 B1 c))
  | d__ac__sub : forall T1 S1,
      d_apply_cont (dcont_sub S1) (dmaybetyp_some T1) (dworklist_conswork dworklist_empty (dwork_sub T1 S1))
.

(* decl worklist delegated reduction, corresponds to Jimmy's dc *)
Inductive dwl_del_red : dworklist -> Prop :=
  | dwldelred_empty : dwl_del_red dworklist_empty
  | dwldelred_inf : forall Γ e T1 c,
      d_typing (dwl_to_denv Γ) e d_typingmode_inf T1 ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c (dmaybetyp_some T1))) ->
      dwl_del_red (dworklist_conswork Γ (dwork_infer e c))
  | dwldelred_chk : forall Γ e T1,
      d_typing (dwl_to_denv Γ) e d_typingmode_chk T1 ->
      dwl_del_red Γ ->
      dwl_del_red (dworklist_conswork Γ (dwork_check e T1))
  | dwldelred_infabs : forall Γ T1 T2 T3 c,
      d_infabs (dwl_to_denv Γ) T1 T2 T3 ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c (dmaybetyp_some (dtyp_arrow T2 T3)))) ->
      dwl_del_red (dworklist_conswork Γ (dwork_infabs T1 c))
  (* | dwldelred_infapp : forall Γ e T1 T2 c,
      d_typing (dwl_to_denv Γ) e d_typingmode_chk T1 ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c T2)) ->
      dwl_del_red (dworklist_conswork Γ (dwork_infapp (dtyp_arrow T1 T2) e c)) *)
  | dwldelred_inftapp : forall Γ T1 T2 T3 c,
      d_inftapp (dwl_to_denv Γ) T1 T2 T3 ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c (dmaybetyp_some T3))) -> 
      dwl_del_red (dworklist_conswork Γ (dwork_inftapp T1 T2 c))
  | dwldelred_sub : forall Γ S1 T1,
      d_sub (dwl_to_denv Γ) S1 T1 ->
      dwl_del_red Γ ->
      dwl_del_red (dworklist_conswork Γ (dwork_sub S1 T1))
  | dwldelred_applycont : forall Γ c T1 Γ',
      d_apply_cont c T1 Γ' ->
      dwl_del_red (dwl_app Γ' Γ) ->
      dwl_del_red (dworklist_conswork Γ (dwork_apply c T1))
  .

(* defns Jdworklist_reduction *)
Inductive d_wl_red : dworklist -> Prop :=    (* defn d_wl_red *)
 | d_wlred_var : forall (Γ:dworklist) (x:atom) (A:dtyp),
    d_wl_red Γ ->
    d_wl_red (dworklist_constvar Γ x (dbind_typ A))
 | d_wlred_tvar : forall (Γ:dworklist) (X:atom),
    d_wl_red Γ ->
    d_wl_red (dworklist_constvar Γ X dbind_tvar_empty)
 | d_wlred_stvar : forall (Γ:dworklist) (SX:atom),
    d_wl_red Γ ->
    d_wl_red (dworklist_constvar Γ SX dbind_stvar_empty)
 | d_wlred_subtop : forall (Γ:dworklist) (A1:dtyp),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 dtyp_top))
 | d_wlred_subbot : forall (Γ:dworklist) (A1:dtyp),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub dtyp_bot A1))
 | d_wlred_subunit : forall (Γ:dworklist),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub dtyp_unit dtyp_unit))
 | d_wlred_subtvar : forall (Γ:dworklist) (X:typvar),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_var_f X) (dtyp_var_f X)))
 | d_wlred_substvar : forall (Γ:dworklist) (SX:stypvar),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_svar SX) (dtyp_svar SX)))
 | d_wlred_subarrow : forall (Γ:dworklist) (A1 A2 B1 B2:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_sub B1 A1)) (dwork_sub A2 B2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)))
 | d_wlred_suball : forall (L:vars) (Γ:dworklist) (A1 B1:dtyp),
     ( forall SX , SX `notin` L -> d_wl_red (dworklist_conswork (dworklist_consstvar Γ SX dbind_stvar_empty) (dwork_sub  (open_dtyp_wrt_dtyp  A1   (dtyp_svar SX) )   (open_dtyp_wrt_dtyp  B1   (dtyp_svar SX) ) ))) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_all A1) (dtyp_all B1)))    
 | d_wlred_suballl : forall (Γ:dworklist) (A1 B1 T1:dtyp),
     dneq_all A1 ->
     dneq_intersection B1 ->
     dneq_union B1 -> 
     dmono_typ T1 ->
     dwf_typ  ( dwl_to_denv  Γ  )  T1 ->
     d_wl_red (dworklist_conswork Γ (dwork_sub  (open_dtyp_wrt_dtyp  A1   T1 )  B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_all A1) B1))
 | d_wlred_subintersection1 : forall (Γ:dworklist) (A1 B1 B2:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_sub A1 B1)) (dwork_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 (dtyp_intersection B1 B2)))
 | d_wlred_subintersection2 : forall (Γ:dworklist) (A1 A2 B1:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_intersection A1 A2) B1))
 | d_wlred_subintersection3 : forall (Γ:dworklist) (A1 A2 B1:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_intersection A1 A2) B1))
 | d_wlred_subunion1 : forall (Γ:dworklist) (A1 B1 B2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 (dtyp_union B1 B2)))
 | d_wlred_subunion2 : forall (Γ:dworklist) (A1 B1 B2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub A1 (dtyp_union B1 B2)))
 | d_wlred_subunion3 : forall (Γ:dworklist) (A1 A2 B1:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_sub A1 B1)) (dwork_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_sub (dtyp_union A1 A2) B1))
 | d_wlred_chksub : forall (Γ:dworklist) (e:dexp) (A1:dtyp),
     dneq_intersection A1 ->
     dneq_union A1 ->
     d_wl_red (dworklist_conswork Γ (dwork_infer e (dcont_sub A1))) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e A1))
 (* | d_wlred_chkall : forall (L:vars) (Γ:dworklist) (e:dexp) (T1:dtyp),
      ( forall X , X \notin  L  -> ds_in X  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar Γ X dbind_tvar_empty) (dwork_check e  ( open_dtyp_wrt_dtyp T1 (dtyp_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_all T1))) *)
 | d_wlred_chkabsarrow : forall (L:vars) (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Γ x (dbind_typ A1)) (dwork_check  ( open_dexp_wrt_dexp e (dexp_var_f x) )  A2)) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_check (dexp_abs e) (dtyp_arrow A1 A2)))
 | d_wlred_chkabstop : forall (L:vars) (Γ:dworklist) (e:dexp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Γ x (dbind_typ dtyp_bot)) (dwork_check  ( open_dexp_wrt_dexp e (dexp_var_f x) )  dtyp_top)) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_check (dexp_abs e) dtyp_top))
 | d_wlred_chkintersection : forall (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_check e A1)) (dwork_check e A2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_intersection A1 A2)))
 | d_wlred_chkunion1 : forall (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_check e A1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_union A1 A2)))
 | d_wlred_chkunion2 : forall (Γ:dworklist) (e:dexp) (A1 A2:dtyp),
     d_wl_red (dworklist_conswork Γ (dwork_check e A2)) ->
     d_wl_red (dworklist_conswork Γ (dwork_check e (dtyp_union A1 A2)))
 | d_wlred_infvar : forall (Γ:dworklist) (x:expvar) (c:dcont) (A1:dtyp),
      binds ( x )  ( (dbind_typ A1) ) (  ( dwl_to_denv  Γ  )  )  ->
     d_wl_red (dworklist_conswork Γ (dwork_apply c A1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer (dexp_var_f x) c))
 | d_wlred_infanno : forall (Γ:dworklist) (e:dexp) (A1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_apply c A1)) (dwork_check e A1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer  ( (dexp_anno e A1) )  c))
 | d_wlred_inftabs : forall (L:vars) (Γ:dworklist) (e:dexp) (A1:dtyp) (c:dcont),
      (* ( forall X , X \notin  L  -> ds_in X  ( open_dtyp_wrt_dtyp A1 (dtyp_var_f X) )  )  -> *)
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork Γ (dwork_apply c  ( (dtyp_all A1) ) )) X dbind_tvar_empty) (dwork_check  ( open_dexp_wrt_dtyp e (dtyp_var_f X) )   ( open_dtyp_wrt_dtyp A1 (dtyp_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Γ (dwork_infer (dexp_tabs (dbody_anno e A1)) c))
 | d_wlred_infunit : forall (Γ:dworklist) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c dtyp_unit)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer dexp_unit c))
 | d_wlred_infapp : forall (Γ:dworklist) (e1 e2:dexp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infer e1 (dcont_infabs (dcont_infapp e2 c)))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer  ( (dexp_app e1 e2) )  c))
 | d_wlred_inftapp : forall (Γ:dworklist) (e:dexp) (T:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infer e (dcont_tapp T c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_infer (dexp_tapp e T) c))
 | d_wlred_inftappall : forall (Γ:dworklist) (T1 T2:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c  (open_dtyp_wrt_dtyp  T1   T2 ) )) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_all T1) T2 c))
 | d_wlred_inftappbot : forall (Γ:dworklist) (T:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c dtyp_bot)) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp dtyp_bot T c))
 | d_wlred_inftappintersection : forall (Γ:dworklist) (A1 A2 B1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A1 B1 (dcont_tappinter A2 B1 c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_intersection A1 A2) B1 c))
 | d_wlred_inftappintersection : forall (Γ:dworklist) (A1 A2 B1:dtyp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A1 B1 (dcont_tappunion A2 B1 c))) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_union A1 A2) B1 c))
 | d_wlred_inftappnone : forall (Γ:dworklist) (A1 B1:dtyp) (c:dcont),
     dneq_bot A1 ->
     dneq_all A1 ->
     dneq_intersection A1 ->
     dneq_union A1 ->
     d_wl_red (dworklist_conswork Γ (dwork_apply c top)) ->
     d_wl_red (dworklist_conswork Γ (dwork_inftapp A1 B1 c))
 | d_wlred_infabsarrow : forall (Γ:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_apply c T2)) (dwork_check e T1)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infabs (dtyp_arrow T1 T2) e c))
 | d_wlred_infappbot : forall (Γ:dworklist) (e:dexp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_apply c dtyp_bot)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infapp dtyp_bot e c))
 | d_wlred_infappintersection1 : forall (Γ:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infapp T1 e c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infapp (dtyp_intersection T1 T2) e c))
 | d_wlred_infappintersection2 : forall (Γ:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     d_wl_red (dworklist_conswork Γ (dwork_infapp T2 e c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infapp (dtyp_intersection T1 T2) e c))
 | d_wlred_infappunion : forall (Γ:dworklist) (T1 T2:dtyp) (e:dexp) (c:dcont),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (dwork_infapp T1 e c)) (dwork_infapp T2 e c)) ->
     d_wl_red (dworklist_conswork Γ (dwork_infapp (dtyp_union T1 T2) e c))  
  | d_wlred_applycont : forall (Γ Γ':dworklist) (T1:dtyp) (c:dcont),
     d_apply_cont c T1 Γ' ->
     d_wl_red (dwl_app Γ' Γ) ->
     d_wl_red (dworklist_conswork Γ (dwork_apply c T1))   
    .
