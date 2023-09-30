Require Import Program.Equality.

Require Import uni.prop_ln.
Require Export uni.def_ott.
Require Export uni.def_extra.


Fixpoint dwl_app (Γ1 Γ2 : dworklist) :=
  match Γ1 with 
  | dworklist_empty => Γ2 
  | dworklist_constvar Γ1' X b => dworklist_constvar (dwl_app Γ1' Γ2) X b
  | dworklist_consvar Γ1' x b => dworklist_consvar (dwl_app Γ1' Γ2) x b
  | dworklist_conswork Γ1' w => dworklist_conswork (dwl_app Γ1' Γ2) w
  end.

(* TODO : check *)
Inductive d_apply_cont : cont -> typ -> dworklist -> Prop :=
  (* | d__ac__done : forall T1,  
      d_apply_cont cont_done (some T1) dworklist_empty *)
  | d__ac__infabs: forall T1 c,
      d_apply_cont (cont_infabs c) 
                   T1
                   (dworklist_conswork dworklist_empty (work_infabs T1 c))
  | d__ac__infabsunion : forall A2 B1 C1 c, 
      d_apply_cont (cont_infabsunion A2 c) 
                   (typ_arrow B1 C1)
                   (dworklist_conswork dworklist_empty (work_infabsunion (typ_arrow B1 C1) A2 c))
  | d__ac__unioninfabs : forall B2 C2 B1 C1 c,
      d_apply_cont (cont_unioninfabs (typ_arrow B1 C1) c) 
                   (typ_arrow B2 C2)
                   (dworklist_conswork dworklist_empty (work_unioninfabs (typ_arrow B1 C1) (typ_arrow B2 C2) c))
  | d__ac_infapp : forall A1 e c,
      d_apply_cont (cont_infapp e c) 
                   A1
                   (dworklist_conswork dworklist_empty (work_infapp A1 e c))
  | d__ac__tapp : forall A1 B1 c,
      d_apply_cont (cont_inftapp B1 c) 
                   A1
                   (dworklist_conswork dworklist_empty (work_inftapp A1 B1 c))
  | d__ac__tappunion : forall A2 B2 C1 c,
      d_apply_cont (cont_inftappunion A2 B2 c) 
                   C1 
                   (dworklist_conswork dworklist_empty (work_inftappunion C1 A2 B2 c))
  | d__ac__unioninftapp : forall A1 A2 c,
      d_apply_cont (cont_unioninftapp A1 c) 
                   A2
                   (dworklist_conswork dworklist_empty (work_unioninftapp A1 A2 c))
  | d__ac__sub : forall A1 B1,
      d_apply_cont (cont_sub A1) 
                   B1
                   (dworklist_conswork dworklist_empty (work_sub B1 A1))
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
      d_wl_del_red (dworklist_constvar Γ SX dbind_stvar_empty)
  | d__wldelred__chk : forall Γ e T1,
      d_typing (dwl_to_denv Γ) e typingmode__chk T1 ->
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_conswork Γ (work_check e T1))
  | d__wldelred__inf : forall Γ e T1 c,
      d_typing (dwl_to_denv Γ) e typingmode__inf T1 ->
      d_wl_del_red (dworklist_conswork Γ (work_apply c T1)) ->
      d_wl_del_red (dworklist_conswork Γ (work_infer e c))
  | d__wldelred__infabs : forall Γ T1 T2 T3 c,
      d_infabs (dwl_to_denv Γ) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Γ (work_apply c (typ_arrow T2 T3))) ->
      d_wl_del_red (dworklist_conswork Γ (work_infabs T1 c))
  | d__wldelred__infabsunion : forall Γ A2 B1 B2 C1 C2 c,
      d_infabs (dwl_to_denv Γ) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Γ (work_apply c (typ_arrow (typ_intersection B1 B2) (typ_union C1 C2)))) ->
      d_wl_del_red (dworklist_conswork Γ (work_infabsunion (typ_arrow B1 C1) A2 c))
  | d__wldelred__unioninfabs : forall Γ B1 B2 C1 C2 c,
      d_wl_del_red (dworklist_conswork Γ (work_apply c (typ_arrow (typ_intersection B1 B2) (typ_union C1 C2)))) -> 
      d_wl_del_red (dworklist_conswork Γ (work_unioninfabs (typ_arrow B1 C1) (typ_arrow B2 C2) c))  
  | d__wldelred__infapp : forall Γ e T1 T2 c,
      d_wl_del_red (dworklist_conswork (dworklist_conswork Γ (work_check e T1)) (work_apply c T2)) ->
      d_wl_del_red (dworklist_conswork Γ (work_infapp (typ_arrow T1 T2) e c))
  | d__wldelred__inftapp : forall Γ T1 T2 T3 c,
      d_inftapp (dwl_to_denv Γ) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Γ (work_apply c T3)) -> 
      d_wl_del_red (dworklist_conswork Γ (work_inftapp T1 T2 c))
  | d__wldelred__inftappunion : forall Γ A2 B2 C1 C2 c,
      d_inftapp (dwl_to_denv Γ) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Γ (work_apply c (typ_union C1 C2))) -> 
      d_wl_del_red (dworklist_conswork Γ (work_inftappunion C1 A2 B2 c))
  | d__wldelred_unioninftapp : forall Γ A1 A2 c,
      d_wl_del_red (dworklist_conswork Γ (work_apply c (typ_union A1 A2))) -> 
      d_wl_del_red (dworklist_conswork Γ (work_unioninftapp A1 A2 c))
  | d__wldelred__sub : forall Γ S1 T1,
      d_sub (dwl_to_denv Γ) S1 T1 ->
      d_wl_del_red Γ ->
      d_wl_del_red (dworklist_conswork Γ (work_sub S1 T1))
  | d__wldelred__applycont : forall Γ c T1 Γ',
      d_apply_cont c T1 Γ' ->
      d_wl_del_red (dwl_app Γ' Γ) ->
      d_wl_del_red (dworklist_conswork Γ (work_apply c T1))
  .

(* defns Jdworklist_reduction *)
Inductive d_wl_red : dworklist -> Prop :=    (* defn d_wl_red *)
 | d__wlred__empty : d_wl_red dworklist_empty
 | d__wlred__var : forall (Γ:dworklist) (x:atom) (A:typ),
    d_wl_red Γ ->
    d_wl_red (dworklist_consvar Γ x (dbind_typ A))
 | d__wlred__tvar : forall (Γ:dworklist) (X:atom),
    d_wl_red Γ ->
    d_wl_red (dworklist_constvar Γ X dbind_tvar_empty)
 | d__wlred__stvar : forall (Γ:dworklist) (SX:atom),
    d_wl_red Γ ->
    d_wl_red (dworklist_constvar Γ SX dbind_stvar_empty)
 | d__wlred__subtop : forall (Γ:dworklist) (A1:typ),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (work_sub A1 typ_top))
 | d__wlred__subbot : forall (Γ:dworklist) (A1:typ),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (work_sub typ_bot A1))
 | d__wlred__subunit : forall (Γ:dworklist),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (work_sub typ_unit typ_unit))
 | d__wlred__subtvar : forall (Γ:dworklist) (X:typvar),
     d_wl_red Γ ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f X)))
 | d__wlred__subarrow : forall (Γ:dworklist) (A1 A2 B1 B2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (work_sub B1 A1)) (work_sub A2 B2)) ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2)))
 | d__wlred__sub_all : forall (L:vars) (Γ:dworklist) (A1 B1:typ),
     ( forall X , X `notin` L -> d_wl_red (dworklist_conswork (dworklist_constvar Γ X dbind_stvar_empty) (work_sub  (open_typ_wrt_typ  A1   (typ_var_f X) )   (open_typ_wrt_typ  B1   (typ_var_f X) ) ))) ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_all A1) (typ_all B1)))    
 | d__wlred__sub_alll : forall (Γ:dworklist) (A1 B1 T1:typ),
     neq_all B1 ->
     neq_intersection B1 ->
     neq_union B1 -> 
     d_mono_typ ( dwl_to_denv  Γ  )  T1 ->
     d_wl_red (dworklist_conswork Γ (work_sub  (open_typ_wrt_typ  A1   T1 )  B1)) ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_all A1) B1))
 | d__wlred__sub_intersection1 : forall (Γ:dworklist) (A1 B1 B2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (work_sub A1 B1)) (work_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Γ (work_sub A1 (typ_intersection B1 B2)))
 | d__wlred__sub_intersection2 : forall (Γ:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork Γ (work_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_intersection A1 A2) B1))
 | d__wlred__sub_intersection3 : forall (Γ:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork Γ (work_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_intersection A1 A2) B1))
 | d__wlred__sub_union1 : forall (Γ:dworklist) (A1 B1 B2:typ),
     d_wl_red (dworklist_conswork Γ (work_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Γ (work_sub A1 (typ_union B1 B2)))
 | d__wlred__sub_union2 : forall (Γ:dworklist) (A1 B1 B2:typ),
     d_wl_red (dworklist_conswork Γ (work_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Γ (work_sub A1 (typ_union B1 B2)))
 | d__wlred__sub_union3 : forall (Γ:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (work_sub A1 B1)) (work_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Γ (work_sub (typ_union A1 A2) B1))
 | d__wlred__chk_sub : forall (Γ:dworklist) (e:exp) (A1:typ),
     neq_intersection A1 ->
     neq_union A1 ->
     d_wl_red (dworklist_conswork Γ (work_infer e (cont_sub A1))) ->
     d_wl_red (dworklist_conswork Γ (work_check e A1))
 (* | d__wlred__chkall : forall (L:vars) (Γ:dworklist) (e:exp) (T1:typ),
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar Γ X dbind_tvar_empty) (work_check e  ( open_typ_wrt_typ T1 (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Γ (work_check e (typ_all T1))) *)
 | d__wlred__chk_absarrow : forall (L:vars) (Γ:dworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Γ x (dbind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     d_wl_red (dworklist_conswork Γ (work_check (exp_abs e) (typ_arrow A1 A2)))
 | d__wlred__chk_abstop : forall (L:vars) (Γ:dworklist) (e:exp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Γ x (dbind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     d_wl_red (dworklist_conswork Γ (work_check (exp_abs e) typ_top))
 | d__wlred__chk_inter : forall (Γ:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (work_check e A1)) (work_check e A2)) ->
     d_wl_red (dworklist_conswork Γ (work_check e (typ_intersection A1 A2)))
 | d__wlred__chk_union1 : forall (Γ:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork Γ (work_check e A1)) ->
     d_wl_red (dworklist_conswork Γ (work_check e (typ_union A1 A2)))
 | d__wlred__chk_union2 : forall (Γ:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork Γ (work_check e A2)) ->
     d_wl_red (dworklist_conswork Γ (work_check e (typ_union A1 A2)))
 | d__wlred__inf_var : forall (Γ:dworklist) (x:expvar) (c:cont) (A1:typ),
      binds ( x )  ( (dbind_typ A1) ) (  ( dwl_to_denv  Γ  )  )  ->
     d_wl_red (dworklist_conswork Γ (work_apply c A1)) ->
     d_wl_red (dworklist_conswork Γ (work_infer (exp_var_f x) c))
 | d__wlred__inf_anno : forall (Γ:dworklist) (e:exp) (A1:typ) (c:cont),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (work_apply c  A1)) (work_check e A1)) ->
     d_wl_red (dworklist_conswork Γ (work_infer  ( (exp_anno e A1) )  c))
 | d__wlred__inf_tabs : forall (L:vars) (Γ:dworklist) (e:exp) (A1:typ) (c:cont),
      (* ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  -> *)
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork Γ (work_apply c  (typ_all A1) )) X dbind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Γ (work_infer (exp_tabs (body_anno e A1)) c))
 | d__wlred__inf_unit : forall (Γ:dworklist) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c typ_unit)) ->
     d_wl_red (dworklist_conswork Γ (work_infer exp_unit c))
 | d__wlred__inf_app : forall (Γ:dworklist) (e1 e2:exp) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_infer e1 (cont_infabs (cont_infapp e2 c)))) ->
     d_wl_red (dworklist_conswork Γ (work_infer  ( (exp_app e1 e2) )  c))
 | d__wlred__inf_tapp : forall (Γ:dworklist) (e:exp) (T:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_infer e (cont_inftapp T c))) ->
     d_wl_red (dworklist_conswork Γ (work_infer (exp_tapp e T) c))
 | d__wlred__inftapp_all : forall (Γ:dworklist) (T1 T2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c (open_typ_wrt_typ  T1   T2 ) )) ->
     d_wl_red (dworklist_conswork Γ (work_inftapp (typ_all T1) T2 c))
 | d__wlred__inftapp_bot : forall (Γ:dworklist) (T:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c typ_bot)) ->
     d_wl_red (dworklist_conswork Γ (work_inftapp typ_bot T c))
 | d__wlred__inftapp_inter1 : forall (Γ:dworklist) (A1 A2 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_inftapp A1 B1 c)) ->
     d_wl_red (dworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B1 c))
 | d__wlred__inftapp_inter2: forall (Γ:dworklist) (A1 A2 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_inftapp A2 B1 c)) ->
     d_wl_red (dworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B1 c))
 | d__wlred__inftapp_union : forall (Γ:dworklist) (A1 A2 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_inftapp A1 B1 (cont_inftappunion A2 B1 c))) ->
     d_wl_red (dworklist_conswork Γ (work_inftapp (typ_union A1 A2) B1 c))
 | d__wlred__inftappunion : forall (Γ:dworklist) (A2 B2 C1:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_inftapp A2 B2 (cont_unioninftapp C1 c) ))->
     d_wl_red (dworklist_conswork Γ (work_inftappunion C1 A2 B2 c))
 | d__wlred__unioninftapp : forall (Γ:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c (typ_union A1 A2)))->
     d_wl_red (dworklist_conswork Γ (work_unioninftapp A1 A2 c))
 | d__wlred__infabs_arrow : forall (Γ:dworklist) (T1 T2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c (typ_arrow T1 T2))) ->
     d_wl_red (dworklist_conswork Γ (work_infabs (typ_arrow T1 T2) c))
 | d__wlred__infabs_bot : forall (Γ:dworklist) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c (typ_arrow typ_top typ_bot))) ->
     d_wl_red (dworklist_conswork Γ (work_infabs typ_bot c))
 | d__wlred__infabs_all : forall (Γ:dworklist) (A1 T1:typ) (c:cont),
     d_mono_typ (dwl_to_denv Γ) T1 ->
     d_wl_red (dworklist_conswork Γ (work_infabs (open_typ_wrt_typ A1 T1) c)) ->
     d_wl_red (dworklist_conswork Γ (work_infabs (typ_all A1) c))
 | d__wlred__infabs_inter1 : forall (Γ:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_infabs A1 c)) ->
     d_wl_red (dworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c))
 | d__wlred__infabs_inter2: forall (Γ:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_infabs A2 c)) ->
     d_wl_red (dworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c))
 | d__wlred__infabs_union : forall (Γ:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_infabs A1 (cont_infabsunion A2 c))) ->
     d_wl_red (dworklist_conswork Γ (work_infabs (typ_union A1 A2) c))  
 | d__wlred__unioninfabs: forall (Γ:dworklist) (A1 A2 B1 B2:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_apply c (typ_arrow (typ_intersection A1 A2) (typ_union B1 B2)))) ->
     d_wl_red (dworklist_conswork Γ (work_unioninfabs (typ_arrow A1 B1) (typ_arrow A2 B2) c))
 | d__wlred__infabsunion: forall (Γ:dworklist) (A2 B1 C1:typ) (c:cont),
     d_wl_red (dworklist_conswork Γ (work_infabs A2 (cont_unioninfabs (typ_arrow B1 C1) c))) ->
     d_wl_red (dworklist_conswork Γ (work_infabsunion (typ_arrow B1 C1) A2 c))
 | d__wlred__infapp: forall (Γ:dworklist) (e:exp) (A1 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork (dworklist_conswork Γ (work_check e A1)) (work_apply c B1)) ->
     d_wl_red (dworklist_conswork Γ (work_infapp (typ_arrow A1 B1) e c))
 | d__wlred__applycont : forall (Γ Γ':dworklist) (T1:typ) (c:cont),
     d_apply_cont c T1 Γ' ->
     d_wl_red (dwl_app Γ' Γ) ->
     d_wl_red (dworklist_conswork Γ (work_apply c T1))   
    .
