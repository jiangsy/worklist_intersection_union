Require Import Program.Equality.

Require Import uni.prop_ln.
Require Export uni.def_ott.
Require Export uni.decl.def_extra.


Fixpoint dwl_app (Ω1 Ω2 : dworklist) :=
  match Ω1 with 
  | dworklist_empty => Ω2 
  | dworklist_constvar Ω1' X b => dworklist_constvar (dwl_app Ω1' Ω2) X b
  | dworklist_consvar Ω1' x b => dworklist_consvar (dwl_app Ω1' Ω2) x b
  | dworklist_conswork Ω1' w => dworklist_conswork (dwl_app Ω1' Ω2) w
  end.

(* TODO : could change to cont -> typ -> work *)
Inductive apply_cont : cont -> typ -> work -> Prop :=
  (* | applycont__done : forall T1,  
      apply_cont cont_done (some T1) dworklist_empty *)
  | applycont__infabs: forall T1 c,
      apply_cont (cont_infabs c) 
                   T1
                   (work_infabs T1 c)
  | applycont__infabsunion : forall A2 B1 C1 c, 
      apply_cont (cont_infabsunion A2 c) 
                   (typ_arrow B1 C1)
                   (work_infabsunion (typ_arrow B1 C1) A2 c)
  | applycont__unioninfabs : forall B2 C2 B1 C1 c,
      apply_cont (cont_unioninfabs (typ_arrow B1 C1) c) 
                   (typ_arrow B2 C2)
                   (work_unioninfabs (typ_arrow B1 C1) (typ_arrow B2 C2) c)
  | d_applycont_infapp : forall A1 e c,
      apply_cont (cont_infapp e c) 
                   A1
                  (work_infapp A1 e c)
  | applycont__tapp : forall A1 B1 c,
      apply_cont (cont_inftapp B1 c) 
                   A1
                   (work_inftapp A1 B1 c)
  | applycont__tappunion : forall A2 B2 C1 c,
      apply_cont (cont_inftappunion A2 B2 c) 
                   C1 
                   (work_inftappunion C1 A2 B2 c)
  | applycont__unioninftapp : forall A1 A2 c,
      apply_cont (cont_unioninftapp A1 c) 
                   A2
                   (work_unioninftapp A1 A2 c)
  | applycont__sub : forall A1 B1,
      apply_cont (cont_sub A1) 
                   B1
                   (work_sub B1 A1)
.

(* decl worklist delegated reduction, corresponds to Jimmy's dc *)
Inductive d_wl_del_red : dworklist -> Prop :=
  | d_wldelred__empty : d_wl_del_red dworklist_empty
  | d_wldelred__var : forall Ω x A,
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_consvar Ω x (dbind_typ A))
  | d_wldelred__tvar : forall Ω X,
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_constvar Ω X dbind_tvar_empty)
  | d_wldelred__stvar : forall Ω X,
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_constvar Ω X dbind_stvar_empty)
  | d_wldelred__chk : forall Ω e T1,
      d_typing (dwl_to_denv Ω) e typingmode__chk T1 ->
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_conswork Ω (work_check e T1))
  | d_wldelred__inf : forall Ω e T1 c,
      d_typing (dwl_to_denv Ω) e typingmode__inf T1 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c T1)) ->
      d_wl_del_red (dworklist_conswork Ω (work_infer e c))
  | d_wldelred__infabs : forall Ω T1 T2 T3 c,
      d_infabs (dwl_to_denv Ω) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c (typ_arrow T2 T3))) ->
      d_wl_del_red (dworklist_conswork Ω (work_infabs T1 c))
  | d_wldelred__infabsunion : forall Ω A2 B1 B2 C1 C2 c,
      d_infabs (dwl_to_denv Ω) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c (typ_arrow (typ_intersection B1 B2) (typ_union C1 C2)))) ->
      d_wl_del_red (dworklist_conswork Ω (work_infabsunion (typ_arrow B1 C1) A2 c))
  | d_wldelred__unioninfabs : forall Ω B1 B2 C1 C2 c,
      d_wl_del_red (dworklist_conswork Ω (work_apply c (typ_arrow (typ_intersection B1 B2) (typ_union C1 C2)))) -> 
      d_wl_del_red (dworklist_conswork Ω (work_unioninfabs (typ_arrow B1 C1) (typ_arrow B2 C2) c))  
  | d_wldelred__infapp : forall Ω e T1 T2 c,
      d_wl_del_red (dworklist_conswork (dworklist_conswork Ω (work_check e T1)) (work_apply c T2)) ->
      d_wl_del_red (dworklist_conswork Ω (work_infapp (typ_arrow T1 T2) e c))
  | d_wldelred__inftapp : forall Ω T1 T2 T3 c,
      d_inftapp (dwl_to_denv Ω) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c T3)) -> 
      d_wl_del_red (dworklist_conswork Ω (work_inftapp T1 T2 c))
  | d_wldelred__inftappunion : forall Ω A2 B2 C1 C2 c,
      d_inftapp (dwl_to_denv Ω) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c (typ_union C1 C2))) -> 
      d_wl_del_red (dworklist_conswork Ω (work_inftappunion C1 A2 B2 c))
  | d_wldelred_unioninftapp : forall Ω A1 A2 c,
      d_wl_del_red (dworklist_conswork Ω (work_apply c (typ_union A1 A2))) -> 
      d_wl_del_red (dworklist_conswork Ω (work_unioninftapp A1 A2 c))
  | d_wldelred__sub : forall Ω S1 T1,
      d_sub (dwl_to_denv Ω) S1 T1 ->
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_conswork Ω (work_sub S1 T1))
  | d_wldelred__applycont : forall Ω c T1 w,
      apply_cont c T1 w ->
      d_wl_del_red (dworklist_conswork Ω w) ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c T1))
  .

(* defns Jdworklist_reduction *)
Inductive d_wl_red : dworklist -> Prop :=    (* defn d_wl_red *)
 | d_wlred__empty : d_wl_red dworklist_empty
 | d_wlred__var : forall (Ω:dworklist) (x:atom) (A:typ),
    d_wl_red Ω ->
    d_wl_red (dworklist_consvar Ω x (dbind_typ A))
 | d_wlred__tvar : forall (Ω:dworklist) (X:atom),
    d_wl_red Ω ->
    d_wl_red (dworklist_constvar Ω X dbind_tvar_empty)
 | d_wlred__stvar : forall (Ω:dworklist) (SX:atom),
    d_wl_red Ω ->
    d_wl_red (dworklist_constvar Ω SX dbind_stvar_empty)
 | d_wlred__subtop : forall (Ω:dworklist) (A1:typ),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub A1 typ_top))
 | d_wlred__subbot : forall (Ω:dworklist) (A1:typ),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub typ_bot A1))
 | d_wlred__subunit : forall (Ω:dworklist),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub typ_unit typ_unit))
 | d_wlred__subtvar : forall (Ω:dworklist) (X:typvar),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_var_f X) (typ_var_f X)))
 | d_wlred__subarrow : forall (Ω:dworklist) (A1 A2 B1 B2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_sub B1 A1)) (work_sub A2 B2)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2)))
 | d_wlred__sub_all : forall (L:vars) (Ω:dworklist) (A1 B1:typ),
     ( forall X , X `notin` L -> d_wl_red (dworklist_conswork (dworklist_constvar Ω X dbind_stvar_empty) (work_sub  (open_typ_wrt_typ  A1   (typ_var_f X) )   (open_typ_wrt_typ  B1   (typ_var_f X) ) ))) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_all A1) (typ_all B1)))    
 | d_wlred__sub_alll : forall (Ω:dworklist) (A1 B1 T1:typ),
     neq_all B1 ->
     neq_intersection B1 ->
     neq_union B1 -> 
     d_mono_typ ( dwl_to_denv  Ω  )  T1 ->
     d_wl_red (dworklist_conswork Ω (work_sub  (open_typ_wrt_typ  A1   T1 )  B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_all A1) B1))
 | d_wlred__sub_intersection1 : forall (Ω:dworklist) (A1 B1 B2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_sub A1 B1)) (work_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Ω (work_sub A1 (typ_intersection B1 B2)))
 | d_wlred__sub_intersection2 : forall (Ω:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_intersection A1 A2) B1))
 | d_wlred__sub_intersection3 : forall (Ω:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_intersection A1 A2) B1))
 | d_wlred__sub_union1 : forall (Ω:dworklist) (A1 B1 B2:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A1 B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub A1 (typ_union B1 B2)))
 | d_wlred__sub_union2 : forall (Ω:dworklist) (A1 B1 B2:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A1 B2)) ->
     d_wl_red (dworklist_conswork Ω (work_sub A1 (typ_union B1 B2)))
 | d_wlred__sub_union3 : forall (Ω:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_sub A1 B1)) (work_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_union A1 A2) B1))
 | d_wlred__chk_sub : forall (Ω:dworklist) (e:exp) (A1:typ),
     d_wl_red (dworklist_conswork Ω (work_infer e (cont_sub A1))) ->
     d_wl_red (dworklist_conswork Ω (work_check e A1))
 (* | d_wlred__chkall : forall (L:vars) (Ω:dworklist) (e:exp) (T1:typ),
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar Ω X dbind_tvar_empty) (work_check e  ( open_typ_wrt_typ T1 (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_all T1))) *)
 | d_wlred__chk_absarrow : forall (L:vars) (Ω:dworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Ω x (dbind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     d_wl_red (dworklist_conswork Ω (work_check (exp_abs e) (typ_arrow A1 A2)))
 | d_wlred__chk_abstop : forall (L:vars) (Ω:dworklist) (e:exp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Ω x (dbind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     d_wl_red (dworklist_conswork Ω (work_check (exp_abs e) typ_top))
 | d_wlred__chk_inter : forall (Ω:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_check e A1)) (work_check e A2)) ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_intersection A1 A2)))
 | d_wlred__chk_union1 : forall (Ω:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork Ω (work_check e A1)) ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_union A1 A2)))
 | d_wlred__chk_union2 : forall (Ω:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork Ω (work_check e A2)) ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_union A1 A2)))
 | d_wlred__inf_var : forall (Ω:dworklist) (x:expvar) (c:cont) (A1:typ),
      binds ( x )  ( (dbind_typ A1) ) (  ( dwl_to_denv  Ω  )  )  ->
     d_wl_red (dworklist_conswork Ω (work_apply c A1)) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_var_f x) c))
 | d_wlred__inf_anno : forall (Ω:dworklist) (e:exp) (A1:typ) (c:cont),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_apply c  A1)) (work_check e A1)) ->
     d_wl_red (dworklist_conswork Ω (work_infer  ( (exp_anno e A1) )  c))
 | d_wlred__inf_tabs : forall (L:vars) (Ω:dworklist) (e:exp) (A1:typ) (c:cont),
      (* ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  -> *)
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork Ω (work_apply c  (typ_all A1) )) X dbind_tvar_empty) (work_check (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) ) ( open_typ_wrt_typ A1 (typ_var_f X) ) )  ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_tabs (body_anno e A1)) c))
 | d_wlred__inf_unit : forall (Ω:dworklist) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c typ_unit)) ->
     d_wl_red (dworklist_conswork Ω (work_infer exp_unit c))
 | d_wlred__inf_app : forall (Ω:dworklist) (e1 e2:exp) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infer e1 (cont_infabs (cont_infapp e2 c)))) ->
     d_wl_red (dworklist_conswork Ω (work_infer  ( (exp_app e1 e2) )  c))
 | d_wlred__inf_tapp : forall (Ω:dworklist) (e:exp) (T:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infer e (cont_inftapp T c))) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_tapp e T) c))
 | d_wlred__inftapp_all : forall (Ω:dworklist) (T1 T2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (open_typ_wrt_typ  T1   T2 ) )) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_all T1) T2 c))
 | d_wlred__inftapp_bot : forall (Ω:dworklist) (T:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c typ_bot)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp typ_bot T c))
 | d_wlred__inftapp_inter1 : forall (Ω:dworklist) (A1 A2 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_inftapp A1 B1 c)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_intersection A1 A2) B1 c))
 | d_wlred__inftapp_inter2: forall (Ω:dworklist) (A1 A2 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_inftapp A2 B1 c)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_intersection A1 A2) B1 c))
 | d_wlred__inftapp_union : forall (Ω:dworklist) (A1 A2 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_inftapp A1 B1 (cont_inftappunion A2 B1 c))) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_union A1 A2) B1 c))
 | d_wlred__inftappunion : forall (Ω:dworklist) (A2 B2 C1:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_inftapp A2 B2 (cont_unioninftapp C1 c) ))->
     d_wl_red (dworklist_conswork Ω (work_inftappunion C1 A2 B2 c))
 | d_wlred__unioninftapp : forall (Ω:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (typ_union A1 A2)))->
     d_wl_red (dworklist_conswork Ω (work_unioninftapp A1 A2 c))
 | d_wlred__infabs_arrow : forall (Ω:dworklist) (T1 T2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (typ_arrow T1 T2))) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_arrow T1 T2) c))
 | d_wlred__infabs_bot : forall (Ω:dworklist) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (typ_arrow typ_top typ_bot))) ->
     d_wl_red (dworklist_conswork Ω (work_infabs typ_bot c))
 | d_wlred__infabs_all : forall (Ω:dworklist) (A1 T1:typ) (c:cont),
     d_mono_typ (dwl_to_denv Ω) T1 ->
     d_wl_red (dworklist_conswork Ω (work_infabs (open_typ_wrt_typ A1 T1) c)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_all A1) c))
 | d_wlred__infabs_inter1 : forall (Ω:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infabs A1 c)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_intersection A1 A2) c))
 | d_wlred__infabs_inter2: forall (Ω:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infabs A2 c)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_intersection A1 A2) c))
 | d_wlred__infabs_union : forall (Ω:dworklist) (A1 A2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infabs A1 (cont_infabsunion A2 c))) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_union A1 A2) c))  
 | d_wlred__unioninfabs: forall (Ω:dworklist) (A1 A2 B1 B2:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (typ_arrow (typ_intersection A1 A2) (typ_union B1 B2)))) ->
     d_wl_red (dworklist_conswork Ω (work_unioninfabs (typ_arrow A1 B1) (typ_arrow A2 B2) c))
 | d_wlred__infabsunion: forall (Ω:dworklist) (A2 B1 C1:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infabs A2 (cont_unioninfabs (typ_arrow B1 C1) c))) ->
     d_wl_red (dworklist_conswork Ω (work_infabsunion (typ_arrow B1 C1) A2 c))
 | d_wlred__infapp: forall (Ω:dworklist) (e:exp) (A1 B1:typ) (c:cont),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_check e A1)) (work_apply c B1)) ->
     d_wl_red (dworklist_conswork Ω (work_infapp (typ_arrow A1 B1) e c))
 | d_wlred__applycont : forall (Ω:dworklist) (w:work) (T1:typ) (c:cont),
     apply_cont c T1 w ->
     d_wl_red (dworklist_conswork Ω w) ->
     d_wl_red (dworklist_conswork Ω (work_apply c T1))   
    .
