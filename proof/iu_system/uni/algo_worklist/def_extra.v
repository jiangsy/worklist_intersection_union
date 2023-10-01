Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.prop_ln.
Require Export uni.def_ott.
Require Export uni.decl_worklist.def.


Definition fv_env_gen (fv : abind -> atoms) (E : aenv) : atoms :=
  fold_right (fun xb acc => match xb with (x , b) => acc `union` fv b end ) {} E.

Definition ftvar_in_aenv := fv_env_gen ftvar_in_abind.

Inductive amode_update_bound := 
  | a_mode_ub__upper
  | a_mode_ub__lower
  | a_mode_ub__both.

Fixpoint awl_app (Γ1 Γ2 : aworklist) :=
  match Γ1 with 
  | aworklist_empty => Γ2 
  | aworklist_constvar Γ1' X b => aworklist_constvar (awl_app Γ1' Γ2) X b
  | aworklist_consvar Γ1' x b => aworklist_consvar (awl_app Γ1' Γ2) x b
  | aworklist_conswork Γ1' w => aworklist_conswork (awl_app Γ1' Γ2) w
  end.

Fixpoint aenv_to_awl (E : list (atom*abind)) :=
  match E with 
  | nil => aworklist_empty
  | (x, abind_typ A1) :: E'  => aworklist_consvar (aenv_to_awl E') x (abind_typ A1)
  | (X, b) :: E'  => aworklist_constvar (aenv_to_awl E') X b
  end.

Inductive a_smono_typ :  list (atom*abind)  -> typ -> Prop  :=
  | a_smono_typ__unit : forall E, a_smono_typ E typ_unit.
  
Definition update_lower_bound (A1 B1:typ) :=
  match B1 with
  | typ_bot => A1 
  | _ => typ_union B1 A1
  end.

Definition update_upper_bound (A1 B1:typ) :=
  match B1 with
  | typ_top => A1 
  | _ => typ_intersection B1 A1
  end.

Inductive a_update_bound
  : aworklist ->  list (atom*abind) -> typvar -> typ -> amode_update_bound -> aworklist -> aworklist -> Prop :=
  | a_ub__lb_stop : forall Γ1 E X A B1 A1, 
    X `notin` ftvar_in_typ A -> 
    a_update_bound
     (aworklist_constvar Γ1 X (abind_bound B1 A1)) E X A a_mode_ub__lower (aworklist_constvar (awl_app (aenv_to_awl E) Γ1) X (abind_bound (update_lower_bound A B1) A1)) aworklist_empty
  | a_ub__ub_stop : forall Γ1 E X A B1 A1, 
    X `notin` ftvar_in_typ A -> 
    a_update_bound
     (aworklist_constvar Γ1 X (abind_bound B1 A1)) E X A a_mode_ub__upper (aworklist_constvar (awl_app (aenv_to_awl E) Γ1) X (abind_bound B1 (update_upper_bound A A1))) aworklist_empty
  | a_ub__bb_stop : forall Γ1 E X A B1 A1, 
    X `notin` ftvar_in_typ A -> 
    a_update_bound
     (aworklist_constvar Γ1 X (abind_bound B1 A1)) E X A a_mode_ub__both (aworklist_constvar (awl_app (aenv_to_awl E) Γ1) X (abind_bound (update_lower_bound A B1) (update_upper_bound A A1))) aworklist_empty
  | a_ub__etvar_move : forall Γ1 X1 b1 E X A m Γ2 Γ3,
    X `notin` ftvar_in_abind b1 ->
    a_update_bound Γ1 E X A m Γ2 Γ3 ->
    a_update_bound (aworklist_constvar Γ1 X1 b1) ( (X1 , b1) :: E ) X A m Γ2 Γ3
  | a_ub__etvar_stay : forall Γ1 X1 b1 E X A m Γ2 Γ3,
    X1 `notin` ftvar_in_typ A /\ X1 `notin` ftvar_in_aenv E ->
    a_update_bound Γ1 E X A m Γ2 Γ3 ->
    a_update_bound (aworklist_constvar Γ1 X1 b1) E X A m Γ2 (aworklist_constvar Γ3 X1 b1)
  | a_ub__tvar_stay : forall Γ1 X1 b1 E X A m Γ2 Γ3,
    X1 `notin` ftvar_in_typ A /\ X1 `notin` ftvar_in_aenv E ->
    a_update_bound Γ1 E X A m Γ2 Γ3 ->
    a_update_bound (aworklist_constvar Γ1 X1 abind_tvar_empty) E X A m Γ2 (aworklist_constvar Γ3 X1 b1)
  | a_ub__stvar_stay : forall Γ1 X1 b1 E X A m Γ2 Γ3,
    X1 `notin` ftvar_in_typ A /\ X1 `notin` ftvar_in_aenv E ->
    a_update_bound Γ1 E X A m Γ2 Γ3 ->
    a_update_bound (aworklist_constvar Γ1 X1 abind_stvar_empty) E X A m Γ2 (aworklist_constvar Γ3 X1 b1)
  | a_ub__w_stay : forall Γ1 w1 E X A m Γ2 Γ3,
    a_update_bound Γ1 E X A m Γ2 Γ3 ->
    a_update_bound (aworklist_conswork Γ1 w1) E X A m Γ2 (aworklist_conswork Γ3 w1)
  | a_ub__var_stay : forall Γ1 x1 b1 E X A m Γ2 Γ3,
    a_update_bound Γ1 E X A m Γ2 Γ3 ->
    a_update_bound (aworklist_consvar Γ1 x1 b1) E X A m Γ2 (aworklist_consvar Γ3 x1 b1) 
  .

(* defns Jaworklist_reduction *)
Inductive a_wl_red : aworklist -> Prop :=    (* defn a_wl_red *)
 | a_wlred__gc_var : forall (aW:aworklist) (x:expvar) (A:typ),
     a_wl_red aW ->
     a_wl_red (aworklist_consvar aW x (abind_typ A))
 | a_wlred__gc_tvar : forall (aW:aworklist) (X:typvar),
     a_wl_red aW ->
     a_wl_red (aworklist_constvar aW X abind_tvar_empty)
 | a_wlred__gc_stvar : forall (aW:aworklist) (X:typvar),
     a_wl_red aW ->
     a_wl_red (aworklist_constvar aW X abind_stvar_empty)
 | a_wlred__gc_etvar : forall (aW:aworklist) (X:typvar) (A B:typ),
     a_wl_red (aworklist_conswork aW (work_sub A B)) ->
     a_wl_red (aworklist_constvar aW X (abind_bound A B))
 | a_wlred__sub_top : forall (aW:aworklist) (B1:typ),
     a_wl_red aW ->
     a_wl_red (aworklist_conswork aW (work_sub B1 typ_top))
 | a_wlred__sub_bot : forall (aW:aworklist) (A:typ),
     a_wl_red aW ->
     a_wl_red (aworklist_conswork aW (work_sub typ_bot A))
 | a_wlred__sub_unit : forall (aW:aworklist),
     a_wl_red aW ->
     a_wl_red (aworklist_conswork aW (work_sub typ_unit typ_unit))
 | a_wlred__sub_tvar : forall (aW:aworklist) (X:typvar),
     a_wl_red aW ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_var_f X) (typ_var_f X)))
 | a_wlred__subarrow : forall (aW:aworklist) (B1 B2 A1 A2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork aW (work_sub A1 B1)) (work_sub B2 A2)) ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_arrow B1 B2) (typ_arrow A1 A2)))
 | a_wlred__sub_alll : forall (L:vars) (aW:aworklist) (B1 A1:typ),
     neq_all A1 ->
     neq_intersection A1 ->
     neq_union A1 ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar aW X (abind_bound typ_bot typ_top)) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )  A1)) )  ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_all B1) A1))
 | a_wlred__sub_all : forall (L:vars) (aW:aworklist) (B1 A1:typ),
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar aW X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_all B1) (typ_all A1)))
 | a_wlred__sub_arrow1 : forall (aW:aworklist) (X:typvar) (A1 A2 B1 B2:typ) (X1 X2:typvar) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  aW  )  )  ->
      ( a_smono_typ   ( awl_to_aenv  aW  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (a_update_bound  (aworklist_constvar (aworklist_constvar aW X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__upper  aW2   aW3 )  ->
     a_wl_red (aworklist_conswork  (   ( awl_app  aW3   aW2  )   )  (work_sub (typ_arrow (typ_var_f X1) (typ_var_f X2)) (typ_arrow A1 A2))) ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_var_f X) (typ_arrow A1 A2)))
 | a_wlred__sub_arrow2 : forall (aW:aworklist) (A1 A2:typ) (X:typvar) (B1 B2:typ) (X1 X2:typvar) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  aW  )  )  ->
      ( a_smono_typ   ( awl_to_aenv  aW  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (a_update_bound  (aworklist_constvar (aworklist_constvar aW X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__lower  aW2   aW3 )  ->
     a_wl_red (aworklist_conswork  (   ( awl_app  aW3   aW2  )   )  (work_sub (typ_arrow A1 A2) (typ_arrow (typ_var_f X1) (typ_var_f X2)))) ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_arrow A1 A2) (typ_var_f X)))
 | a_wlred__sub_etvar1 : forall (aW:aworklist) (Y X:typvar) (B1 B2 B3 B4:typ) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  aW  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  aW  )  )  ->
      (a_update_bound  aW   nil   X   (typ_var_f Y)  a_mode_ub__lower  aW2   aW3 )  ->
     a_evs_in_wl aW X Y ->
     a_wl_red  (   ( awl_app  aW3   aW2  )   )  ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_var_f Y) (typ_var_f X)))
 | a_wlred__sub_etvar2 : forall (aW:aworklist) (X Y:typvar) (B1 B2 B3 B4:typ) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  aW  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  aW  )  )  ->
      (a_update_bound  aW   nil   X   (typ_var_f Y)  a_mode_ub__upper  aW2   aW3 )  ->
     a_evs_in_wl aW X Y ->
     a_wl_red  (   ( awl_app  aW3   aW2  )   )  ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_var_f X) (typ_var_f Y)))
 | a_wlred__sub_etvarmono1 : forall (aW:aworklist) (A1:typ) (X:typvar) (B1 B2:typ) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  aW  )  )  ->
     a_smono_typ  ( awl_to_aenv  aW  )  A1 ->
      (a_update_bound  aW   nil   X   A1  a_mode_ub__lower  aW2   aW3 )  ->
     a_wl_red  (   ( awl_app  aW3   aW2  )   )  ->
     a_wl_red (aworklist_conswork aW (work_sub A1 (typ_var_f X)))
 | a_wlred__sub_etvarmono2 : forall (aW:aworklist) (X:typvar) (B1 A1 A2:typ) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  aW  )  )  ->
     a_smono_typ  ( awl_to_aenv  aW  )  B1 ->
      (a_update_bound  aW   nil   X   B1  a_mode_ub__upper  aW2   aW3 )  ->
     a_wl_red  (   ( awl_app  aW3   aW2  )   )  ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_var_f X) B1))
 | a_wlred__sub_intersection1 : forall (aW:aworklist) (A1 B1 B2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork aW (work_sub A1 B1)) (work_sub A1 B2)) ->
     a_wl_red (aworklist_conswork aW (work_sub A1 (typ_intersection B1 B2)))
 | a_wlred__sub_intersection2 : forall (aW:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork aW (work_sub B1 A1)) ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_intersection B1 B2) A1))
 | a_wlred__sub_intersection3 : forall (aW:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork aW (work_sub B2 A1)) ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_intersection B1 B2) A1))
 | a_wlred__sub_union1 : forall (aW:aworklist) (B1 A1 A2:typ),
     a_wl_red (aworklist_conswork aW (work_sub B1 A1)) ->
     a_wl_red (aworklist_conswork aW (work_sub B1 (typ_union A1 A2)))
 | a_wlred__sub_union2 : forall (aW:aworklist) (B1 A1 A2:typ),
     a_wl_red (aworklist_conswork aW (work_sub B1 A2)) ->
     a_wl_red (aworklist_conswork aW (work_sub B1 (typ_union A1 A2)))
 | a_wlred__sub_union3 : forall (aW:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork aW (work_sub B1 A1)) (work_sub B2 A1)) ->
     a_wl_red (aworklist_conswork aW (work_sub (typ_union B1 B2) A1))
 | a_wlred__chk_sub : forall (aW:aworklist) (e:exp) (A1:typ),
     a_wl_red (aworklist_conswork aW (work_infer e (cont_sub A1))) ->
     a_wl_red (aworklist_conswork aW (work_check e A1))
 | a_wlred__chk_absarrow : forall (L:vars) (aW:aworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar aW x (abind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     a_wl_red (aworklist_conswork aW (work_check (exp_abs e) (typ_arrow A1 A2)))
 | a_wlred__chk_absevar : forall (L:vars) (aW:aworklist) (e:exp) (X:typvar) (A1 A2:typ) (X1 X2:typvar) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  aW  )  )  ->
      (a_update_bound  (aworklist_constvar (aworklist_constvar aW X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))  nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both  aW2   aW3 )  ->
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar  (   ( awl_app  aW3   aW2  )   )  x (abind_typ (typ_var_f X1))) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2))) )  ->
     a_wl_red (aworklist_conswork aW (work_check (exp_abs e) (typ_var_f X)))
 | a_wlred__chk_abstop : forall (L:vars) (aW:aworklist) (e:exp),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar aW x (abind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     a_wl_red (aworklist_conswork aW (work_check (exp_abs e) typ_top))
 | a_wlred__chk_inter : forall (aW:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork aW (work_check e A1)) (work_check e A2)) ->
     a_wl_red (aworklist_conswork aW (work_check e (typ_intersection A1 A2)))
 | a_wlred__chk_union1 : forall (aW:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork aW (work_check e A1)) ->
     a_wl_red (aworklist_conswork aW (work_check e (typ_union A1 A2)))
 | a_wlred__chk_union2 : forall (aW:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork aW (work_check e A2)) ->
     a_wl_red (aworklist_conswork aW (work_check e (typ_union A1 A2)))
 | a_wlred__inf_var : forall (aW:aworklist) (x:expvar) (c:cont) (A:typ),
      binds ( x )  ( (abind_typ A) ) (  ( awl_to_aenv  aW  )  )  ->
     a_wl_red (aworklist_conswork aW (work_apply c A)) ->
     a_wl_red (aworklist_conswork aW (work_infer (exp_var_f x) c))
 | a_wlred__inf_anno : forall (aW:aworklist) (e:exp) (A:typ) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork aW (work_apply c A)) (work_check e A)) ->
     a_wl_red (aworklist_conswork aW (work_infer  ( (exp_anno e A) )  c))
 | a_wlred__inf_tabs : forall (L:vars) (aW:aworklist) (e:exp) (A:typ) (c:cont) (aW2:aworklist),
     lc_aworklist aW ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar (aworklist_conswork aW2 (work_apply c  ( (typ_all A) ) )) X abind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork aW (work_infer (exp_tabs (body_anno e A)) c))
 | a_wlred__inf_unit : forall (aW:aworklist) (c:cont),
     a_wl_red (aworklist_conswork aW (work_apply c typ_unit)) ->
     a_wl_red (aworklist_conswork aW (work_infer exp_unit c))
 | a_wlred__inf_app : forall (aW:aworklist) (e1 e2:exp) (c:cont),
     a_wl_red (aworklist_conswork aW (work_infer e1  (  (cont_infabs  (  (cont_infapp e2 c)  ) )  ) )) ->
     a_wl_red (aworklist_conswork aW (work_infer  ( (exp_app e1 e2) )  c))
 | a_wlred__infapparrow : forall (aW:aworklist) (A1 A2:typ) (e:exp) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork aW (work_apply c A2)) (work_check e A1)) ->
     a_wl_red (aworklist_conswork aW (work_infapp (typ_arrow A1 A2) e c))
 | a_wlred__infabs_arr : forall (aW:aworklist) (A1 B1:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_apply c (typ_arrow A1 B1))) ->
     a_wl_red (aworklist_conswork aW (work_infabs (typ_arrow A1 B1) c))
 | a_wlred__infabs_evar : forall (aW:aworklist) (X:typvar) (c:cont) (A1 A2:typ) (X1 X2:typvar) (aW2 aW3:aworklist),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  aW  )  )  ->
      (a_update_bound  (aworklist_constvar (aworklist_constvar aW X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both  aW2   aW3 )  ->
     a_wl_red (aworklist_conswork  (   ( awl_app  aW3   aW2  )   )  (work_infabs (typ_arrow (typ_var_f X1) (typ_var_f X2)) c)) ->
     a_wl_red (aworklist_conswork aW (work_infabs (typ_var_f X) c))
 | a_wlred__infappbot : forall (aW:aworklist) (c:cont),
     a_wl_red (aworklist_conswork aW (work_infabs (typ_arrow typ_top typ_bot) c)) ->
     a_wl_red (aworklist_conswork aW (work_infabs typ_bot c))
 | a_wlred__infabs_inter1 : forall (aW:aworklist) (A1 A2:typ) (c:cont),
     lc_typ A2 ->
     a_wl_red (aworklist_conswork aW (work_infabs A1 c)) ->
     a_wl_red (aworklist_conswork aW (work_infabs (typ_intersection A1 A2) c))
 | a_wlred__infabs_inter2 : forall (aW:aworklist) (A1 A2:typ) (c:cont),
     lc_typ A1 ->
     a_wl_red (aworklist_conswork aW (work_infabs A2 c)) ->
     a_wl_red (aworklist_conswork aW (work_infabs (typ_intersection A1 A2) c))
 | a_wlred__infabs_union : forall (aW:aworklist) (A1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_infabs A1  (  (cont_infabsunion A2 c)  ) )) ->
     a_wl_red (aworklist_conswork aW (work_infabs (typ_union A1 A2) c))
 | a_wlred__infabsunion : forall (aW:aworklist) (B1 C1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_infabs A2  (  (cont_unioninfabs (typ_arrow B1 C1) c)  ) )) ->
     a_wl_red (aworklist_conswork aW (work_infabsunion (typ_arrow B1 C1) A2 c))
 | a_wlred__unioninfabs : forall (aW:aworklist) (B2 C2 B1 C1:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_apply c (typ_arrow  ( (typ_intersection B1 B2) )   ( (typ_union C1 C2) ) ))) ->
     a_wl_red (aworklist_conswork aW (work_unioninfabs (typ_arrow B2 C2) (typ_arrow B1 C1) c))
 | a_wlred__inf_tapp : forall (aW:aworklist) (e:exp) (B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_infer e (cont_inftapp B c))) ->
     a_wl_red (aworklist_conswork aW (work_infer (exp_tapp e B) c))
 | a_wlred__inftapp_all : forall (aW:aworklist) (A B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_apply c  (open_typ_wrt_typ  A   B ) )) ->
     a_wl_red (aworklist_conswork aW (work_inftapp (typ_all A) B c))
 | a_wlred__inftapp_bot : forall (aW:aworklist) (B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_apply c typ_bot)) ->
     a_wl_red (aworklist_conswork aW (work_inftapp typ_bot B c))
 | a_wlred__inftapp_inter1 : forall (aW:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_inftapp A1 B c)) ->
     a_wl_red (aworklist_conswork aW (work_inftapp (typ_intersection A1 A2) B c))
 | a_wlred__inftapp_inter2 : forall (aW:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_inftapp A2 B c)) ->
     a_wl_red (aworklist_conswork aW (work_inftapp (typ_intersection A1 A2) B c))
 | a_wlred__inftapp_union : forall (aW:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_inftapp A1 B  (  (cont_inftappunion A2 B c)  ) )) ->
     a_wl_red (aworklist_conswork aW (work_inftapp (typ_union A1 A2) B c))
 | a_wlred__inftappunion : forall (aW:aworklist) (C1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_inftapp A2 B  (  (cont_unioninftapp C1 c)  ) )) ->
     a_wl_red (aworklist_conswork aW (work_inftappunion C1 A2 B c))
 | a_wlred__unioninftapp : forall (aW:aworklist) (C2 C1:typ) (c:cont),
     a_wl_red (aworklist_conswork aW (work_apply c (typ_union C1 C2))) ->
     a_wl_red (aworklist_conswork aW (work_unioninftapp C2 C1 c))
 | d_wlred__applycont : forall (aW:aworklist) (w:work) (T1:typ) (c:cont),
     apply_cont c T1 w ->
     a_wl_red (aworklist_conswork aW w) ->
     a_wl_red (aworklist_conswork aW (work_apply c T1))   
.
