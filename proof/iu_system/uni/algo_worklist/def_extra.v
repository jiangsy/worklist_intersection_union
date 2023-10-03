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


(* TODO *)
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
 | d_wl_del__empty : a_wl_red aworklist_empty
 | d_wl_del__gc_var : forall (Γ:aworklist) (x:expvar) (A:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_consvar Γ x (abind_typ A))
 | d_wl_del__gc_tvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red Γ ->
     a_wl_red (aworklist_constvar Γ X abind_tvar_empty)
 | d_wl_del__gc_stvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red Γ ->
     a_wl_red (aworklist_constvar Γ X abind_stvar_empty)
 | d_wl_del__gc_etvar : forall (Γ:aworklist) (X:typvar) (A B:typ),
     a_wl_red (aworklist_conswork Γ (work_sub A B)) ->
     a_wl_red (aworklist_constvar Γ X (abind_bound A B))
 | d_wl_del__sub_top : forall (Γ:aworklist) (B1:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub B1 typ_top))
 | d_wl_del__sub_bot : forall (Γ:aworklist) (A:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub typ_bot A))
 | d_wl_del__sub_unit : forall (Γ:aworklist),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub typ_unit typ_unit))
 | d_wl_del__sub_tvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f X)))
 | d_wl_del__subarrow : forall (Γ:aworklist) (B1 B2 A1 A2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A1 B1)) (work_sub B2 A2)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_arrow B1 B2) (typ_arrow A1 A2)))
 | d_wl_del__sub_alll : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
     neq_all A1 ->
     neq_intersection A1 ->
     neq_union A1 ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )  A1)) )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_all B1) A1))
 | d_wl_del__sub_all : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_all B1) (typ_all A1)))
 | d_wl_del__sub_arrow1 : forall (L:vars) (Γ:aworklist) (X:typvar) (A1 A2 B1 B2:typ) (X1 X2:typvar),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_smono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) ->  
        (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__upper  Γ2   Γ3 ) /\ 
        (a_wl_red (aworklist_conswork  (   ( awl_app  Γ3   Γ2  )   )  (work_sub (typ_arrow (typ_var_f X1) (typ_var_f X2)) (typ_arrow A1 A2)))) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_arrow A1 A2)))
 | d_wl_del__sub_arrow2 : forall (L:vars) (Γ:aworklist) (A1 A2:typ) (X:typvar) (B1 B2:typ) (X1 X2:typvar),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_smono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (  forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) -> 
             (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__lower  Γ2   Γ3 )  /\
            a_wl_red (aworklist_conswork  (   ( awl_app  Γ3   Γ2  )   )  (work_sub (typ_arrow A1 A2) (typ_arrow (typ_var_f X1) (typ_var_f X2)))) )->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_arrow A1 A2) (typ_var_f X)))
 | d_wl_del__sub_etvar1 : forall (L:vars) (Γ:aworklist) (Y X:typvar) (B1 B2 B3 B4:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  Γ  )  )  ->     a_evs_in_wl Γ X Y ->
      a_evs_in_wl Γ X Y ->
      (  forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) -> 
            (a_update_bound  Γ   nil   X   (typ_var_f Y)  a_mode_ub__lower  Γ2   Γ3 )  /\
            a_wl_red  (   ( awl_app  Γ3   Γ2  )   ) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f Y) (typ_var_f X)))
 | d_wl_del__sub_etvar2 : forall (L:vars) (Γ:aworklist) (X Y:typvar) (B1 B2 B3 B4:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  Γ  )  )  ->
      a_evs_in_wl Γ X Y ->
      (  forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) -> 
            (a_update_bound  Γ   nil   X   (typ_var_f Y)  a_mode_ub__upper  Γ2   Γ3 )  /\
            a_wl_red  (   ( awl_app  Γ3   Γ2  )   ) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f Y)))
 | d_wl_del__sub_etvarmono1 : forall (L:vars) (Γ:aworklist) (A1:typ) (X:typvar) (B1 B2:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_smono_typ  ( awl_to_aenv  Γ  )  A1 ->
     (  forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) -> 
            (a_update_bound  Γ   nil   X   A1  a_mode_ub__lower  Γ2   Γ3 )  /\
            a_wl_red  (   ( awl_app  Γ3   Γ2  )   ) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub A1 (typ_var_f X)))
 | d_wl_del__sub_etvarmono2 : forall (L:vars) (Γ:aworklist) (X:typvar) (B1 A1 A2:typ),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_smono_typ  ( awl_to_aenv  Γ  )  B1 ->
     (  forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) -> 
            (a_update_bound  Γ   nil   X   B1  a_mode_ub__upper  Γ2   Γ3 ) /\  a_wl_red  (   ( awl_app  Γ3   Γ2  )   ) 
     ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) B1))
 | d_wl_del__sub_intersection1 : forall (Γ:aworklist) (A1 B1 B2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A1 B1)) (work_sub A1 B2)) ->
     a_wl_red (aworklist_conswork Γ (work_sub A1 (typ_intersection B1 B2)))
 | d_wl_del__sub_intersection2 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B1 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_intersection B1 B2) A1))
 | d_wl_del__sub_intersection3 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B2 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_intersection B1 B2) A1))
 | d_wl_del__sub_union1 : forall (Γ:aworklist) (B1 A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B1 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub B1 (typ_union A1 A2)))
 | d_wl_del__sub_union2 : forall (Γ:aworklist) (B1 A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B1 A2)) ->
     a_wl_red (aworklist_conswork Γ (work_sub B1 (typ_union A1 A2)))
 | d_wl_del__sub_union3 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub B1 A1)) (work_sub B2 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_union B1 B2) A1))
 | d_wl_del__chk_sub : forall (Γ:aworklist) (e:exp) (A1:typ),
     a_wl_red (aworklist_conswork Γ (work_infer e (cont_sub A1))) ->
     a_wl_red (aworklist_conswork Γ (work_check e A1))
 | d_wl_del__chk_absarrow : forall (L:vars) (Γ:aworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar Γ x (abind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) (typ_arrow A1 A2)))
 | d_wl_del__chk_absevar : forall (L:vars) (Γ:aworklist) (e:exp) (X:typvar) (A1 A2:typ) (X1 X2:typvar),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
      (  forall x X1 X2 Γ2 Γ3, x `notin` L -> X1 `notin` (L `union` (singleton x)) -> X2 `notin` (L `union` singleton x `union` singleton X1) -> 
            (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))  nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both  Γ2   Γ3 )  /\
            a_wl_red (aworklist_conswork (aworklist_consvar  (   ( awl_app  Γ3   Γ2  )   )  x (abind_typ (typ_var_f X1))) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2))) ) ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) (typ_var_f X)))
 | d_wl_del__chk_abstop : forall (L:vars) (Γ:aworklist) (e:exp),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar Γ x (abind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) typ_top))
 | d_wl_del__chk_inter : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_check e A1)) (work_check e A2)) ->
     a_wl_red (aworklist_conswork Γ (work_check e (typ_intersection A1 A2)))
 | d_wl_del__chk_union1 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_check e A1)) ->
     a_wl_red (aworklist_conswork Γ (work_check e (typ_union A1 A2)))
 | d_wl_del__chk_union2 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_check e A2)) ->
     a_wl_red (aworklist_conswork Γ (work_check e (typ_union A1 A2)))
 | d_wl_del__inf_var : forall (Γ:aworklist) (x:expvar) (c:cont) (A:typ),
      binds ( x )  ( (abind_typ A) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_wl_red (aworklist_conswork Γ (work_apply c A)) ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_var_f x) c))
 | d_wl_del__inf_anno : forall (Γ:aworklist) (e:exp) (A:typ) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_apply c A)) (work_check e A)) ->
     a_wl_red (aworklist_conswork Γ (work_infer  ( (exp_anno e A) )  c))
 | d_wl_del__inf_tabs : forall (L:vars) (Γ:aworklist) (e:exp) (A:typ) (c:cont) (Γ2:aworklist),
     lc_aworklist Γ ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar (aworklist_conswork Γ2 (work_apply c  ( (typ_all A) ) )) X abind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_tabs (body_anno e A)) c))
 | d_wl_del__inf_unit : forall (Γ:aworklist) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c typ_unit)) ->
     a_wl_red (aworklist_conswork Γ (work_infer exp_unit c))
 | d_wl_del__inf_app : forall (Γ:aworklist) (e1 e2:exp) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infer e1  (  (cont_infabs  (  (cont_infapp e2 c)  ) )  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_infer  ( (exp_app e1 e2) )  c))
 | d_wl_del__infapp : forall (Γ:aworklist) (A1 A2:typ) (e:exp) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_apply c A2)) (work_check e A1)) ->
     a_wl_red (aworklist_conswork Γ (work_infapp (typ_arrow A1 A2) e c))
 | d_wl_del__infabs_arr : forall (Γ:aworklist) (A1 B1:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c (typ_arrow A1 B1))) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_arrow A1 B1) c))
 | d_wl_del__infabs_bot : forall (Γ:aworklist) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_arrow typ_top typ_bot) c)) ->
     a_wl_red (aworklist_conswork Γ (work_infabs typ_bot c))
 | d_wl_del__infabs_all : forall (L:vars) (Γ:aworklist) (A:typ) (c:cont),
     (forall X, X `notin` L -> a_wl_red (aworklist_conswork  (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) c)) ) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_all A) c))
 | d_wl_del__infabs_inter1 : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     lc_typ A2 ->
     a_wl_red (aworklist_conswork Γ (work_infabs A1 c)) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c))
 | d_wl_del__infabs_inter2 : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     lc_typ A1 ->
     a_wl_red (aworklist_conswork Γ (work_infabs A2 c)) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c))
 | d_wl_del__infabs_union : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs A1  (  (cont_infabsunion A2 c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_union A1 A2) c))
 | d_wl_del__infabsunion : forall (Γ:aworklist) (B1 C1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs A2  (  (cont_unioninfabs (typ_arrow B1 C1) c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_infabsunion (typ_arrow B1 C1) A2 c))
 | d_wl_del__unioninfabs : forall (Γ:aworklist) (B2 C2 B1 C1:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c (typ_arrow  ( (typ_intersection B1 B2) )   ( (typ_union C1 C2) ) ))) ->
     a_wl_red (aworklist_conswork Γ (work_unioninfabs (typ_arrow B2 C2) (typ_arrow B1 C1) c))
 | d_wl_del__infabs_evar : forall (L:vars) (Γ:aworklist) (X:typvar) (c:cont) (A1 A2:typ) (X1 X2:typvar),
     binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
     (forall X1 X2 Γ2 Γ3, X1 `notin` L -> X2 `notin` (L `union` singleton X1) -> 
       (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   nil   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both  Γ2   Γ3 )  /\
       a_wl_red (aworklist_conswork  (   ( awl_app  Γ3   Γ2  )   )  (work_infabs (typ_arrow (typ_var_f X1) (typ_var_f X2)) c))
     ) ->
    a_wl_red (aworklist_conswork Γ (work_infabs (typ_var_f X) c))
 | d_wl_del__inf_tapp : forall (Γ:aworklist) (e:exp) (B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infer e (cont_inftapp B c))) ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_tapp e B) c))
 | d_wl_del__inftapp_all : forall (Γ:aworklist) (A B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c  (open_typ_wrt_typ  A   B ) )) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_all A) B c))
 | d_wl_del__inftapp_bot : forall (Γ:aworklist) (B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c typ_bot)) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp typ_bot B c))
 | d_wl_del__inftapp_inter1 : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A1 B c)) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B c))
 | d_wl_del__inftapp_inter2 : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A2 B c)) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B c))
 | d_wl_del__inftapp_union : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A1 B  (  (cont_inftappunion A2 B c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_union A1 A2) B c))
 | d_wl_del__inftappunion : forall (Γ:aworklist) (C1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A2 B  (  (cont_unioninftapp C1 c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_inftappunion C1 A2 B c))
 | d_wl_del__unioninftapp : forall (Γ:aworklist) (C2 C1:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c (typ_union C1 C2))) ->
     a_wl_red (aworklist_conswork Γ (work_unioninftapp C2 C1 c))
 | d_wl_red__applycont : forall (Γ:aworklist) (w:work) (T1:typ) (c:cont),
     apply_cont c T1 w ->
     a_wl_red (aworklist_conswork Γ w) ->
     a_wl_red (aworklist_conswork Γ (work_apply c T1))   
.


Declare Scope aworklist_scope.
Delimit Scope aworklist_scope with aworklist.
Bind Scope aworklist_scope with aworklist.



Notation " x ~ A ; Γ " :=
  (aworklist_consvar Γ x (abind_typ A))
      (at level 58, A at next level, right associativity) : aworklist_scope.
    
Notation " X ~ ▫ ; Γ " :=
  (aworklist_constvar Γ X abind_tvar_empty)
      (at level 58, right associativity) : aworklist_scope.

Notation " X ~ ▪ ; Γ " :=
  (aworklist_constvar Γ X abind_stvar_empty)
      (at level 58, right associativity) : aworklist_scope.

Notation " W ⫤ Γ " :=
  (aworklist_conswork Γ W)
      (at level 58, right associativity) : aworklist_scope.

Notation " Γ ⟶ᵃʷ⁎⋅ " :=
  (a_wl_red Γ)
      (at level 58, no associativity) : type_scope.

Notation " ⊢ᵃ Γ " :=
  (a_wf_wl Γ)
      (at level 58, no associativity) : type_scope.
    