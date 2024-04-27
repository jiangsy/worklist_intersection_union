Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.prop_ln.
Require Export uni.def_ott.
Require Export uni.decl_worklist.def.


Definition fv_env_gen (fv : abind -> atoms) (E : aenv) : atoms :=
  fold_right (fun xb acc => match xb with (x , b) => acc `union` fv b end ) {} E.

Definition ftvar_in_aenv := fv_env_gen ftvar_in_abind.

Inductive a_bound_mode := 
  | a_bound_mode__upper
  | a_bound_mode__lower.

Fixpoint awl_app (Γ1 Γ2 : aworklist) :=
  match Γ1 with 
  | aworklist_empty => Γ2 
  | aworklist_constvar Γ1' X b => aworklist_constvar (awl_app Γ1' Γ2) X b
  | aworklist_consvar Γ1' x b => aworklist_consvar (awl_app Γ1' Γ2) x b
  | aworklist_conswork Γ1' w => aworklist_conswork (awl_app Γ1' Γ2) w
  end.

Fixpoint awl_rev_app (Γ1 Γ2 : aworklist) :=
    match Γ1 with 
    | aworklist_empty => Γ2 
    | aworklist_constvar Γ1' X b => awl_rev_app Γ1' (aworklist_constvar Γ2 X b)
    | aworklist_consvar Γ1' x b => awl_rev_app Γ1' (aworklist_consvar Γ2 x b)
    | aworklist_conswork Γ1' w => awl_rev_app Γ1' (aworklist_conswork Γ2 w)
    end.

Fixpoint aenv_to_awl (E : list (atom*abind)) :=
  match E with 
  | nil => aworklist_empty
  | (x, abind_typ A1) :: E'  => aworklist_consvar (aenv_to_awl E') x (abind_typ A1)
  | (X, b) :: E'  => aworklist_constvar (aenv_to_awl E') X b
  end.



Inductive lub : aworklist -> typ -> typ -> aworklist -> typ -> Prop := 
  | lub__unit : forall Γ, lub Γ typ_unit typ_unit Γ typ_unit
  | lub__top : forall Γ T, lub Γ typ_top T Γ typ_top
  | lub__bot : forall Γ T, lub Γ typ_bot T Γ T
  | lub__bot : forall Γ T, lub Γ typ_bot T Γ T
  .

Inductive glb : aworklist -> typ -> typ -> aworklist -> typ -> Prop := 
  | glb__unit : forall Γ, glb Γ typ_unit typ_unit Γ typ_unit.


Inductive a_update_bound
  : aworklist -> typvar -> typ -> a_bound_mode ->  list (atom*abind) -> aworklist -> aworklist -> typ -> typ -> Prop :=
  | a_ub__lb_stop : forall Γ1 Γ2 X A LB UB LB1, 
    X `notin` ftvar_in_typ A -> 
    lub Γ1 A LB Γ2 LB1 ->
    a_update_bound (aworklist_constvar Γ1 X (abind_bound LB UB)) X A a_bound_mode__lower nil Γ2 aworklist_empty LB1 UB
  | a_ub__ub_stop : forall Γ1 Γ2 X A LB UB UB1, 
    X `notin` ftvar_in_typ A -> 
    glb Γ1 A UB Γ2 UB1 ->
    a_update_bound (aworklist_constvar Γ1 X (abind_bound LB UB)) X A a_bound_mode__upper nil Γ1 aworklist_empty LB UB1
  | a_ub__etvar_move : forall Γ1 X1 LB1 UB1 E X A m Γ2 Γ3 LB UB,
    X `notin` ftvar_in_abind (abind_bound LB1 UB1) ->
    a_update_bound Γ1 X A m E Γ2 Γ3 LB UB ->
    a_update_bound (aworklist_constvar Γ1 X1 (abind_bound LB1 UB1)) X A m ( (X1 , (abind_bound LB1 UB1)) :: E ) Γ2 Γ3 LB UB
  | a_ub__etvar_stay : forall Γ1 X1 LB1 UB1 E X A m Γ2 Γ3 LB UB ,
    X1 `notin` ftvar_in_typ A /\ X1 `notin` ftvar_in_aenv E ->
    a_update_bound Γ1 X A m E Γ2 Γ3 LB UB ->
    a_update_bound (aworklist_constvar Γ1 X1 (abind_bound LB1 UB1)) X A m E Γ2 (aworklist_constvar Γ3 X1 (abind_bound LB1 UB1)) LB UB
  | a_ub__tvar_stay : forall Γ1 X1 E X A m Γ2 Γ3 LB UB ,
    X1 `notin` ftvar_in_typ A /\ X1 `notin` ftvar_in_aenv E ->
    a_update_bound Γ1 X A m E Γ2 Γ3 LB UB  ->
    a_update_bound (aworklist_constvar Γ1 X1 abind_tvar_empty) X A m E Γ2 (aworklist_constvar Γ3 X1 abind_tvar_empty) LB UB  
  | a_ub__stvar_stay : forall Γ1 X1 E X A m Γ2 Γ3 LB UB ,
    X1 `notin` ftvar_in_typ A /\ X1 `notin` ftvar_in_aenv E ->
    a_update_bound Γ1 X A m E Γ2 Γ3 LB UB ->
    a_update_bound (aworklist_constvar Γ1 X1 abind_stvar_empty) X A m E Γ2  (aworklist_constvar Γ3 X1 abind_stvar_empty) LB UB
  | a_ub__w_stay : forall Γ1 w1 E X A m Γ2 Γ3 LB UB,
    a_update_bound Γ1 X A m E Γ2 Γ3 LB UB ->
    a_update_bound (aworklist_conswork Γ1 w1) X A m E Γ2 (aworklist_conswork Γ3 w1) LB UB 
  | a_ub__var_stay : forall Γ1 x1 b1 E X A m Γ2 Γ3 LB UB,
    a_update_bound Γ1 X A m E Γ2 Γ3 LB UB  ->
    a_update_bound (aworklist_consvar Γ1 x1 b1) X A m E Γ2 (aworklist_consvar Γ3 x1 b1) LB UB 
  .

(* defns Jaworklist_reduction *)
Inductive a_wl_red : aworklist -> Prop :=    (* defn a_wl_red *)
 | a_wl_red__empty : a_wl_red aworklist_empty
 | a_wl_red__gc_var : forall (Γ:aworklist) (x:expvar) (A:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_consvar Γ x (abind_typ A))
 | a_wl_red__gc_tvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red Γ ->
     a_wl_red (aworklist_constvar Γ X abind_tvar_empty)
 | a_wl_red__gc_stvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red Γ ->
     a_wl_red (aworklist_constvar Γ X abind_stvar_empty)
 | a_wl_red__gc_etvar : forall (Γ:aworklist) (X:typvar) (A B:typ),
     a_wl_red (aworklist_conswork Γ (work_sub A B)) ->
     a_wl_red (aworklist_constvar Γ X (abind_bound A B))
 | a_wl_red__sub_top : forall (Γ:aworklist) (B1:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub B1 typ_top))
 | a_wl_red__sub_bot : forall (Γ:aworklist) (A:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub typ_bot A))
 | a_wl_red__sub_unit : forall (Γ:aworklist),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub typ_unit typ_unit))
 | a_wl_red__sub_tvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red Γ ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f X)))
 | a_wl_red__subarrow : forall (Γ:aworklist) (B1 B2 A1 A2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A1 B1)) (work_sub B2 A2)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_arrow B1 B2) (typ_arrow A1 A2)))
 | a_wl_red__sub_alll : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
     neq_all A1 ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )  A1)) )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_all B1) A1))
 | a_wl_red__sub_all : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_all B1) (typ_all A1)))
 | a_wl_red__sub_arrow1 : forall (L:vars) (Γ:aworklist) (X:typvar) (A1 A2 B1 B2:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ2 Γ3 E LB UB,
        (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_bound_mode__upper E Γ2 Γ3 LB UB ) ->
        (a_wl_red (aworklist_conswork  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )   )  (work_sub (typ_arrow (typ_var_f X1) (typ_var_f X2)) (typ_arrow A1 A2)))) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_arrow A1 A2)))
 | a_wl_red__sub_arrow2 : forall (L:vars) (Γ:aworklist) (A1 A2:typ) (X:typvar) (B1 B2:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ2 Γ3 E LB UB,
             (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_bound_mode__lower  E Γ2  Γ3 LB UB ) ->
            a_wl_red (aworklist_conswork  (  (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )   )  (work_sub (typ_arrow A1 A2) (typ_arrow (typ_var_f X1) (typ_var_f X2)))) )->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_arrow A1 A2) (typ_var_f X)))
 | a_wl_red__sub_etvar1 : forall (L:vars) (E:aenv) (Γ Γ2 Γ3:aworklist) (Y X:typvar) (B1 B2 B3 B4 LB UB:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  Γ  )  )  ->     a_evs_in_wl Γ X Y ->
      a_evs_in_wl Γ X Y ->
      (a_update_bound  Γ  X   (typ_var_f Y)  a_bound_mode__lower  E Γ2   Γ3 LB UB)  ->
       a_wl_red  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f Y) (typ_var_f X)))
 | a_wl_red__sub_etvar2 : forall (L:vars) (E:aenv) (Γ Γ2 Γ3:aworklist) (X Y:typvar) (B1 B2 B3 B4 LB UB:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  Γ  )  )  ->
      a_evs_in_wl Γ X Y ->
      (a_update_bound  Γ  X   (typ_var_f Y)  a_bound_mode__upper E Γ2   Γ3 LB UB)  ->
      a_wl_red  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f Y)))
 | a_wl_red__sub_etvarmono1 : forall (L:vars)  (E:aenv) (Γ Γ2 Γ3:aworklist) (A1:typ) (X:typvar) (B1 B2 LB UB:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_mono_typ  ( awl_to_aenv  Γ  )  A1 ->
     (a_update_bound  Γ  X   A1  a_bound_mode__lower E Γ2 Γ3 LB UB )  ->
      a_wl_red  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) ) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub A1 (typ_var_f X)))
 | a_wl_red__sub_etvarmono2 : forall (L:vars) (E:aenv) (Γ Γ2 Γ3:aworklist) (X:typvar) (B1 A1 A2 LB UB:typ),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_mono_typ  ( awl_to_aenv  Γ  )  B1 ->
     a_update_bound  Γ  X   B1  a_bound_mode__upper E  Γ2   Γ3 LB UB->
      a_wl_red  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) B1))
 | a_wl_red__chk_sub : forall (Γ:aworklist) (e:exp) (A1:typ),
     a_wl_red (aworklist_conswork Γ (work_infer e (cont_sub A1))) ->
     a_wl_red (aworklist_conswork Γ (work_check e A1))
 | a_wl_red__chk_absarrow : forall (L:vars) (Γ:aworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar Γ x (abind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) (typ_arrow A1 A2)))
 | a_wl_red__chk_absevar : forall (L:vars) (Γ:aworklist) (e:exp) (X:typvar) (A1 A2:typ) (X1 X2:typvar),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
      (  forall x, x `notin` L -> forall X1, X1 `notin` (L `union` (singleton x)) -> forall X2, X2 `notin` (L `union` singleton x `union` singleton X1) -> forall Γ2 Γ3 E LB UB,
            (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))  X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both E  Γ2   Γ3 LB UB)  ->
            a_wl_red (aworklist_conswork (aworklist_consvar  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )  x (abind_typ (typ_var_f X1))) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2))) ) ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) (typ_var_f X)))
 | a_wl_red__chk_abstop : forall (L:vars) (Γ:aworklist) (e:exp),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar Γ x (abind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) typ_top))
 | a_wl_red__inf_var : forall (Γ:aworklist) (x:expvar) (c:cont) (A:typ),
      binds ( x )  ( (abind_typ A) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_wl_red (aworklist_conswork Γ (work_apply c A)) ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_var_f x) c))
 | a_wl_red__inf_anno : forall (Γ:aworklist) (e:exp) (A:typ) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_apply c A)) (work_check e A)) ->
     a_wl_red (aworklist_conswork Γ (work_infer  ( (exp_anno e A) )  c))
 | a_wl_red__inf_tabs : forall (L:vars) (Γ:aworklist) (e:exp) (A:typ) (c:cont) (Γ2:aworklist),
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar (aworklist_conswork Γ2 (work_apply c  ( (typ_all A) ) )) X abind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_tabs (body_anno e A)) c))
 | a_wl_red__inf_unit : forall (Γ:aworklist) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c typ_unit)) ->
     a_wl_red (aworklist_conswork Γ (work_infer exp_unit c))
 | a_wl_red__inf_app : forall (Γ:aworklist) (e1 e2:exp) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infer e1  (  (cont_infabs  (  (cont_infapp e2 c)  ) )  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_infer  ( (exp_app e1 e2) )  c))
 | a_wl_red__infapp : forall (Γ:aworklist) (A1 A2:typ) (e:exp) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_check e A1)) (work_apply c A2)) ->
     a_wl_red (aworklist_conswork Γ (work_infapp (typ_arrow A1 A2) e c))
 | a_wl_red__infabs_arr : forall (Γ:aworklist) (A1 B1:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c (typ_arrow A1 B1))) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_arrow A1 B1) c))
 | a_wl_red__infabs_bot : forall (Γ:aworklist) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_arrow typ_top typ_bot) c)) ->
     a_wl_red (aworklist_conswork Γ (work_infabs typ_bot c))
 | a_wl_red__infabs_all : forall (L:vars) (Γ:aworklist) (A:typ) (c:cont),
     (forall X, X `notin` L -> a_wl_red (aworklist_conswork  (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) c)) ) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_all A) c))
 | a_wl_red__infabs_evar : forall (L:vars) (Γ:aworklist) (X:typvar) (c:cont) (A1 A2:typ) (X1 X2:typvar),
     binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
     (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall E Γ2 Γ3 LB UB,
         (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))  X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both  E  Γ2   Γ3 LB UB)  /\
       a_wl_red (aworklist_conswork  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )   )  (work_infabs (typ_arrow (typ_var_f X1) (typ_var_f X2)) c))
     ) ->
    a_wl_red (aworklist_conswork Γ (work_infabs (typ_var_f X) c))
 | a_wl_red__inf_tapp : forall (Γ:aworklist) (e:exp) (B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infer e (cont_inftapp B c))) ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_tapp e B) c))
 | a_wl_red__inftapp_all : forall (Γ:aworklist) (A B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c  (open_typ_wrt_typ  A   B ) )) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_all A) B c))
 | a_wl_red__inftapp_bot : forall (Γ:aworklist) (B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c typ_bot)) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp typ_bot B c))
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
    