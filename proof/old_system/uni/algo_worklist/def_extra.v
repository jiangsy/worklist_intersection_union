Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.prop_ln.
Require Export uni.def_ott.
Require Export uni.decl_worklist.def.


Definition fv_env_gen (fv : abind -> atoms) (E : aenv) : atoms :=
  fold_right (fun xb acc => match xb with (x , b) => acc `union` fv b end ) {} E.

Definition ftvar_in_aenv := fv_env_gen ftvar_in_abind.


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

(* Fixpoint aenv_to_awl (E : list typvar) :=
  match E with 
  | nil => aworklist_empty
  | (x, abind_var_typ A1) :: E'  => aworklist_consvar (aenv_to_awl E') x (abind_var_typ A1)
  | (X, b) :: E'  => aworklist_constvar (aenv_to_awl E') X b
  end. *)


Fixpoint etvar_list_to_awl (E : list typvar) :=
  match E with 
  | nil => aworklist_empty
  | X :: E  => aworklist_constvar (etvar_list_to_awl E) X abind_etvar_empty
  end.


Inductive aworklist_subst : aworklist -> typvar -> typ ->  list typvar -> aworklist -> aworklist -> Prop :=
    | a_ws__stop : forall Γ X A , 
        aworklist_subst (aworklist_constvar Γ X (abind_etvar_empty)) X A nil Γ aworklist_empty
    | a_ws__var_stay : forall Γ E X Y A B Γ1 Γ2,
        aworklist_subst Γ X A E Γ1 Γ2 ->
        aworklist_subst (aworklist_consvar Γ Y (abind_var_typ B)) X A E Γ1 (aworklist_consvar Γ2 Y (abind_var_typ B))
    | a_ws__tvar_stay : forall Γ E X Y A Γ1 Γ2,
        aworklist_subst Γ X A E Γ1 Γ2 ->
        Y <> X ->
        Y `notin` ftvar_in_typ A -> 
        aworklist_subst (aworklist_constvar Γ Y (abind_tvar_empty)) X A E Γ1 (aworklist_constvar Γ2 Y (abind_tvar_empty))
    | a_ws__stvar_stay : forall Γ E X Y A Γ1 Γ2,
        aworklist_subst Γ X A E Γ1 Γ2 ->
        Y <> X ->
        Y `notin` ftvar_in_typ A -> 
        aworklist_subst (aworklist_constvar Γ Y (abind_stvar_empty)) X A E Γ1 (aworklist_constvar Γ2 Y (abind_stvar_empty))
    | a_ws__work_stay : forall Γ E X A w Γ1 Γ2,
        aworklist_subst Γ X A E Γ1 Γ2 ->
        aworklist_subst (aworklist_conswork Γ w) X A E Γ1 (aworklist_conswork Γ2 w)
    | a_ws__etvar_stay : forall Γ E X Y A Γ1 Γ2,
        aworklist_subst Γ X A E Γ1 Γ2 ->
        Y <> X ->
        Y `notin` ftvar_in_typ A -> 
        aworklist_subst (aworklist_constvar Γ Y (abind_etvar_empty)) X A E Γ1 (aworklist_constvar Γ2 Y (abind_etvar_empty))
    | a_ws__etvar_move : forall Γ E X Y A Γ1 Γ2,
        aworklist_subst Γ X A E Γ1 Γ2 ->
        Y <> X ->
        aworklist_subst (aworklist_constvar Γ Y (abind_etvar_empty)) X A (Y :: E) Γ1 Γ2
    .


(* defns Jaworklist_reduction *)
Inductive a_wl_red : aworklist -> Prop :=    (* defn a_wl_red *)
 | a_wl_red__empty : a_wl_red aworklist_empty
 | a_wl_red__gc_var : forall (Γ:aworklist) (x:expvar) (A:typ),
     a_wl_red Γ ->
     a_wl_red (aworklist_consvar Γ x (abind_var_typ A))
 | a_wl_red__gc_tvar : forall (Γ:aworklist) (X:typvar) (b:abind),
     a_wl_red Γ ->
     (* b = abind_tvar_empty \/ b = abind_stvar_empty \/ abind_etvar_empty*)
     a_wl_red (aworklist_constvar Γ X b)
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
     neq_intersection A1 ->
     neq_union A1 ->
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )  A1)) )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_all B1) A1))
 | a_wl_red__sub_all : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
      ( forall X , X \notin  L  -> a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_all B1) (typ_all A1)))
 | a_wl_red__sub_arrow1 : forall (L:vars) (Γ:aworklist) (X:typvar) (A1 A2:typ),
      binds ( X )  ( abind_etvar_empty ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ1 Γ2 E,
        (aworklist_subst (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_arrow A1 A2))) X (typ_arrow (typ_var_f X1) (typ_var_f X2)) E Γ1 Γ2) ->
        (a_wl_red  (awl_app (subst_tvar_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) (awl_app (etvar_list_to_awl E) Γ1) )   ) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_arrow A1 A2)))
 | a_wl_red__sub_arrow2 : forall (L:vars) (Γ:aworklist) (A1 A2:typ) (X:typvar),
      binds ( X )  ( abind_etvar_empty ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ1 Γ2 E,
        (aworklist_subst (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_arrow A1 A2))) X (typ_arrow (typ_var_f X1) (typ_var_f X2)) E Γ1 Γ2) ->
        (a_wl_red  (awl_app (subst_tvar_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) (awl_app (etvar_list_to_awl E) Γ1) )   ) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_arrow A1 A2) (typ_var_f X)))
 | a_wl_red__sub_etvarmono1 : forall (E:list typvar) (Γ Γ1 Γ2:aworklist) (X:typvar) (A:typ),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
      a_mono_typ  ( awl_to_aenv  Γ  )  A ->
      X `notin` ftvar_in_typ A ->
      (aworklist_subst (aworklist_conswork Γ (work_sub A (typ_var_f X)) X A E Γ1 Γ2)) ->
      a_wl_red   (awl_app (subst_tvar_in_aworklist A X Γ2) (awl_app (etvar_list_to_awl E) Γ1) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub A (typ_var_f X)))
 | a_wl_red__sub_etvarmono2 : forall (E:list typvar) (Γ Γ1 Γ2:aworklist) (X:typvar) (B:typ),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
     a_mono_typ  ( awl_to_aenv  Γ  )  B ->
     X `notin` ftvar_in_typ B ->
     (aworklist_subst (aworklist_conswork Γ (work_sub (typ_var_f X) B)) X B E Γ1 Γ2) ->
     a_wl_red   (awl_app (subst_tvar_in_aworklist B X Γ2) (awl_app (etvar_list_to_awl E) Γ1) ) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_var_f X) B))
 | a_wl_red__sub_intersection1 : forall (Γ:aworklist) (A1 B1 B2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A1 B1)) (work_sub A1 B2)) ->
     a_wl_red (aworklist_conswork Γ (work_sub A1 (typ_intersection B1 B2)))
 | a_wl_red__sub_intersection2 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B1 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_intersection B1 B2) A1))
 | a_wl_red__sub_intersection3 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B2 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_intersection B1 B2) A1))
 | a_wl_red__sub_union1 : forall (Γ:aworklist) (B1 A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B1 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub B1 (typ_union A1 A2)))
 | a_wl_red__sub_union2 : forall (Γ:aworklist) (B1 A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_sub B1 A2)) ->
     a_wl_red (aworklist_conswork Γ (work_sub B1 (typ_union A1 A2)))
 | a_wl_red__sub_union3 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub B1 A1)) (work_sub B2 A1)) ->
     a_wl_red (aworklist_conswork Γ (work_sub (typ_union B1 B2) A1))
 | a_wl_red__chk_sub : forall (Γ:aworklist) (e:exp) (A1:typ),
     a_wl_red (aworklist_conswork Γ (work_infer e (cont_sub A1))) ->
     a_wl_red (aworklist_conswork Γ (work_check e A1))
 | a_wl_red__chk_absarrow : forall (L:vars) (Γ:aworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar Γ x (abind_var_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) (typ_arrow A1 A2)))
 | a_wl_red__chk_absetvar : forall (L:vars) (Γ:aworklist) (e:exp) (X:typvar),
      binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
      (  forall x, x `notin` L -> forall X1, X1 `notin` (L `union` (singleton x)) -> forall X2, X2 `notin` (L `union` singleton x `union` singleton X1) -> forall Γ1 Γ2 E,
            (aworklist_subst (aworklist_conswork (aworklist_consvar (aworklist_constvar (aworklist_constvar Γ X1 abind_etvar_empty) X2 abind_etvar_empty) x (abind_var_typ (typ_var_f X1)))  (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2))) X  
                 (typ_arrow (typ_var_f X1) (typ_var_f X2))  E  Γ1  Γ2)  ->
            a_wl_red  (   (awl_app (subst_tvar_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) (awl_app (etvar_list_to_awl E) Γ1) ) )  ) ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) (typ_var_f X)))
 | a_wl_red__chk_abstop : forall (L:vars) (Γ:aworklist) (e:exp),
      ( forall x , x \notin  L  -> a_wl_red (aworklist_conswork (aworklist_consvar Γ x (abind_var_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     a_wl_red (aworklist_conswork Γ (work_check (exp_abs e) typ_top))
 | a_wl_red__chk_inter : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_check e A1)) (work_check e A2)) ->
     a_wl_red (aworklist_conswork Γ (work_check e (typ_intersection A1 A2)))
 | a_wl_red__chk_union1 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_check e A1)) ->
     a_wl_red (aworklist_conswork Γ (work_check e (typ_union A1 A2)))
 | a_wl_red__chk_union2 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red (aworklist_conswork Γ (work_check e A2)) ->
     a_wl_red (aworklist_conswork Γ (work_check e (typ_union A1 A2)))
 | a_wl_red__inf_var : forall (Γ:aworklist) (x:expvar) (c:cont) (A:typ),
      binds ( x )  ( (abind_var_typ A) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_wl_red (aworklist_conswork Γ (work_apply c A)) ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_var_f x) c))
 | a_wl_red__inf_anno : forall (Γ:aworklist) (e:exp) (A:typ) (c:cont),
     a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_apply c A)) (work_check e A)) ->
     a_wl_red (aworklist_conswork Γ (work_infer  ( (exp_anno e A) )  c))
 | a_wl_red__inf_tabs : forall (L:vars) (Γ:aworklist) (e:exp) (A:typ) (c:cont),
      ( forall X , X \notin  L  -> 
        a_wl_red (aworklist_conswork (aworklist_constvar (aworklist_conswork Γ (work_apply c  ( (typ_all A) ) )) X abind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
     a_wl_red (aworklist_conswork Γ (work_infer (exp_tabs (body_anno e A)) c))
 | a_wl_red__inf_abs_mono : forall (L:vars) (Γ:aworklist) (e:exp) (c:cont),
    (forall x, x `notin` L -> forall X1, X1 `notin` (L `union` singleton x) -> forall X2, X2 `notin` (L `union` singleton x `union` singleton X1) ->
        a_wl_red (aworklist_conswork (aworklist_consvar (aworklist_conswork (aworklist_constvar (aworklist_constvar Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_apply c (typ_arrow (typ_var_f X1) (typ_var_f X2)))) x (abind_var_typ (typ_var_f X1)) ) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2)))
        ) ->
    a_wl_red (aworklist_conswork Γ (work_infer (exp_abs e) c))
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
     (forall X, X `notin` L -> a_wl_red (aworklist_conswork  (aworklist_constvar Γ X abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) c)) ) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_all A) c))
 | a_wl_red__infabs_inter1 : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs A1 c)) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c))
 | a_wl_red__infabs_inter2 : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs A2 c)) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c))
 | a_wl_red__infabs_union : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs A1  (  (cont_infabsunion A2 c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_infabs (typ_union A1 A2) c))
 | a_wl_red__infabsunion : forall (Γ:aworklist) (B1 C1 A2:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_infabs A2  (  (cont_unioninfabs (typ_arrow B1 C1) c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_infabsunion (typ_arrow B1 C1) A2 c))
 | a_wl_red__unioninfabs : forall (Γ:aworklist) (B2 C2 B1 C1:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c (typ_arrow  ( (typ_intersection B1 B2) )   ( (typ_union C1 C2) ) ))) ->
     a_wl_red (aworklist_conswork Γ (work_unioninfabs (typ_arrow B1 C1) (typ_arrow B2 C2) c))
 | a_wl_red__infabs_etvar : forall (L:vars) (Γ:aworklist) (X:typvar) (c:cont),
     binds ( X )  abind_etvar_empty (  ( awl_to_aenv  Γ  )  )  ->
     (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall E Γ1 Γ2,
         (aworklist_subst (aworklist_conswork (aworklist_constvar (aworklist_constvar Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_infabs (typ_arrow (typ_var_f X1) (typ_var_f X2)) c))  X   (typ_arrow (typ_var_f X1) (typ_var_f X2))    E  Γ1 Γ2) ->
       a_wl_red ( (awl_app (subst_tvar_in_aworklist (typ_arrow (typ_var_f X1) (typ_var_f X2)) X Γ2) (awl_app (etvar_list_to_awl E) Γ1) )  )
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
 | a_wl_red__inftapp_inter1 : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A1 B c)) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B c))
 | a_wl_red__inftapp_inter2 : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A2 B c)) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B c))
 | a_wl_red__inftapp_union : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A1 B  (  (cont_inftappunion A2 B c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_inftapp (typ_union A1 A2) B c))
 | a_wl_red__inftappunion : forall (Γ:aworklist) (C1 A2 B:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_inftapp A2 B  (  (cont_unioninftapp C1 c)  ) )) ->
     a_wl_red (aworklist_conswork Γ (work_inftappunion C1 A2 B c))
 | a_wl_red__unioninftapp : forall (Γ:aworklist) (C2 C1:typ) (c:cont),
     a_wl_red (aworklist_conswork Γ (work_apply c (typ_union C1 C2))) ->
     a_wl_red (aworklist_conswork Γ (work_unioninftapp C1 C2 c))
 | a_wl_red__applycont : forall (Γ:aworklist) (w:work) (T1:typ) (c:cont),
     apply_cont c T1 w ->
     a_wl_red (aworklist_conswork Γ w) ->
     a_wl_red (aworklist_conswork Γ (work_apply c T1))   
.

     
     

(* defns Jaworklist_reduction *)
(*
Inductive a_wl_red_ss : aworklist -> aworklist -> Prop :=    (* defn a_wl_red_ss *)
 | a_wl_red_ss__empty : a_wl_red_ss aworklist_empty aworklist_empty
 | a_wl_red_ss__gc_var : forall (Γ:aworklist) (x:expvar) (A:typ),
     a_wl_red_ss (aworklist_consvar Γ x (abind_var_typ A)) Γ
 | a_wl_red_ss__gc_tvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red_ss (aworklist_constvar Γ X abind_tvar_empty) Γ
 | a_wl_red_ss__gc_stvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red_ss (aworklist_constvar Γ X abind_stvar_empty) Γ
 | a_wl_red_ss__gc_etvar : forall (Γ:aworklist) (X:typvar) (A B:typ),
     a_wl_red_ss (aworklist_constvar Γ X (abind_bound A B))
                 (aworklist_conswork Γ (work_sub A B))
 | a_wl_red_ss__sub_top : forall (Γ:aworklist) (B1:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub B1 typ_top)) Γ
 | a_wl_red_ss__sub_bot : forall (Γ:aworklist) (A:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub typ_bot A)) Γ
 | a_wl_red_ss__sub_unit : forall (Γ:aworklist),
     a_wl_red_ss (aworklist_conswork Γ (work_sub typ_unit typ_unit)) Γ
 | a_wl_red_ss__sub_tvar : forall (Γ:aworklist) (X:typvar),
     a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f X))) Γ
 | a_wl_red_ss__subarrow : forall (Γ:aworklist) (B1 B2 A1 A2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_arrow B1 B2) (typ_arrow A1 A2)))
                 (aworklist_conswork (aworklist_conswork Γ (work_sub A1 B1)) (work_sub B2 A2))
 | a_wl_red_ss__sub_alll : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
     neq_all A1 ->
     neq_intersection A1 ->
     neq_union A1 ->
      ( forall X , X \notin  L ->
        a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_all B1) A1))
                    (aworklist_conswork (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )  A1)) )
 | a_wl_red_ss__sub_all : forall (L:vars) (Γ:aworklist) (B1 A1:typ),
      ( forall X , X \notin  L ->
        a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_all B1) (typ_all A1)))
                    (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ B1 (typ_var_f X) )   ( open_typ_wrt_typ A1 (typ_var_f X) ) )) )
 | a_wl_red_ss__sub_arrow1 : forall (L:vars) (Γ:aworklist) (X:typvar) (A1 A2 B1 B2:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ2 Γ3 E LB UB,
        (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__upper E Γ2 Γ3 LB UB ) ->
        (a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_arrow A1 A2)))
                     (aworklist_conswork  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )   )  (work_sub (typ_arrow (typ_var_f X1) (typ_var_f X2)) (typ_arrow A1 A2)))) )
 | a_wl_red_ss__sub_arrow2 : forall (L:vars) (Γ:aworklist) (A1 A2:typ) (X:typvar) (B1 B2:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      ( a_mono_typ   ( awl_to_aenv  Γ  )     ( (typ_arrow A1 A2) )   -> False )  ->
      (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall Γ2 Γ3 E LB UB,
             (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))   X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__lower  E Γ2  Γ3 LB UB ) ->
            a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_arrow A1 A2) (typ_var_f X)))
                        (aworklist_conswork  (  (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )   )  (work_sub (typ_arrow A1 A2) (typ_arrow (typ_var_f X1) (typ_var_f X2)))) )
 | a_wl_red_ss__sub_etvar1 : forall (L:vars) (E:aenv) (Γ Γ2 Γ3:aworklist) (Y X:typvar) (B1 B2 B3 B4 LB UB:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  Γ  )  )  ->     a_evs_in_wl Γ X Y ->
      a_evs_in_wl Γ X Y ->
      (a_update_bound  Γ  X   (typ_var_f Y)  a_mode_ub__lower  E Γ2   Γ3 LB UB)  ->
       a_wl_red_ss  (aworklist_conswork Γ (work_sub (typ_var_f Y) (typ_var_f X)))
                    (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )
 | a_wl_red_ss__sub_etvar2 : forall (L:vars) (E:aenv) (Γ Γ2 Γ3:aworklist) (X Y:typvar) (B1 B2 B3 B4 LB UB:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
      binds ( Y )  ( (abind_bound B3 B4) ) (  ( awl_to_aenv  Γ  )  )  ->
      a_evs_in_wl Γ X Y ->
      (a_update_bound  Γ  X   (typ_var_f Y)  a_mode_ub__upper E Γ2   Γ3 LB UB)  ->
      a_wl_red_ss  (aworklist_conswork Γ (work_sub (typ_var_f X) (typ_var_f Y)))
                   (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )
 | a_wl_red_ss__sub_etvarmono1 : forall (L:vars)  (E:aenv) (Γ Γ2 Γ3:aworklist) (A1:typ) (X:typvar) (B1 B2 LB UB:typ),
      binds ( X )  ( (abind_bound B1 B2) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_mono_typ  ( awl_to_aenv  Γ  )  A1 ->
     (a_update_bound  Γ  X   A1  a_mode_ub__lower E Γ2 Γ3 LB UB )  ->
      a_wl_red_ss  (aworklist_conswork Γ (work_sub A1 (typ_var_f X)))
                   (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) ) )
 | a_wl_red_ss__sub_etvarmono2 : forall (L:vars) (E:aenv) (Γ Γ2 Γ3:aworklist) (X:typvar) (B1 A1 A2 LB UB:typ),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_mono_typ  ( awl_to_aenv  Γ  )  B1 ->
     a_update_bound  Γ  X   B1  a_mode_ub__upper E  Γ2   Γ3 LB UB->
      a_wl_red_ss  (aworklist_conswork Γ (work_sub (typ_var_f X) B1))
                   (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )
 | a_wl_red_ss__sub_intersection1 : forall (Γ:aworklist) (A1 B1 B2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub A1 (typ_intersection B1 B2)))
                 (aworklist_conswork (aworklist_conswork Γ (work_sub A1 B1)) (work_sub A1 B2))
 | a_wl_red_ss__sub_intersection2 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_intersection B1 B2) A1))
                 (aworklist_conswork Γ (work_sub B1 A1))
 | a_wl_red_ss__sub_intersection3 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_intersection B1 B2) A1))
                 (aworklist_conswork Γ (work_sub B2 A1))
 | a_wl_red_ss__sub_union1 : forall (Γ:aworklist) (B1 A1 A2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub B1 (typ_union A1 A2))) (aworklist_conswork Γ (work_sub B1 A1)) 
 | a_wl_red_ss__sub_union2 : forall (Γ:aworklist) (B1 A1 A2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub B1 (typ_union A1 A2))) (aworklist_conswork Γ (work_sub B1 A2)) 
 | a_wl_red_ss__sub_union3 : forall (Γ:aworklist) (B1 B2 A1:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_sub (typ_union B1 B2) A1)) (aworklist_conswork (aworklist_conswork Γ (work_sub B1 A1)) (work_sub B2 A1))
 | a_wl_red_ss__chk_sub : forall (Γ:aworklist) (e:exp) (A1:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_check e A1)) (aworklist_conswork Γ (work_infer e (cont_sub A1))) 
 | a_wl_red_ss__chk_absarrow : forall (L:vars) (Γ:aworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> a_wl_red_ss (aworklist_conswork Γ (work_check (exp_abs e) (typ_arrow A1 A2))) (aworklist_conswork (aworklist_consvar Γ x (abind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )
 | a_wl_red_ss__chk_absevar : forall (L:vars) (Γ:aworklist) (e:exp) (X:typvar) (A1 A2:typ) (X1 X2:typvar),
      binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
      (  forall x, x `notin` L -> forall X1, X1 `notin` (L `union` (singleton x)) -> forall X2, X2 `notin` (L `union` singleton x `union` singleton X1) -> forall Γ2 Γ3 E LB UB,
            (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))  X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both E  Γ2   Γ3 LB UB)  ->
            a_wl_red_ss (aworklist_conswork Γ (work_check (exp_abs e) (typ_var_f X))) (aworklist_conswork (aworklist_consvar  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )  )  x (abind_typ (typ_var_f X1))) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  (typ_var_f X2))) )
 | a_wl_red_ss__chk_abstop : forall (L:vars) (Γ:aworklist) (e:exp),
      ( forall x , x \notin  L  -> a_wl_red_ss (aworklist_conswork Γ (work_check (exp_abs e) typ_top)) (aworklist_conswork (aworklist_consvar Γ x (abind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )
 | a_wl_red_ss__chk_inter : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_check e (typ_intersection A1 A2))) (aworklist_conswork (aworklist_conswork Γ (work_check e A1)) (work_check e A2)) 
 | a_wl_red_ss__chk_union1 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_check e (typ_union A1 A2))) (aworklist_conswork Γ (work_check e A1)) 
 | a_wl_red_ss__chk_union2 : forall (Γ:aworklist) (e:exp) (A1 A2:typ),
     a_wl_red_ss (aworklist_conswork Γ (work_check e (typ_union A1 A2))) (aworklist_conswork Γ (work_check e A2)) 
 | a_wl_red_ss__inf_var : forall (Γ:aworklist) (x:expvar) (c:cont) (A:typ),
      binds ( x )  ( (abind_typ A) ) (  ( awl_to_aenv  Γ  )  )  ->
     a_wl_red_ss (aworklist_conswork Γ (work_infer (exp_var_f x) c)) (aworklist_conswork Γ (work_apply c A))
 | a_wl_red_ss__inf_anno : forall (Γ:aworklist) (e:exp) (A:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infer  ( (exp_anno e A) )  c)) (aworklist_conswork (aworklist_conswork Γ (work_apply c A)) (work_check e A))
 | a_wl_red_ss__inf_tabs : forall (L:vars) (Γ:aworklist) (e:exp) (A:typ) (c:cont) (Γ2:aworklist),
      ( forall X , X \notin  L  -> a_wl_red_ss (aworklist_conswork Γ (work_infer (exp_tabs (body_anno e A)) c)) (aworklist_conswork (aworklist_constvar (aworklist_conswork Γ2 (work_apply c  ( (typ_all A) ) )) X abind_tvar_empty) (work_check  ( open_exp_wrt_typ e (typ_var_f X) )   ( open_typ_wrt_typ A (typ_var_f X) ) )) )
 | a_wl_red_ss__inf_unit : forall (Γ:aworklist) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infer exp_unit c)) (aworklist_conswork Γ (work_apply c typ_unit))
 | a_wl_red_ss__inf_app : forall (Γ:aworklist) (e1 e2:exp) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infer  ( (exp_app e1 e2) )  c)) (aworklist_conswork Γ (work_infer e1  (  (cont_infabs  (  (cont_infapp e2 c)  ) )  ) ))
 | a_wl_red_ss__infapp : forall (Γ:aworklist) (A1 A2:typ) (e:exp) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infapp (typ_arrow A1 A2) e c)) (aworklist_conswork (aworklist_conswork Γ (work_check e A1)) (work_apply c A2))
 | a_wl_red_ss__infabs_arr : forall (Γ:aworklist) (A1 B1:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infabs (typ_arrow A1 B1) c)) (aworklist_conswork Γ (work_apply c (typ_arrow A1 B1)))
 | a_wl_red_ss__infabs_bot : forall (Γ:aworklist) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infabs typ_bot c)) (aworklist_conswork Γ (work_infabs (typ_arrow typ_top typ_bot) c))
 | a_wl_red_ss__infabs_all : forall (L:vars) (Γ:aworklist) (A:typ) (c:cont),
     (forall X, X `notin` L -> a_wl_red_ss (aworklist_conswork Γ (work_infabs (typ_all A) c)) (aworklist_conswork  (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) c)) )
 | a_wl_red_ss__infabs_inter1 : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     lc_typ A2 ->
     a_wl_red_ss (aworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c)) (aworklist_conswork Γ (work_infabs A1 c))
 | a_wl_red_ss__infabs_inter2 : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     lc_typ A1 ->
     a_wl_red_ss (aworklist_conswork Γ (work_infabs (typ_intersection A1 A2) c)) (aworklist_conswork Γ (work_infabs A2 c))
 | a_wl_red_ss__infabs_union : forall (Γ:aworklist) (A1 A2:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infabs (typ_union A1 A2) c)) (aworklist_conswork Γ (work_infabs A1  (  (cont_infabsunion A2 c)  ) ))
 | a_wl_red_ss__infabsunion : forall (Γ:aworklist) (B1 C1 A2:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infabsunion (typ_arrow B1 C1) A2 c)) (aworklist_conswork Γ (work_infabs A2  (  (cont_unioninfabs (typ_arrow B1 C1) c)  ) ))
 | a_wl_red_ss__unioninfabs : forall (Γ:aworklist) (B2 C2 B1 C1:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_unioninfabs (typ_arrow B1 C1) (typ_arrow B2 C2) c)) (aworklist_conswork Γ (work_apply c (typ_arrow  ( (typ_intersection B1 B2) )   ( (typ_union C1 C2) ) )))
 | a_wl_red_ss__infabs_evar : forall (L:vars) (Γ:aworklist) (X:typvar) (c:cont) (A1 A2:typ) (X1 X2:typvar),
     binds ( X )  ( (abind_bound A1 A2) ) (  ( awl_to_aenv  Γ  )  )  ->
     (forall X1, X1 `notin` L -> forall X2, X2 `notin` (L `union` singleton X1) -> forall E Γ2 Γ3 LB UB,
         (a_update_bound  (aworklist_constvar (aworklist_constvar Γ X1 (abind_bound typ_bot typ_top)) X2 (abind_bound typ_bot typ_top))  X   (typ_arrow (typ_var_f X1) (typ_var_f X2))  a_mode_ub__both  E  Γ2   Γ3 LB UB)  ->
       a_wl_red_ss (aworklist_conswork Γ (work_infabs (typ_var_f X) c))
                   (aworklist_conswork  (   (awl_rev_app Γ3 (aworklist_constvar (awl_rev_app (aenv_to_awl E) Γ2) X (abind_bound LB UB)) )   )  (work_infabs (typ_arrow (typ_var_f X1) (typ_var_f X2)) c))
     )
 | a_wl_red_ss__inf_tapp : forall (Γ:aworklist) (e:exp) (B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_infer (exp_tapp e B) c))
                 (aworklist_conswork Γ (work_infer e (cont_inftapp B c)))
 | a_wl_red_ss__inftapp_all : forall (Γ:aworklist) (A B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_inftapp (typ_all A) B c))
                 (aworklist_conswork Γ (work_apply c  (open_typ_wrt_typ  A   B ) ))
 | a_wl_red_ss__inftapp_bot : forall (Γ:aworklist) (B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_inftapp typ_bot B c))
                 (aworklist_conswork Γ (work_apply c typ_bot))
 | a_wl_red_ss__inftapp_inter1 : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B c))
                 (aworklist_conswork Γ (work_inftapp A1 B c))
 | a_wl_red_ss__inftapp_inter2 : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_inftapp (typ_intersection A1 A2) B c))
                 (aworklist_conswork Γ (work_inftapp A2 B c))
 | a_wl_red_ss__inftapp_union : forall (Γ:aworklist) (A1 A2 B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_inftapp (typ_union A1 A2) B c))
                 (aworklist_conswork Γ (work_inftapp A1 B  (  (cont_inftappunion A2 B c)  ) ))
 | a_wl_red_ss__inftappunion : forall (Γ:aworklist) (C1 A2 B:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_inftappunion C1 A2 B c))
                 (aworklist_conswork Γ (work_inftapp A2 B  (  (cont_unioninftapp C1 c)  ) ))
 | a_wl_red_ss__unioninftapp : forall (Γ:aworklist) (C2 C1:typ) (c:cont),
     a_wl_red_ss (aworklist_conswork Γ (work_unioninftapp C1 C2 c))
                 (aworklist_conswork Γ (work_apply c (typ_union C1 C2)))
 | a_wl_red_ss__applycont : forall (Γ:aworklist) (w:work) (T1:typ) (c:cont),
     apply_cont c T1 w ->
     a_wl_red_ss (aworklist_conswork Γ (work_apply c T1))
                 (aworklist_conswork Γ w)
. *)

(* Inductive a_wl_mul_red : aworklist -> aworklist -> Prop :=
  | a_wl_mul_red__refl : forall (Γ:aworklist), a_wl_mul_red Γ Γ
  | a_wl_mul_red__step : forall (Γ1 Γ2 Γ3:aworklist),
      a_wl_red_ss Γ1 Γ2 ->
      a_wl_mul_red Γ2 Γ3 ->
      a_wl_mul_red Γ1 Γ3
. *)

Declare Scope aworklist_scope.
Delimit Scope aworklist_scope with aworklist.
Bind Scope aworklist_scope with aworklist.



Notation " x ~ᵃ A ;ᵃ Γ " :=
  (aworklist_consvar Γ x (abind_var_typ A))
      (at level 58, A at next level, right associativity) : aworklist_scope.
    
Notation " X ~ᵃ □ ;ᵃ Γ " :=
  (aworklist_constvar Γ X abind_tvar_empty)
      (at level 58, right associativity) : aworklist_scope.

Notation " X ~ᵃ ■ ;ᵃ Γ " :=
  (aworklist_constvar Γ X abind_stvar_empty)
      (at level 58, right associativity) : aworklist_scope.

Notation " X ~ᵃ ⬒ ;ᵃ Γ " :=
  (aworklist_constvar Γ X abind_etvar_empty)
      (at level 58, right associativity) : aworklist_scope.

Notation " W ⫤ Γ " :=
  (aworklist_conswork Γ W)
      (at level 58, right associativity) : aworklist_scope.

Notation " Γ ⟶ᵃʷ⁎⋅ " :=
  (a_wl_red Γ)
      (at level 58, no associativity) : type_scope.

(* Notation " Γ1 ⟶ᵃʷ Γ2 " :=
  (a_wl_red_ss Γ1 Γ2)
      (at level 58, no associativity) : type_scope.

Notation " Γ1 ⟶ᵃʷ⁎ Γ2 " :=
  (a_wl_mul_red Γ1 Γ2)
      (at level 58, no associativity) : type_scope. *)

Notation " ⊢ᵃʷ Γ " :=
  (a_wf_wl Γ)
      (at level 58, no associativity) : type_scope.
