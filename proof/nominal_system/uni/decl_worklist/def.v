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
  | applycont__infabs: forall A c,
      apply_cont (cont_infabs c) 
                   A
                   (work_infabs A c)
  | d_applycont_infapp : forall A e c,
      apply_cont (cont_infapp e c) 
                   A
                  (work_infapp A e c)
  | applycont__tapp : forall A B c,
      apply_cont (cont_inftapp B c) 
                   A
                   (work_inftapp A B c)
  | applycont__sub : forall A B,
      apply_cont (cont_sub B) 
                   A
                   (work_sub A B)
.

(* decl worklist delegated reduction, corresponds to Jimmy's dc *)
Inductive d_wl_del_red : dworklist -> Prop :=
  | d_wl_del_red__empty : d_wl_del_red dworklist_empty
  | d_wl_del_red__var : forall Ω x A,
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_consvar Ω x (dbind_typ A))
  | d_wl_del_red__tvar : forall Ω X,
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_constvar Ω X dbind_tvar_empty)
  | d_wl_del_red__stvar : forall Ω X,
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_constvar Ω X dbind_stvar_empty)
  | d_wl_del_red__chk : forall Ω e T1,
      d_typing (dwl_to_denv Ω) e typingmode__chk T1 ->
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_conswork Ω (work_check e T1))
  | d_wl_del_red__inf : forall Ω e T1 c,
      d_typing (dwl_to_denv Ω) e typingmode__inf T1 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c T1)) ->
      d_wl_del_red (dworklist_conswork Ω (work_infer e c))
  | d_wl_del_red__infabs : forall Ω T1 T2 T3 c,
      d_infabs (dwl_to_denv Ω) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c (typ_arrow T2 T3))) ->
      d_wl_del_red (dworklist_conswork Ω (work_infabs T1 c))
  | d_wl_del_red__inftapp : forall Ω T1 T2 T3 c,
      d_inftapp (dwl_to_denv Ω) T1 T2 T3 ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c T3)) -> 
      d_wl_del_red (dworklist_conswork Ω (work_inftapp T1 T2 c))
  | d_wl_del_red__sub : forall Ω S1 T1,
      d_sub (dwl_to_denv Ω) S1 T1 ->
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_conswork Ω (work_sub S1 T1))
  | d_wl_del_red__applycont : forall Ω c T1 w,
      apply_cont c T1 w ->
      d_wl_del_red (dworklist_conswork Ω w) ->
      d_wl_del_red (dworklist_conswork Ω (work_apply c T1))
  .

(* defns Jdworklist_reduction *)
Inductive d_wl_red : dworklist -> Prop :=    (* defn d_wl_red *)
 | d_wl_red__empty : d_wl_red dworklist_empty
 | d_wl_red__gc_var : forall (Ω:dworklist) (x:atom) (A:typ),
    d_wl_red Ω ->
    d_wl_red (dworklist_consvar Ω x (dbind_typ A))
 | d_wl_red__gc_tvar : forall (Ω:dworklist) (X:atom),
    d_wl_red Ω ->
    d_wl_red (dworklist_constvar Ω X dbind_tvar_empty)
 | d_wl_red__gc_stvar : forall (Ω:dworklist) (X:atom),
    d_wl_red Ω ->
    d_wl_red (dworklist_constvar Ω X dbind_stvar_empty)
 | d_wl_red__sub_top : forall (Ω:dworklist) (A:typ),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub A typ_top))
 | d_wl_red__sub_bot : forall (Ω:dworklist) (B:typ),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub typ_bot B))
 | d_wl_red__sub_unit : forall (Ω:dworklist),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub typ_unit typ_unit))
 | d_wl_red__sub_tvar : forall (Ω:dworklist) (X:typvar),
     d_wl_red Ω ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_var_f X) (typ_var_f X)))
 | d_wl_red__sub_arrow : forall (Ω:dworklist) (A1 A2 B1 B2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_sub B1 A1)) (work_sub A2 B2)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_arrow A1 A2) (typ_arrow B1 B2)))
 | d_wl_red__sub_all : forall (L:vars) (Ω:dworklist) (A B:typ),
     ( forall X , X `notin` L -> d_wl_red (dworklist_conswork (dworklist_constvar Ω X dbind_stvar_empty) (work_sub  (open_typ_wrt_typ  A   (typ_var_f X) )   (open_typ_wrt_typ  B   (typ_var_f X) ) ))) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_all A) (typ_all B)))    
 | d_wl_red__sub_alll : forall (Ω:dworklist) (A B T:typ),
     neq_all B ->
     d_mono_typ ( dwl_to_denv  Ω  )  T ->
     d_wl_red (dworklist_conswork Ω (work_sub  (open_typ_wrt_typ  A   T )  B)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_all A) B))
 | d_wl_red__chk_sub : forall (Ω:dworklist) (e:exp) (A:typ),
     d_wl_red (dworklist_conswork Ω (work_infer e (cont_sub A))) ->
     d_wl_red (dworklist_conswork Ω (work_check e A))
 (* | d_wl_red__chkall : forall (L:vars) (Ω:dworklist) (e:exp) (T1:typ),
      ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar Ω X dbind_tvar_empty) (work_check e  ( open_typ_wrt_typ T1 (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_all T1))) *)
 | d_wl_red__chk_absarrow : forall (L:vars) (Ω:dworklist) (e:exp) (A1 A2:typ),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Ω x (dbind_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  A2)) )  ->
     d_wl_red (dworklist_conswork Ω (work_check (exp_abs e) (typ_arrow A1 A2)))
 | d_wl_red__chk_abstop : forall (L:vars) (Ω:dworklist) (e:exp),
      ( forall x , x \notin  L  -> d_wl_red (dworklist_conswork (dworklist_consvar Ω x (dbind_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) )  ->
     d_wl_red (dworklist_conswork Ω (work_check (exp_abs e) typ_top))
 | d_wl_red__inf_var : forall (Ω:dworklist) (x:expvar) (c:cont) (A:typ),
      binds ( x )  ( (dbind_typ A) ) (  ( dwl_to_denv  Ω  )  )  ->
     d_wl_red (dworklist_conswork Ω (work_apply c A)) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_var_f x) c))
 | d_wl_red__inf_anno : forall (Ω:dworklist) (e:exp) (A:typ) (c:cont),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_apply c  A)) (work_check e A)) ->
     d_wl_red (dworklist_conswork Ω (work_infer  ( (exp_anno e A) )  c))
 | d_wl_red__inf_tabs : forall (L:vars) (Ω:dworklist) (e:exp) (A:typ) (c:cont),
      (* ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  -> *)
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork Ω (work_apply c  (typ_all A) )) X dbind_tvar_empty) (work_check (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) ) ( open_typ_wrt_typ A (typ_var_f X) ) )  ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_tabs (body_anno e A)) c))
 | d_wl_red__inf_unit : forall (Ω:dworklist) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c typ_unit)) ->
     d_wl_red (dworklist_conswork Ω (work_infer exp_unit c))
 | d_wl_red__inf_app : forall (Ω:dworklist) (e1 e2:exp) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infer e1 (cont_infabs (cont_infapp e2 c)))) ->
     d_wl_red (dworklist_conswork Ω (work_infer  ( (exp_app e1 e2) )  c))
 | d_wl_red__inf_tapp : forall (Ω:dworklist) (e:exp) (B:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_infer e (cont_inftapp B c))) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_tapp e B) c))
 | d_wl_red__inftapp_all : forall (Ω:dworklist) (A B:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (open_typ_wrt_typ  A   B ) )) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_all A) B c))
 | d_wl_red__inftapp_bot : forall (Ω:dworklist) (B:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c typ_bot)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp typ_bot B c))
 | d_wl_red__infabs_arrow : forall (Ω:dworklist) (A B:typ) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (typ_arrow A B))) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_arrow A B) c))
 | d_wl_red__infabs_bot : forall (Ω:dworklist) (c:cont),
     d_wl_red (dworklist_conswork Ω (work_apply c (typ_arrow typ_top typ_bot))) ->
     d_wl_red (dworklist_conswork Ω (work_infabs typ_bot c))
 | d_wl_red__infabs_all : forall (Ω:dworklist) (A T:typ) (c:cont),
     d_mono_typ (dwl_to_denv Ω) T ->
     d_wl_red (dworklist_conswork Ω (work_infabs (open_typ_wrt_typ A T) c)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_all A) c))
 | d_wl_red__infapp: forall (Ω:dworklist) (e:exp) (A B:typ) (c:cont),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_check e A)) (work_apply c B)) ->
     d_wl_red (dworklist_conswork Ω (work_infapp (typ_arrow A B) e c))
 | d_wl_red__applycont : forall (Ω:dworklist) (w:work) (A:typ) (c:cont),
     apply_cont c A w ->
     d_wl_red (dworklist_conswork Ω w) ->
     d_wl_red (dworklist_conswork Ω (work_apply c A))   
.


Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dworklist.
Bind Scope dworklist_scope with dworklist.
    
Notation " x ~ T ; Ω " :=
    (dworklist_consvar Ω x (dbind_typ T))
        (at level 58, T at next level, right associativity) : dworklist_scope.
      
  Notation " X ~ ▫ ; Ω " :=
    (dworklist_constvar Ω X dbind_tvar_empty)
        (at level 58, right associativity) : dworklist_scope.
  
  Notation " X ~ ▪ ; Ω " :=
    (dworklist_constvar Ω X dbind_stvar_empty)
        (at level 58, right associativity) : dworklist_scope.
  
  Notation " W ⫤ Ω " :=
    (dworklist_conswork Ω W)
        (at level 58, right associativity) : dworklist_scope.
  
  Notation " Ω ⟶ᵈʷ⁎⋅ " :=
    (d_wl_red Ω)
        (at level 58, no associativity) : type_scope.
  
  Notation " Ω ⟶ᵈ⁎⋅ " :=
    (d_wl_del_red Ω)
        (at level 58, no associativity) : type_scope.
  
  Notation " ⊢ᵈʷ Ω " :=
    (d_wf_wl Ω)
        (at level 58, no associativity) : type_scope.
      
  