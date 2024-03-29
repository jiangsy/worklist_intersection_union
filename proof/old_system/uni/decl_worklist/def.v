Require Import Program.Equality.

Require Export uni.def_ott.
Require Export uni.def_extra.
Require Export uni.decl.def_extra.


Fixpoint dwl_app (Ω1 Ω2 : dworklist) :=
  match Ω1 with 
  | dworklist_empty => Ω2 
  | dworklist_constvar Ω1' X b => dworklist_constvar (dwl_app Ω1' Ω2) X b
  | dworklist_consvar Ω1' x b => dworklist_consvar (dwl_app Ω1' Ω2) x b
  | dworklist_conswork Ω1' w => dworklist_conswork (dwl_app Ω1' Ω2) w
  end.


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
  | d_wl_del_red__inf : forall Ω e T1 cs,
      d_typing (dwl_to_denv Ω) e typingmode__inf T1 ->
      d_wl_del_red (dworklist_conswork Ω (work_applys cs T1)) ->
      d_wl_del_red (dworklist_conswork Ω (work_infer e cs))
  | d_wl_del_red__infabs : forall Ω A B C cd,
      d_infabs (dwl_to_denv Ω) A B C ->
      d_wl_del_red (dworklist_conswork Ω (work_applyd cd B C)) ->
      d_wl_del_red (dworklist_conswork Ω (work_infabs A cd))
  | d_wl_del_red__infabsunion : forall Ω A2 B1 B2 C1 C2 cd,
      d_infabs (dwl_to_denv Ω) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Ω (work_applyd cd (typ_intersection B1 B2) (typ_union C1 C2))) ->
      d_wl_del_red (dworklist_conswork Ω (work_infabsunion B1 C1 A2 cd))
  | d_wl_del_red__unioninfabs : forall Ω B1 B2 C1 C2 cd,
      d_wl_del_red (dworklist_conswork Ω (work_applyd cd (typ_intersection B1 B2) (typ_union C1 C2))) -> 
      d_wl_del_red (dworklist_conswork Ω (work_unioninfabs B1 C1 B2 C2 cd))
  | d_wl_del_red__infapp : forall Ω e A B cs,
      d_wl_del_red (dworklist_conswork (dworklist_conswork Ω (work_check e A)) (work_applys cs B)) ->
      d_wl_del_red (dworklist_conswork Ω (work_infapp A B e cs))
  | d_wl_del_red__inftapp : forall Ω A B C cs,
      d_inftapp (dwl_to_denv Ω) A B C ->
      d_wl_del_red (dworklist_conswork Ω (work_applys cs C)) -> 
      d_wl_del_red (dworklist_conswork Ω (work_inftapp A B cs))
  | d_wl_del_red__inftappunion : forall Ω A2 B2 C1 C2 cs,
      d_inftapp (dwl_to_denv Ω) A2 B2 C2 ->
      d_wl_del_red (dworklist_conswork Ω (work_applys cs (typ_union C1 C2))) -> 
      d_wl_del_red (dworklist_conswork Ω (work_inftappunion C1 A2 B2 cs))
  | d_wl_del_red__unioninftapp : forall Ω A1 A2 cs,
      d_wl_del_red (dworklist_conswork Ω (work_applys cs (typ_union A1 A2))) -> 
      d_wl_del_red (dworklist_conswork Ω (work_unioninftapp A1 A2 cs))
  | d_wl_del_red__sub : forall Ω A B,
      d_sub (dwl_to_denv Ω) A B ->
      d_wl_del_red Ω ->
      d_wl_del_red (dworklist_conswork Ω (work_sub A B))
  | d_wl_del_red__applys : forall Ω cs A w,
      apply_conts cs A w ->
      d_wl_del_red (dworklist_conswork Ω w) ->
      d_wl_del_red (dworklist_conswork Ω (work_applys cs A))
  | d_wl_del_red__applyd : forall Ω cd A B w,
      apply_contd cd A B w ->
      d_wl_del_red (dworklist_conswork Ω w) ->
      d_wl_del_red (dworklist_conswork Ω (work_applyd cd A B))
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
     ( forall X , X `notin` L -> 
        d_wl_red (dworklist_conswork (dworklist_constvar Ω X dbind_stvar_empty) 
        (work_sub  (open_typ_wrt_typ  A   (typ_var_f X) )   (open_typ_wrt_typ  B   (typ_var_f X) ) ))) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_all A) (typ_all B)))    
 | d_wl_red__sub_alll : forall (Ω:dworklist) (A B T:typ),
     neq_all B ->
     neq_intersection B ->
     neq_union B -> 
     d_mono_typ ( dwl_to_denv  Ω  )  T ->
     d_wl_red (dworklist_conswork Ω (work_sub  (open_typ_wrt_typ  A   T )  B)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_all A) B))
 | d_wl_red__sub_intersection1 : forall (Ω:dworklist) (A B1 B2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_sub A B1)) (work_sub A B2)) ->
     d_wl_red (dworklist_conswork Ω (work_sub A (typ_intersection B1 B2)))
 | d_wl_red__sub_intersection2 : forall (Ω:dworklist) (A1 A2 B:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A1 B)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_intersection A1 A2) B))
 | d_wl_red__sub_intersection3 : forall (Ω:dworklist) (A1 A2 B:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A2 B)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_intersection A1 A2) B))
 | d_wl_red__sub_union1 : forall (Ω:dworklist) (A B1 B2:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub A (typ_union B1 B2)))
 | d_wl_red__sub_union2 : forall (Ω:dworklist) (A B1 B2:typ),
     d_wl_red (dworklist_conswork Ω (work_sub A B2)) ->
     d_wl_red (dworklist_conswork Ω (work_sub A (typ_union B1 B2)))
 | d_wl_red__sub_union3 : forall (Ω:dworklist) (A1 A2 B1:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_sub A1 B1)) (work_sub A2 B1)) ->
     d_wl_red (dworklist_conswork Ω (work_sub (typ_union A1 A2) B1))
 | d_wl_red__chk_sub : forall (Ω:dworklist) (e:exp) (A:typ),
     d_wl_red (dworklist_conswork Ω (work_infer e (conts_sub A))) ->
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
 | d_wl_red__chk_inter : forall (Ω:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_check e A1)) (work_check e A2)) ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_intersection A1 A2)))
 | d_wl_red__chk_union1 : forall (Ω:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork Ω (work_check e A1)) ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_union A1 A2)))
 | d_wl_red__chk_union2 : forall (Ω:dworklist) (e:exp) (A1 A2:typ),
     d_wl_red (dworklist_conswork Ω (work_check e A2)) ->
     d_wl_red (dworklist_conswork Ω (work_check e (typ_union A1 A2)))
 | d_wl_red__inf_var : forall (Ω:dworklist) (x:expvar) (cs:conts) (A:typ),
      binds ( x )  ( (dbind_typ A) ) (  ( dwl_to_denv  Ω  )  )  ->
     d_wl_red (dworklist_conswork Ω (work_applys cs A)) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_var_f x) cs))
 | d_wl_red__inf_anno : forall (Ω:dworklist) (e:exp) (A:typ) (cs:conts),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_applys cs  A)) (work_check e A)) ->
     d_wl_red (dworklist_conswork Ω (work_infer  ( (exp_anno e A) )  cs))
 | d_wl_red__inf_tabs : forall (L:vars) (Ω:dworklist) (e:exp) (A:typ) (cs:conts),
      (* ( forall X , X \notin  L  -> ds_in X  ( open_typ_wrt_typ A1 (typ_var_f X) )  )  -> *)
      ( forall X , X \notin  L  -> d_wl_red (dworklist_conswork (dworklist_constvar (dworklist_conswork Ω (work_applys cs  (typ_all A) )) X dbind_tvar_empty) (work_check (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) ) ( open_typ_wrt_typ A (typ_var_f X) ) )  ( open_typ_wrt_typ A (typ_var_f X) ) )) )  ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_tabs (body_anno e A)) cs))
 | d_wl_red__inf_unit : forall (Ω:dworklist) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_applys cs typ_unit)) ->
     d_wl_red (dworklist_conswork Ω (work_infer exp_unit cs))
 | d_wl_red__inf_abs_mono : forall (Ω:dworklist) (e:exp) (T1 T2:typ) (cs:conts),
     d_mono_typ ( dwl_to_denv  Ω  )  (typ_arrow T1 T2) ->
     d_wl_red (dworklist_conswork Ω (work_applys cs (typ_arrow T1 T2))) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_abs e) cs))
 | d_wl_red__inf_app : forall (Ω:dworklist) (e1 e2:exp) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_infer e1 (conts_infabs (contd_infapp e2 cs)))) ->
     d_wl_red (dworklist_conswork Ω (work_infer  ( (exp_app e1 e2) )  cs))
 | d_wl_red__inf_tapp : forall (Ω:dworklist) (e:exp) (B:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_infer e (conts_inftapp B cs))) ->
     d_wl_red (dworklist_conswork Ω (work_infer (exp_tapp e B) cs))
 | d_wl_red__inftapp_all : forall (Ω:dworklist) (A B:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_applys cs (open_typ_wrt_typ  A   B ) )) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_all A) B cs))
 | d_wl_red__inftapp_bot : forall (Ω:dworklist) (B:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_applys cs typ_bot)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp typ_bot B cs))
 | d_wl_red__inftapp_inter1 : forall (Ω:dworklist) (A1 A2 B:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_inftapp A1 B cs)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_intersection A1 A2) B cs))
 | d_wl_red__inftapp_inter2: forall (Ω:dworklist) (A1 A2 B:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_inftapp A2 B cs)) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_intersection A1 A2) B cs))
 | d_wl_red__inftapp_union : forall (Ω:dworklist) (A1 A2 B:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_inftapp A1 B (conts_inftappunion A2 B cs))) ->
     d_wl_red (dworklist_conswork Ω (work_inftapp (typ_union A1 A2) B cs))
 | d_wl_red__inftappunion : forall (Ω:dworklist) (A B C:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_inftapp A B (conts_unioninftapp C cs) ))->
     d_wl_red (dworklist_conswork Ω (work_inftappunion C A B cs))
 | d_wl_red__unioninftapp : forall (Ω:dworklist) (A1 A2:typ) (cs:conts),
     d_wl_red (dworklist_conswork Ω (work_applys cs (typ_union A1 A2)))->
     d_wl_red (dworklist_conswork Ω (work_unioninftapp A1 A2 cs))
 | d_wl_red__infabs_arrow : forall (Ω:dworklist) (A B:typ) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_applyd cd A B)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_arrow A B) cd))
 | d_wl_red__infabs_bot : forall (Ω:dworklist) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_applyd cd typ_top typ_bot)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs typ_bot cd))
 | d_wl_red__infabs_all : forall (Ω:dworklist) (A T:typ) (cd:contd),
     d_mono_typ (dwl_to_denv Ω) T ->
     d_wl_red (dworklist_conswork Ω (work_infabs (open_typ_wrt_typ A T) cd)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_all A) cd))
 | d_wl_red__infabs_inter1 : forall (Ω:dworklist) (A1 A2:typ) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_infabs A1 cd)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_intersection A1 A2) cd))
 | d_wl_red__infabs_inter2: forall (Ω:dworklist) (A1 A2:typ) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_infabs A2 cd)) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_intersection A1 A2) cd))
 | d_wl_red__infabs_union : forall (Ω:dworklist) (A1 A2:typ) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_infabs A1 (contd_infabsunion A2 cd))) ->
     d_wl_red (dworklist_conswork Ω (work_infabs (typ_union A1 A2) cd))
 | d_wl_red__unioninfabs: forall (Ω:dworklist) (A1 A2 B1 B2:typ) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_applyd cd (typ_intersection A1 A2) (typ_union B1 B2))) ->
     d_wl_red (dworklist_conswork Ω (work_unioninfabs A1 B1 A2 B2 cd))
 | d_wl_red__infabsunion: forall (Ω:dworklist) (A B C:typ) (cd:contd),
     d_wl_red (dworklist_conswork Ω (work_infabs A (contd_unioninfabs B C cd))) ->
     d_wl_red (dworklist_conswork Ω (work_infabsunion B C A cd))
 | d_wl_red__infapp: forall (Ω:dworklist) (e:exp) (A B:typ) (cs:conts),
     d_wl_red (dworklist_conswork (dworklist_conswork Ω (work_check e A)) (work_applys cs B)) ->
     d_wl_red (dworklist_conswork Ω (work_infapp A B e cs))
 | d_wl_red__applys : forall (Ω:dworklist) (w:work) (A:typ) (cs:conts),
     apply_conts cs A w ->
     d_wl_red (dworklist_conswork Ω w) ->
     d_wl_red (dworklist_conswork Ω (work_applys cs A))   
 | d_wl_red__applyd : forall (Ω:dworklist) (w:work) (A B:typ) (cd:contd),
     apply_contd cd A B w ->
     d_wl_red (dworklist_conswork Ω w) ->
     d_wl_red (dworklist_conswork Ω (work_applyd cd A B))   
    .


Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dworklist.
Bind Scope dworklist_scope with dworklist.
    
Notation " x ~ᵈ T ;ᵈ Ω " :=
    (dworklist_consvar Ω x (dbind_typ T))
        (at level 58, T at next level, right associativity) : dworklist_scope.
      
Notation " X ~ᵈ □ ;ᵈ Ω " :=
(dworklist_constvar Ω X dbind_tvar_empty)
    (at level 58, right associativity) : dworklist_scope.

Notation " X ~ᵈ ■ ;ᵈ Ω " :=
(dworklist_constvar Ω X dbind_stvar_empty)
    (at level 58, right associativity) : dworklist_scope.

Notation " W ⫤ Ω " :=
(dworklist_conswork Ω W)
    (at level 58, right associativity) : dworklist_scope.

Notation " Ω2 ⧺ Ω1 " :=
    (dwl_app Ω2 Ω1)
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
    
