Require Import Program.Equality.

Require Import decl.notations.


Fixpoint dwl_app (Γ1 Γ2 : dworklist) :=
  match Γ1 with 
  | dworklist_empty => Γ2 
  | dworklist_constvar Γ1' X b => dworklist_constvar (dwl_app Γ1' Γ2) X b
  | dworklist_consstvar Γ1' SX b => dworklist_consstvar (dwl_app Γ1' Γ2) SX b
  | dworklist_consvar Γ1' x b => dworklist_consvar (dwl_app Γ1' Γ2) x b
  | dworklist_conswork Γ1' w => dworklist_conswork (dwl_app Γ1' Γ2) w
  end.

Fixpoint to_denv (Γ : dworklist) : denv :=
  match Γ with 
  | dworklist_empty => nil
  | dworklist_conswork Γ1' _ => to_denv Γ1'
  | dworklist_constvar Γ1' X b => X ~ b ++ to_denv Γ1'
  | dworklist_consstvar Γ1' SX b => SX ~ b ++ to_denv Γ1'
  | dworklist_consvar Γ1' x b => x ~ b ++ to_denv Γ1'
  end.

Inductive apply_dcont : dcont -> dtyp -> dworklist -> Prop :=
  | applydcont_done : forall T,  
      apply_dcont dcont_done T dworklist_empty
  | applydcont_app : forall T e c,
      apply_dcont (dcont_app e c) T (dworklist_conswork dworklist_empty (dwork_infapp T e c))
  | applydcont_tapp : forall T T1 c,
      apply_dcont (dcont_tapp T1 c) T (dworklist_conswork dworklist_empty (dwork_inftapp T T1 c))
  | applydcont_sub : forall T S,
      apply_dcont (dcont_sub S) T (dworklist_conswork dworklist_empty (dwork_sub T S))
.


Inductive dwl_red : dworklist -> Prop :=
  | dwlred_empty : dwl_red dworklist_empty
  | dwlred_inf : forall Γ e T c,
      dtyping (to_denv Γ) e dtypingmode_inf T ->
      dwl_red (dworklist_conswork Γ (dwork_apply c T)) ->
      dwl_red (dworklist_conswork Γ (dwork_infer e c))
  | dwlred_chk : forall Γ e T,
      dtyping (to_denv Γ) e dtypingmode_chk T ->
      dwl_red Γ ->
      dwl_red (dworklist_conswork Γ (dwork_check e T))
  | dwlred_infapp : forall Γ e T1 T2 c,
      dtyping (to_denv Γ) e (dtypingmode_infapp T1) T2 ->
      dwl_red (dworklist_conswork Γ (dwork_apply c T1)) ->
      dwl_red (dworklist_conswork Γ (dwork_infapp T2 e c))
  | dwlred_inftappall : forall Γ T T1 c,
    dwl_red (dworklist_conswork Γ (dwork_apply c (open_dtyp_wrt_dtyp T1 T))) -> 
    dwl_red (dworklist_conswork Γ (dwork_inftapp (dtyp_all T1) T c))
  | dwlred_inftappbot : forall Γ T c,
      dwl_red (dworklist_conswork Γ (dwork_apply c dtyp_bot)) -> 
      dwl_red (dworklist_conswork Γ (dwork_inftapp dtyp_bot T c))
  | dwlred_sub : forall Γ S T,
      dsub (to_denv Γ) S T ->
      dwl_red Γ ->
      dwl_red (dworklist_conswork Γ (dwork_sub S T))
  | dwlred_applycont : forall Γ c T Γ',
      apply_dcont c T Γ' ->
      dwl_red (dwl_app Γ' Γ) ->
      dwl_red (dworklist_conswork Γ (dwork_apply c T))
  .