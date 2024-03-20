Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.def_ott.


Fixpoint ftvar_in_aworklist' (aW_5:aworklist) : vars :=
  match aW_5 with
  | aworklist_empty => empty
  | (aworklist_consvar aW x ab) => (ftvar_in_aworklist' aW) \u (ftvar_in_abind ab)
  | (aworklist_constvar aW X ab) => (ftvar_in_aworklist' aW) \u (ftvar_in_abind ab) \u (singleton X)
  | (aworklist_conswork aW w) => (ftvar_in_aworklist' aW) \u (ftvar_in_work w)
end.


Fixpoint fvar_in_aworklist' (aW_5:aworklist) : vars :=
  match aW_5 with
  | aworklist_empty => {}
  | (aworklist_consvar aW x ab) => (fvar_in_aworklist' aW) \u (singleton x) (* no var in abind *)
  | (aworklist_constvar aW X ab) => (fvar_in_aworklist' aW) (* no var in abind *)
  | (aworklist_conswork aW w) => (fvar_in_aworklist' aW) \u (fvar_in_work w)
end.
  

(* Inductive work : Set := 
 | work_infer (e:exp) (c:typ -> work)
 | work_check (e:exp) (A:typ)
 | work_infabs (A:typ) (c:typ -> work)
 | work_infapp (A:typ) (e:exp) (c:typ -> work)
 | work_inftapp (A1:typ) (A2:typ) (c:typ -> work)
 | work_sub (A1:typ) (A2:typ)
 | work_apply (c:typ -> work) (A:typ). *)
