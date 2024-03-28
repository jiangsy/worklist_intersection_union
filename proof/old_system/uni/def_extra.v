Require Export Metalib.Metatheory.
Require Import List.

Require Import uni.def_ott.


Fixpoint ftvar_in_aworklist' (Γ_5:aworklist) : vars :=
  match Γ_5 with
  | aworklist_empty => empty
  | (aworklist_consvar Γ x ab) => (ftvar_in_aworklist' Γ) \u (ftvar_in_abind ab)
  | (aworklist_constvar Γ X ab) => (ftvar_in_aworklist' Γ) \u (ftvar_in_abind ab) \u (singleton X)
  | (aworklist_conswork Γ w) => (ftvar_in_aworklist' Γ) \u (ftvar_in_work w)
end.


Fixpoint fvar_in_aworklist' (Γ_5:aworklist) : vars :=
  match Γ_5 with
  | aworklist_empty => {}
  | (aworklist_consvar Γ x ab) => (fvar_in_aworklist' Γ) \u (singleton x) (* no var in abind *)
  | (aworklist_constvar Γ X ab) => (fvar_in_aworklist' Γ) (* no var in abind *)
  | (aworklist_conswork Γ w) => (fvar_in_aworklist' Γ) \u (fvar_in_work w)
end.
  
Inductive apply_cont : cont -> typ -> work -> Prop :=
  | apply_cont__infabs: forall A c,
      apply_cont (cont_infabs c) 
                   A
                   (work_infabs A c)
  | apply_cont__tapp : forall A B c,
      apply_cont (cont_inftapp B c) 
                   A
                   (work_inftapp A B c)
  | apply_cont__tappunion : forall A2 B C1 c,
      apply_cont (cont_inftappunion A2 B c) 
                   C1
                   (work_inftappunion C1 A2 B c)
  | apply_cont__unioninftapp : forall A1 A2 c,
      apply_cont (cont_unioninftapp A1 c) 
                   A2
                   (work_unioninftapp A1 A2 c)
  | apply_cont__sub : forall A B,
      apply_cont (cont_sub B) 
                   A
                   (work_sub A B)
.

Inductive apply_cont2 : contd -> typ -> typ -> work -> Prop :=
  | apply_cont2__infapp : forall A B e c,
      apply_cont2 (contd_infapp e c) 
                  A B
                  (work_infapp A B e c)
  | apply_cont2__infabsunion : forall A2 B1 C1 c, 
      apply_cont2 (contd_infabsunion A2 c) 
                  B1 C1
                  (work_infabsunion B1 C1 A2 c)
  | apply_cont2__unioninfabs : forall B1 B2 C1 C2 c,
      apply_cont2 (contd_unioninfabs B1 C1 c) 
                  B2 C2
                  (work_unioninfabs B1 C1 B2 C2 c)
.