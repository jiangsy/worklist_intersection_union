Require Export Metalib.Metatheory.
Require Import List.

Require Import uni.def_ott.


Fixpoint favar_in_aworklist (Γ_5:aworklist) : vars :=
  match Γ_5 with
  | aworklist_empty => empty
  | (aworklist_cons_var Γ x ab) => (favar_in_aworklist Γ) \u (ftvar_in_abind ab) \u (singleton x)
  | (aworklist_cons_work Γ w) => (favar_in_aworklist Γ) \u (ftvar_in_work w) \u (fvar_in_work w)
end.
  
Inductive apply_conts : conts -> typ -> work -> Prop :=
  | apply_conts__infabs: forall A cs,
      apply_conts (conts_infabs cs) 
                   A
                   (work_infabs A cs)
  | apply_conts__inftapp : forall A B cs,
      apply_conts (conts_inftapp B cs) 
                   A
                   (work_inftapp A B cs)
  | apply_conts__inftappunion : forall A2 B C1 cs,
      apply_conts (conts_inftappunion A2 B cs) 
                   C1
                   (work_inftappunion C1 A2 B cs)
  | apply_conts__unioninftapp : forall A1 A2 cs,
      apply_conts (conts_unioninftapp A1 cs) 
                   A2
                   (work_unioninftapp A1 A2 cs)
  | apply_conts__sub : forall A B,
      apply_conts (conts_sub B) 
                   A
                   (work_sub A B)
.

Inductive apply_contd : contd -> typ -> typ -> work -> Prop :=
  | apply_contd__infapp : forall A B e c,
      apply_contd (contd_infapp e c) 
                  A B
                  (work_infapp A B e c)
  | apply_contd__infabsunion : forall A2 B1 C1 c, 
      apply_contd (contd_infabsunion A2 c) 
                  B1 C1
                  (work_infabsunion B1 C1 A2 c)
  | apply_contd__unioninfabs : forall B1 B2 C1 C2 c,
      apply_contd (contd_unioninfabs B1 C1 c) 
                  B2 C2
                  (work_unioninfabs B1 C1 B2 C2 c)
.
