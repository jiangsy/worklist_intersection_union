Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import ln_utils.

Hint Constructors a_wl_red : core.
Hint Constructors a_wl_red_ss : core.
Hint Constructors a_wl_mul_red : core.

Theorem a_wl_mul_red_sound : forall Γ,
  a_wl_mul_red Γ aworklist_empty -> a_wl_red Γ.
Proof.
  intros. dependent induction H; auto.
  assert (IHa_wl_mul_red': Γ2 ⟶ᵃʷ⁎⋅); auto.
  dependent destruction H; auto.
  - eapply a_wl_red__sub_alll with (L:=L); eauto.
    intros. admit. (* rename *)
  - eapply a_wl_red__sub_all with (L:=L); auto.
    intros. admit. (* rename *)
  - eapply a_wl_red__sub_arrow1 with (L:=L) (B1:=B1) (B2:=B2); auto.
    intros. admit. (* rename *)
  - apply a_wl_red__sub_arrow2 with (L:=L) (B1:=B1) (B2:=B2); auto.
    intros. admit. (* rename *)
  - eapply a_wl_red__sub_etvar1; eauto.
  - eapply a_wl_red__sub_etvar2; eauto.
  - eapply a_wl_red__sub_etvarmono1; eauto.
  - eapply a_wl_red__sub_etvarmono2; eauto.
  - eapply a_wl_red__chk_absarrow with (L:=L); eauto. 
    intros. admit. (* rename *)
  - eapply a_wl_red__chk_absevar with (L:=L); eauto.
    intros. admit. (* rename *) 
  - eapply a_wl_red__chk_abstop with (L:=L); eauto.
    intros. admit. (* rename *)
  - eapply a_wl_red__inf_var; eauto.
  - eapply a_wl_red__inf_tabs with (L:=L); eauto.
    intros. admit. (* rename *)
  - eapply a_wl_red__infabs_all with (L:=L); eauto.
    intros. admit. (* rename *)
  - eapply a_wl_red__infabs_evar with (L:=L); eauto.
    intros. admit. (* rename / pls check this *)
  - eapply a_wl_red__applycont; eauto.
(* Why shelved? *)
Admitted. 

Theorem a_wl_mul_red_complete : forall Γ,
  a_wl_red Γ -> a_wl_mul_red Γ aworklist_empty.
Proof.
  intros. dependent induction H.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - eapply a_wl_mul_red__step; eauto.
  - pick fresh x. inst_cofinites_with x.
    eapply a_wl_mul_red__step; eauto.
  - pick fresh x. inst_cofinites_with x.
    eapply a_wl_mul_red__step; eauto.
  - pick fresh x1. inst_cofinites_with x1.
    pick fresh x2. inst_cofinites_with x2.
    