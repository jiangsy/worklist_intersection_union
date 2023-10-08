Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wf_wl : Hdb_a_wl_red_soundness.
Hint Constructors inst_typ : Hdb_a_wl_red_soundness.
Hint Constructors inst_cont : Hdb_a_wl_red_soundness.
Hint Constructors inst_work : Hdb_a_wl_red_soundness.
Hint Constructors inst_worklist : Hdb_a_wl_red_soundness.
Hint Constructors wf_ss : Hdb_a_wl_red_soundness.
Hint Constructors d_wl_del_red : Hdb_a_wl_red_soundness.


Theorem a_mono_typ_wf : forall aE A,
  a_mono_typ aE A -> a_wf_typ aE A.
Proof.
  intros. induction H; auto.
  eapply a_wf_typ__etvar; eauto.
Qed.

Hint Resolve a_mono_typ_wf : Hdb_a_wl_red_soundness.



Ltac destruct_a_wf_wl :=
  repeat
    match goal with
    | H : a_wf_wl (aworklist_conswork ?Γ ?w) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_consvar ?Γ ?w ?b) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_constvar ?Γ ?X ?b) |- _ => dependent destruction H
    | H : a_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : a_wf_typ ?E (?Ct ?A1 ?A2) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?b) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?e1 ?e2) |- _ => dependent destruction H
    end.


Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵃ ?Γ) -> ?P |- _ => destruct_a_wf_wl; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃ Γ) by auto with Hdb_a_wl_red_soundness;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2;
      destruct H2 as [Ω [Htrans Hdred]];
      destruct Htrans as [θ Htrans]
    end.


Hint Resolve a_wf_wl_wf_ss : Hdb_a_wl_red_soundness.



Ltac trans_all_typ :=
  match goal with 
  | H5 : nil ⫦ ?Γ ⇝ ?Ω ⫣ ?θ |- _ => 
    repeat
    match goal with 
    | H1 : a_wf_typ (awl_to_aenv ?Γ) ?C |- _ =>
      let H3 := fresh "Htrans" in
      let H4 := fresh "Htrans"  in
      let C1 := fresh C"ᵈ" in
        lazymatch goal with
        | _ : inst_typ θ C ?Cᵈ |- _ => fail
        | _ : _ |- _ =>
        eapply a_wf_typ_trans_typ in H1 as H3; eauto with Hdb_a_wl_red_soundness
        end;
        destruct H3 as [C1]
    end
  end.

Theorem d_a_wl_red_soundness: forall Γ,
  ⊢ᵃ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto with Hdb_a_wl_red_soundness.
  intros * Hwfa Hared. dependent induction Hared; auto; unfold transfer in *.
  - exists dworklist_empty. intuition...
  - _apply_IH_a_wl_red.   
    trans_all_typ.
    exists (dworklist_consvar Ω x (dbind_typ Aᵈ))...
  - _apply_IH_a_wl_red.
    exists (dworklist_constvar Ω X dbind_tvar_empty)...
    split... exists ((X, dbind_tvar_empty) :: θ)...
  - _apply_IH_a_wl_red.
    exists (dworklist_constvar Ω X dbind_stvar_empty)...
    split... exists ((X, dbind_stvar_empty) :: θ)...
  - destruct_a_wf_wl; intuition; subst; _apply_IH_a_wl_red.
    + apply a_mono_typ_wf in H2.
      apply a_mono_typ_wf in H0.
      dependent destruction Htrans.
      trans_all_typ. admit.
    + dependent destruction Htrans. trans_all_typ. admit.
    + admit.
    + admit.
  - _apply_IH_a_wl_red.
    trans_all_typ.
    exists (dworklist_conswork Ω (work_sub B1ᵈ typ_top)); split...
    exists θ... econstructor... econstructor... admit.
    admit.
  - _apply_IH_a_wl_red.
    trans_all_typ.
    exists (dworklist_conswork Ω (work_sub typ_bot Aᵈ)); split...
    exists θ... econstructor... econstructor... admit. admit.
  - _apply_IH_a_wl_red. 
    exists (dworklist_conswork Ω (work_sub typ_unit typ_unit)).
    split... exists θ... 
    econstructor; eauto... econstructor... 
    econstructor...
    econstructor...
    admit.
  - _apply_IH_a_wl_red.
    dependent destruction H.
    + admit.
    + admit.
    + admit.
  - _apply_IH_a_wl_red.
    dependent destruction Htrans. dependent destruction Htrans.
    dependent destruction H2. dependent destruction H4.
    exists ((work_sub (typ_arrow B1ᵈ A1ᵈ0) (typ_arrow A1ᵈ B1ᵈ0) ⫤ Ω)%dworklist).
    split. exists θ. auto...
    econstructor.
    econstructor. 
    admit.
    admit.
    admit.  
  (* forall x. A < B  *)
  - inst_cofinites_by (L) using_name X.
    assert ( ⊢ᵃ (work_sub (B1 ^ᵈ X) A1 ⫤ aworklist_constvar Γ X (abind_bound typ_bot typ_top))) by admit.
    apply H3 in H4.
    destruct H4 as [Ω].
    destruct H4 as [[θ Htrans] Hdred].
    dependent destruction Htrans. dependent destruction Htrans.
    dependent destruction H9.
    rename A1ᵈ into B1tᵈ. rename B1ᵈ into A1ᵈ.
    apply inst_typ_etvar_tvar_subst_cons in H9...
    destruct H9 as [B1xᵈ].
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) A1ᵈ ⫤ Ω)%dworklist.
    split.
    + exists θ'. econstructor...
      econstructor... econstructor.
      admit. admit.
    + econstructor. 
      dependent destruction Hwfa. 
      dependent destruction H.
      dependent destruction H.
      eapply d_sub__alll with (T:=T) (L:=L)...
      * admit.
      * admit.
      * admit.
      * intros. inst_cofinites_with X0.
        erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X B1xᵈ)) by apply close_typ_notin.
        rewrite open_typ_wrt_typ_close_typ_wrt_typ.
        admit.
      * admit.
      * erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X B1xᵈ)) by apply close_typ_notin.
        rewrite open_typ_wrt_typ_close_typ_wrt_typ.
        admit.
      * dependent destruction Hdred...
    + admit.
    + admit.
  - inst_cofinites_by L using_name X.
    assert ( ⊢ᵃ (work_sub (B1 ^ᵈ X) (A1 ^ᵈ X) ⫤ aworklist_constvar Γ X abind_stvar_empty) ) by admit.
    apply H0 in H1.
    destruct H1 as [Ω].
    destruct H1 as [[θ Htrans] Hdred]...
    dependent destruction Htrans...
    dependent destruction Htrans...
    dependent destruction H1.
    rename A1ᵈ into B1xᵈ. rename B1ᵈ into A1xᵈ.
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) (typ_all (close_typ_wrt_typ X A1xᵈ)) ⫤ Ω)%dworklist.
    split.
    + exists θ'. admit.
    + dependent destruction Hdred. admit.
  - inst_cofinites_by L using_name X.
    inst_cofinites_by (L `union` singleton X0) using_name X.
    admit.  
  - admit.
  - admit.
  - admit.
  (* tau < ^X *)
  - admit.

  - admit.
  - _apply_IH_a_wl_red.
    dependent destruction Htrans. dependent destruction H1.
    dependent destruction Htrans. dependent destruction H1.
    eapply inst_typ_det in H1... subst.
    rename B1ᵈ0 into B2ᵈ.
    exists (work_sub A1ᵈ (typ_intersection B1ᵈ B2ᵈ) ⫤ Ω)%dworklist. split...
    dependent destruction Hdred.
    dependent destruction Hdred.
    econstructor... 
    admit.
  (* simple *)
  - admit.
  (* simple *)
  - admit.
  (* simpl *)
  - admit.
  (* simpl *)
  - admit.
  (* simpl *)
  - admit.
  - _apply_IH_a_wl_red.
    dependent destruction H1. dependent destruction H1.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.
