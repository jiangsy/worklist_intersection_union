Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import uni.decl.prop_typing.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import uni.algo_worklist.prop_rename.
Require Import uni.algo_worklist.transfer.
Require Import ln_utils.


Hint Constructors a_wf_wl : core.

#[local] Hint Constructors d_wl_del_red aworklist_subst : core.
#[local] Hint Resolve wf_ss_uniq a_wf_wl_d_wf_env : core.

Open Scope aworklist_scope.


Ltac rename_typ_to_fresh' :=
  repeat 
    lazymatch goal with
    | H : trans_typ ?θ (open_typ_wrt_typ _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ (?C_T _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ ?A1ᵃ ?A1ᵈ |- _ => 
      let A1ᵃ1 := fresh A1ᵃ"ᵈ0" in 
      rename A1ᵈ into A1ᵃ1;
      generalize dependent H
    end.
    
Ltac rename_typ' :=
  repeat 
    lazymatch goal with
    | H : trans_typ ?θ (open_typ_wrt_typ _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ (?C_T _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ ?A1ᵃ ?A1ᵈ |- _ => 
      let A1ᵃ1 := fresh A1ᵃ"ᵈ" in 
      rename A1ᵈ into A1ᵃ1;
      generalize dependent H
    end.

Ltac rename_typ :=
  rename_typ_to_fresh';
  intros;
  rename_typ';
  intros.

(* dependent destruction all non-atomic trans_* relation *)
Ltac destruct_trans :=
  repeat
    lazymatch goal with
    | H : trans_worklist ?θ (aworklist_conswork ?Γ ?w) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ (aworklist_consvar ?Γ ?w ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ  (aworklist_constvar ?Γ ?X ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_work ?θ (?wᵃ _ _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_conts ?θ (?C_CS _) ?wᵈ |- _ => dependent destruction H
    | H : trans_conts ?θ (?C_CS _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_contd ?θ (?C_CD _ ) ?wᵈ |- _ => dependent destruction H
    | H : trans_contd ?θ (?C_CD _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_contd ?θ (?C_CD _ _ _) ?wᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ typ_unit ?Aᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ typ_bot ?Aᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ typ_top ?Aᵈ |- _ => dependent destruction H
    | H : trans_typ ?θ (open_typ_wrt_typ _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ (?C_T _ _) ?Aᵈ |- _ => dependent destruction H
    end;
    try unify_trans_typ;
    try unify_trans_exp.


Theorem a_mono_typ_wf : forall Σ A,
  a_mono_typ Σ A -> a_wf_typ Σ A.
Proof.
  intros. induction H; auto.
Qed.

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp : core.
#[local] Hint Resolve a_mono_typ_wf : core.
#[local] Hint Resolve wf_ss_weaken_tvar wf_ss_weaken_stvar wf_ss_weaken_etvar : core.

(* assert the well-formedness and apply the induction hypothesis  *)
Ltac _apply_IH_a_wl_red :=
  let H := fresh "H" in
    match goal with 
    | H : (⊢ᵃʷ ?Γ) -> ?P |- _ => destruct_a_wf_wl; 
      let H1 := fresh "H" in
      assert (H1 : ⊢ᵃʷ Γ) by auto;
      let H2 := fresh "IHHdred" in
      apply H in H1 as H2;
      destruct H2 as [Ω [Htrans Hdred]];
      destruct Htrans as [θ Htrans]
    end.


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
        | _ : trans_typ θ C ?Cᵈ |- _ => fail
        | _ : _ |- _ =>
        eapply trans_typ_total in H1 as H3; eauto
        end;
        destruct H3 as [C1]
    end
  end.

#[local] Hint Constructors wf_ss : core.
#[local] Hint Resolve trans_typ_wf_ss : core.

Lemma trans_typ_subst_tvar : forall θ1 θ2 Bᵃ Bᵈ X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  wf_ss (θ2 ++ θ1) ->
  X `notin` dom (θ2 ++ θ1) ->
  θ1 ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {Bᵈ /ᵗ X} Aᵈ = A'ᵈ /\ θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros *  Hlc Hwfss Hfv Hwft Hinst. 
  generalize dependent θ2. generalize dependent X. generalize dependent A'ᵈ.
  dependent induction Hlc; simpl in *; intros.
  - dependent destruction Hinst. 
    exists typ_unit...  
  - dependent destruction Hinst. 
    exists typ_top... 
  - dependent destruction Hinst;
    exists typ_bot...
  - destruct_eq_atom.
    + exists (` X0). simpl. destruct_eq_atom; split.
      * rewrite_env (nil ++ θ1) in Hwft.
        apply trans_typ_weaken with (θ2:=θ2) in Hwft...
        apply trans_typ_det with (A₁ᵈ:=A'ᵈ) in Hwft...
      * constructor; auto. 
    + exists A'ᵈ. split.
      rewrite <- ftvar_in_trans_dtyp_upper in Hfv; eauto.
      * apply subst_tvar_in_typ_fresh_eq...
      * rewrite_env (θ2 ++ (X0 ~ □) ++ θ1). apply trans_typ_weaken... 
        apply wf_ss_weaken_tvar...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_arrow A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
  - dependent destruction Hinst.  
    pick fresh X0. inst_cofinites_with X0.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2 in H1...
    rewrite_env (((X0, dbind_tvar_empty) :: θ2) ++ θ1) in H1.
    apply H0 in H1; simpl...
    destruct H1 as [Aᵈ].
    exists (typ_all (close_typ_wrt_typ X0 Aᵈ)). simpl.
    rewrite subst_tvar_in_typ_close_typ_wrt_typ... 
    split...
    + apply f_equal. erewrite typ_open_r_close_l... intuition.
    + eapply trans_typ__all with (L:=L `union` dom (θ2 ++ (X, □) :: θ1)); intros.
      intuition.
      erewrite subst_tvar_in_typ_intro by auto.
      erewrite (subst_tvar_in_typ_intro X0 (close_typ_wrt_typ X0 Aᵈ)) by apply close_typ_wrt_typ_notin.
      apply trans_typ_rename_tvar_cons...
      rewrite open_typ_wrt_typ_close_typ_wrt_typ...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_union A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_intersection A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
Qed.


Lemma trans_typ_subst_tvar_cons : forall θ Bᵃ Bᵈ X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X `notin` dom θ ->
  θ ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {Bᵈ /ᵗ X} Aᵈ = A'ᵈ /\ (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  rewrite_env (nil ++ θ) in H2.
  eapply trans_typ_subst_tvar in H2...
Qed.


Lemma trans_typ_subst_etvar : forall θ1 θ2 Tᵃ Tᵈ X Aᵃ Aᵈ,
  lc_typ Aᵃ -> 
  wf_ss (θ2 ++ θ1) ->
  X `notin` dom (θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) Tᵈ ->
  θ2 ++ θ1 ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ2 ++ θ1 ⫦ᵗ {Tᵃ /ᵗ X} Aᵃ ⇝ Aᵈ -> 
  θ2 ++ X ~ dbind_typ Tᵈ ++ θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof.
  intros * Hlc Hwfss Hnotin Hmono Hinstt Hinsta.
  generalize dependent θ2. generalize dependent X. generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros.
  - dependent destruction Hinsta. 
    constructor...
    apply wf_ss_weaken_etvar; auto.
  - dependent destruction Hinsta. 
    constructor...
    apply wf_ss_weaken_etvar; auto.
  - dependent destruction Hinsta.
    constructor... 
    apply wf_ss_weaken_etvar; auto.
  - destruct_eq_atom.
    + constructor. 
      * apply wf_ss_weaken_etvar; auto.
      * rewrite_env (nil ++ θ1) in Hinstt. 
        apply trans_typ_det with (A₁ᵈ:=Aᵈ) in Hinstt; auto. 
        -- subst. auto.
    + dependent destruction Hinsta.
      * apply trans_typ__tvar.
        apply wf_ss_weaken_etvar; auto. 
        rewrite_env ((θ2 ++ (X0 ~ dbind_typ Tᵈ) ++ θ1)).
        apply binds_weaken; auto.
      * apply trans_typ__stvar.
        apply wf_ss_weaken_etvar; auto. 
        rewrite_env ((θ2 ++ (X0 ~ dbind_typ Tᵈ) ++ θ1)).
        apply binds_weaken; auto.
      * apply trans_typ__etvar...
        apply wf_ss_weaken_etvar; auto. 
        rewrite_env ((θ2 ++ (X0 ~ dbind_typ Tᵈ) ++ θ1)).
        apply binds_weaken; auto.
  - simpl in Hinsta.
    dependent destruction Hinsta. constructor; auto.
  - simpl in Hinsta. 
    dependent destruction Hinsta. 
    inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X0.
    rewrite_env (((X0, □) :: θ2) ++ (X, dbind_typ Tᵈ) :: θ1).
    apply H0; auto.
    + simpl. constructor; auto.
    + simpl. rewrite_env (nil ++ (X0 ~ □) ++ (θ2 ++ θ1)). 
      apply trans_typ_weaken; auto.
      constructor; auto.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ.
      * simpl. destruct_eq_atom. auto.
      * eapply trans_typ_lc_atyp; eauto.
  - simpl in Hinsta.
    dependent destruction Hinsta. constructor; auto.
  - simpl in Hinsta.
    dependent destruction Hinsta. constructor; auto.
Qed.


Lemma trans_typ_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X Aᵃ Aᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵗ {Tᵃ /ᵗ X} Aᵃ ⇝ Aᵈ -> 
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof.
  intros.
  assert (exists θ1 θ2, θ = θ2 ++ X ~ dbind_typ Tᵈ ++ θ1) by admit.
  destruct H4 as [θ1 [θ2 Heq]].
  rewrite  Heq in *.
  apply trans_typ_strengthen_etvar in H2; auto.
  apply trans_typ_strengthen_etvar in H3; auto.
  eapply trans_typ_subst_etvar; eauto.
  - apply lc_typ_subst_inv with (T:=Tᵃ) (X:=X).
    eapply trans_typ_lc_atyp; eauto.
    eapply trans_typ_lc_atyp; eauto.
  - admit.
  - clear H0 H1 Heq H2 H3. induction θ2; simpl in *. 
    + inversion H; auto.
    + inversion H; apply IHθ2; eauto.
  - apply subst_tvar_in_typ_fresh_same; auto.
Admitted.


Lemma trans_exp_subst_etvar_same_ss' : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵉ (subst_tvar_in_exp Tᵃ X eᵃ) ⇝ eᵈ -> 
  θ ⫦ᵉ eᵃ ⇝ eᵈ
with trans_body_subst_etvar_same_ss' : forall θ Tᵃ Tᵈ X bᵃ bᵈ,
  lc_body bᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵇ (subst_tvar_in_body Tᵃ X bᵃ) ⇝ bᵈ -> 
  θ ⫦ᵇ bᵃ ⇝ bᵈ.
Proof.
  - intros * Hlc.
    generalize dependent θ. generalize dependent eᵈ.
    induction Hlc; simpl in *; intros.
    + dependent destruction H3; constructor; auto.
    + dependent destruction H3; constructor; auto.
    + dependent destruction H5.
      inst_cofinites_for trans_exp__abs. intros.
      apply H0; auto.
      rewrite subst_tvar_in_exp_open_exp_wrt_exp.
      simpl. auto.
    + dependent destruction H3; eauto.
    + dependent destruction H4; eauto.
      inst_cofinites_for trans_exp__tabs.
      intros. inst_cofinites_with X0.
      eapply trans_body_subst_etvar_same_ss'; eauto.
      * rewrite_env (nil ++ (X0 ~ □) ++ θ). apply trans_typ_weaken; auto.
        constructor; auto.
      * rewrite subst_tvar_in_body_open_body_wrt_typ; simpl.
        destruct_eq_atom; auto.
        eapply trans_typ_lc_atyp; eauto.
    + dependent destruction H4.
      constructor.
      * apply IHHlc; eauto.
      * eapply trans_typ_subst_etvar_same_ss; eauto.
    + dependent destruction H4.
      constructor.
      * apply IHHlc; eauto.
      * eapply trans_typ_subst_etvar_same_ss; eauto.
  - intros * Hlc. dependent destruction Hlc; intros; simpl in *.
    dependent destruction H5. constructor.
    + eapply trans_exp_subst_etvar_same_ss'; eauto.
    + eapply trans_typ_subst_etvar_same_ss; eauto.
Qed.


Lemma trans_exp_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵉ (subst_tvar_in_exp Tᵃ X eᵃ) ⇝ eᵈ -> 
  θ ⫦ᵉ eᵃ ⇝ eᵈ
with trans_body_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X bᵃ bᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᵇ (subst_tvar_in_body Tᵃ X bᵃ) ⇝ bᵈ -> 
  θ ⫦ᵇ bᵃ ⇝ bᵈ.
Proof.
  - intros. clear trans_exp_subst_etvar_same_ss. clear  trans_body_subst_etvar_same_ss.
    apply trans_exp_lc_aexp in H3 as Hlce.
    apply trans_typ_lc_atyp in H2 as Hlct.
    apply lc_exp_subst_tvar_in_exp_inv in Hlce; auto.
    eapply trans_exp_subst_etvar_same_ss'; eauto. 
  - intros. clear trans_exp_subst_etvar_same_ss. clear trans_body_subst_etvar_same_ss.
    apply trans_body_lc_abody in H3 as Hlcb.
    apply trans_typ_lc_atyp in H2 as Hlct.
    apply lc_body_subst_tvar_in_body_inv in Hlcb; auto.
    eapply trans_body_subst_etvar_same_ss'; eauto. 
Qed.


Lemma trans_conts_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X csᵃ csᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᶜˢ (subst_tvar_in_conts Tᵃ X csᵃ) ⇝ csᵈ -> 
  θ ⫦ᶜˢ csᵃ ⇝ csᵈ
with trans_contd_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X cdᵃ cdᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ᶜᵈ (subst_tvar_in_contd Tᵃ X cdᵃ) ⇝ cdᵈ -> 
  θ ⫦ᶜᵈ cdᵃ ⇝ cdᵈ.
Proof.
  intros. generalize dependent θ. generalize dependent csᵈ.
  induction csᵃ; intros; simpl in *; dependent destruction H3;
    constructor;
      try eapply trans_typ_subst_etvar_same_ss;
      try eapply trans_exp_subst_etvar_same_ss;
      try apply trans_contd_subst_etvar_same_ss; 
      try apply IHcsᵃ; eauto.
  intros. generalize dependent θ. generalize dependent cdᵈ.
  induction cdᵃ; intros; simpl in *; dependent destruction H3;
    constructor;
      try eapply trans_typ_subst_etvar_same_ss; 
      try eapply trans_exp_subst_etvar_same_ss;
      try apply trans_contd_subst_etvar_same_ss; 
      try apply IHcsᵃ; eauto.
Qed.

Lemma trans_work_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X wᵃ wᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X `notin` ftvar_in_typ Tᵃ ->
  θ ⫦ᵗ Tᵃ ⇝ Tᵈ ->
  θ ⫦ʷ (subst_tvar_in_work Tᵃ X wᵃ) ⇝ wᵈ -> 
  θ ⫦ʷ wᵃ ⇝ wᵈ.
Proof.
  intros. destruct wᵃ; try simpl in *; dependent destruction H3;
    constructor; 
      try eapply trans_typ_subst_etvar_same_ss; eauto;
      try eapply trans_exp_subst_etvar_same_ss; eauto;
      try eapply trans_conts_subst_etvar_same_ss; eauto;
      try eapply trans_contd_subst_etvar_same_ss; eauto.
Qed.

#[local] Hint Resolve wf_ss_etvar_tvar : core.

Lemma trans_typ_etvar_tvar_subst : forall θ1 θ2 T X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X `notin` dom (θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) T ->
  θ2 ++ (X, dbind_typ T) :: θ1 ⫦ᵗ Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {T /ᵗ X} Aᵈ = A'ᵈ /\ θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros * Hlc Hfv Hwft Hinst.
  generalize dependent θ2. generalize dependent X. generalize dependent A'ᵈ.
  dependent induction Hlc; simpl in *; intros.
  - dependent destruction Hinst.
    exists typ_unit...
  - dependent destruction Hinst. 
    exists typ_top... 
  - dependent destruction Hinst.
    exists typ_bot...
  - destruct (X == X0) in *.
    + subst. exists (` X0). split.
      * simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X0).
        -- subst. eapply trans_typ_det with (θ:=(θ2 ++ (X0, dbind_typ T) :: θ1))...
        -- contradiction.
      * econstructor...
    + dependent destruction Hinst.
      * exists ` X. intuition...
        econstructor...
        apply binds_remove_mid in H0...
        rewrite_env (θ2 ++ (X0 ~  □) ++ θ1).
        eapply binds_weaken...
      * exists ` X... intuition...
        apply trans_typ__stvar...
        apply binds_remove_mid in H0...
        rewrite_env (θ2 ++ (X0 ~  □) ++ θ1).
        eapply binds_weaken...
      * exists A1. split.
        -- rewrite subst_tvar_in_typ_fresh_eq...
           eapply etvar_bind_no_etvar...
        -- econstructor...
           apply binds_remove_mid in H0...
           rewrite_env (θ2 ++ (X0 ~  □) ++ θ1).
           eapply binds_weaken...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_arrow A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
  - dependent destruction Hinst.  
    pick fresh X0. inst_cofinites_with X0.
    rewrite_env (((X0, dbind_tvar_empty) :: θ2) ++ (X, dbind_typ T) :: θ1) in H1.
    apply H0 in H1...
    destruct H1 as [Aᵈ].
    exists (typ_all (close_typ_wrt_typ X0 Aᵈ)). simpl. 
    rewrite subst_tvar_in_typ_close_typ_wrt_typ... 
    split.
    + apply f_equal. erewrite typ_open_r_close_l... intuition.
    + eapply trans_typ__all with (L:=L `union` (dom (θ2 ++ (X, □) :: θ1))); intros.
      intuition.
      erewrite subst_tvar_in_typ_intro by auto.
      erewrite (subst_tvar_in_typ_intro X0 (close_typ_wrt_typ X0 Aᵈ)) by apply close_typ_wrt_typ_notin.
      apply trans_typ_rename_tvar_cons...
      rewrite open_typ_wrt_typ_close_typ_wrt_typ...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_union A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_intersection A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
Qed.


Lemma trans_typ_etvar_tvar_subst_cons : forall θ1 T X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X `notin` dom θ1 ->
  d_mono_typ (ss_to_denv θ1) T ->
  (X, dbind_typ T) :: θ1 ⫦ᵗ Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {T /ᵗ X} Aᵈ = A'ᵈ /\ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with auto. 
  intros. 
  rewrite_env (nil ++ (X, □) :: θ1).  
  apply trans_typ_etvar_tvar_subst...
Qed.


#[local] Hint Immediate trans_wl_wf_ss : core.


Lemma a_worklist_subst_transfer_same_dworklist: forall Γ Ω θ X T Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  a_mono_typ (awl_to_aenv Γ) T ->
  X `notin` ftvar_in_typ T ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  trans_worklist nil (awl_app (subst_tvar_in_aworklist T X Γ2) Γ1)  Ω θ ->
  exists θ' Tᵈ, 
      trans_worklist nil Γ Ω θ' /\ 
      θ ⫦ᵗ T ⇝ Tᵈ /\ 
      θ' ⫦ᵗ T ⇝ Tᵈ /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      binds X (dbind_typ Tᵈ) θ' /\
      wf_ss θ'.
Proof with auto.
  intros. generalize dependent θ. generalize dependent Ω. dependent induction H2; intros.
  - simpl in *.
    assert (exists Aᵈ, θ ⫦ᵗ A ⇝ Aᵈ) by admit. (* *, trans_typ_total s*)
    destruct H2 as [Aᵈ].
    destruct_a_wf_wl.
    exists ((X ~ dbind_typ Aᵈ) ++ θ). 
    exists Aᵈ.
    assert (wf_ss ((X ~ dbind_typ Aᵈ) ++ θ)). { 
      constructor; eauto.
      erewrite trans_wl_ss_dom_upper_bound; eauto. 
      admit. }
    dependent destruction H5.
    repeat split; auto.
    + econstructor; auto.  
    + apply trans_typ_weaken_cons...
    + intros. destruct_binds...
    + constructor...
  - dependent destruction H3. 
    apply IHaworklist_subst in H3 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].
    exists θ'1. exists Tᵈ. repeat split; auto.
    + constructor. auto.
      eapply trans_typ_subst_etvar_same_ss; eauto.
      eapply trans_typ_reorder with (θ:=θ'); eauto.
      intros. apply Hbinds... 
      unfold not. intros. subst.
      apply subst_tvar_in_typ_fresh_same in H5...
    + intros. apply Hbinds; auto.
    + intros. apply Hbinds; auto.
    + destruct_a_wf_wl...
    + admit. (* *, mono *)
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists ((Y , dbind_tvar_empty) :: θ'1), Tᵈ. repeat split; auto.
    + econstructor; auto.
      admit. (* *, notin *)
    + rewrite_env (nil ++ (Y ~ □) ++ θ'). apply trans_typ_weaken...
      constructor; auto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ □) ++ θ'1). apply trans_typ_weaken...
      constructor; auto.
      eapply notin_dom_reorder...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + simpl. constructor; eauto. admit. (* *, notin *)
    + destruct_a_wf_wl...
    + admit. (* *, mono *)
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists (Y ~ dbind_stvar_empty ++ θ'1), Tᵈ. repeat split; auto.
    + econstructor; auto.
      admit. (* *, notin *)
    + rewrite_env (nil ++ (Y ~ ■) ++ θ'). apply trans_typ_weaken...
      econstructor; auto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ ■) ++ θ'1). apply trans_typ_weaken... 
      constructor; auto.
      eapply notin_dom_reorder...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + simpl. constructor... 
      eapply notin_dom_reorder...
    + destruct_a_wf_wl...
    + admit. (* *, mono *)
    + auto.
  (* work_stay *)
  - dependent destruction H3.
    apply IHaworklist_subst in H3 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists θ'1. exists Tᵈ. repeat split; auto.
    + constructor; auto.
      eapply trans_work_subst_etvar_same_ss; eauto.
      apply trans_work_reorder with (θ:=θ'); eauto.
      * intros. apply Hbinds; auto.
        unfold not. intros. subst.
        apply subst_tvar_in_work_fresh_same in H5; auto.
    + apply Hbinds...
    + apply Hbinds...
    + destruct_a_wf_wl...
    + simpl in H0...
    + auto.
  - dependent destruction H5.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists (Y ~ dbind_typ T ++ θ'1). exists Tᵈ. repeat split; auto.
    + econstructor; auto. 
      eapply notin_dom_reorder...
      admit. (* *, mono *)
    + rewrite_env (nil ++ (Y ~ dbind_typ T) ++ θ'). apply trans_typ_weaken...
      constructor; auto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ dbind_typ T) ++ θ'1). apply trans_typ_weaken...
      constructor; auto.
      eapply notin_dom_reorder...
      admit. (* *, mono *)
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + constructor; auto. 
      eapply notin_dom_reorder...
      admit. (* *, monos *)
    + destruct_a_wf_wl...
    + admit. (* *, mono *)
    + auto.
  - simpl in *.
    apply IHaworklist_subst in H5 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].
    apply trans_wl_split in Htrans.
    destruct Htrans as [Ω1 [Ω2 [θ' [Heq [Htrans1 Htrans2]]]]].
    dependent destruction Htrans1.
    dependent destruction Htrans1.
    apply trans_wl_split_ss in Htrans2 as Hsplitss.
    destruct Hsplitss as [θ'' Heqss]. rewrite Heqss in *.
    exists ((Y, dbind_typ T0) :: θ'' ++ (X, dbind_typ T) :: θ').
    exists Tᵈ. repeat split; auto.
    + constructor.
      rewrite_env ((X ~ dbind_typ T) ++ (Y, dbind_typ T0) :: θ') in Htrans2.
      rewrite_env ((θ'' ++ X ~ dbind_typ T) ++ (Y, dbind_typ T0) :: θ') in Htrans2.
      apply trans_wl_strengthen_etvar_gen in Htrans2.
      replace (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)%aworklist with (Γ2 ⧺ (X ~ᵃ ⬒ ;ᵃ Γ1))%aworklist by admit.
      rewrite Heq.
      eapply trans_wl_app with (θ2:= X ~ dbind_typ T ++ θ'); eauto.
      constructor; eauto.
      rewrite_env ((θ'' ++ X ~ dbind_typ T) ++ θ'). auto.
      admit. (* *, notin *)
      admit. (* *, notin *)
      admit. (* *, mono *)
    + eapply trans_typ_reorder with (θ:=θ'' ++ (X, dbind_typ T) :: (Y, dbind_typ T0) :: θ'); auto.
      admit. (* *, wf_ss *)
      intros.
      apply binds_same_move_etvar_before...
    + intros. 
      apply binds_same_move_etvar_before...
      apply Hbinds...
    + intros. 
      apply Hbinds...
      apply binds_same_move_etvar_before...
    + subst. apply binds_same_move_etvar_before... 
    + admit.
    + apply a_wf_wl_move_etvar_back... 
    + admit. (* *, mono *)
    + auto.
Admitted.


Lemma trans_wl_a_wl_binds_var_trans_typ_d_wl' : forall θ Γ Ω x Aᵃ Aᵈ,
  ⊢ᵃʷ Γ ->
  ⊢ᵈʷ Ω ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds x (abind_var_typ Aᵃ) (awl_to_aenv Γ) ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds x (dbind_typ Aᵈ) (dwl_to_denv Ω).
Proof with eauto.
  intros.
  eapply trans_wl_a_wl_binds_var_binds_d_wl_and_trans in H2; eauto.
  destruct H2 as [Aᵈ' [Hbinds Htrans]].
  unify_trans_typ...
Qed.


Lemma trans_wl_a_wl_binds_var_trans_typ_d_wl : forall θ Γ Ω x Aᵃ Aᵈ,
  ⊢ᵃʷ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds x (abind_var_typ Aᵃ) (awl_to_aenv Γ) ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds x (dbind_typ Aᵈ) (dwl_to_denv Ω).
Proof.
  intros. eapply trans_wl_a_wf_wl_d_wf_wl in H0 as Hdwf; auto.
  eapply trans_wl_a_wl_binds_var_trans_typ_d_wl'; eauto.
Qed.
  

Ltac solve_notin_dom :=
  rewrite awl_to_aenv_app in *; rewrite dom_aenv_app_comm in *; simpl in *; auto.

Lemma worklist_subst_fresh_etvar_total : forall Γ1 Γ2 X X1 X2,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  X1 `notin` dom (awl_to_aenv (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1)) ->
  X2 `notin` add X1 (dom (awl_to_aenv (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1))) ->
  aworklist_subst (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X
    (typ_arrow ` X1 ` X2) (X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) Γ2.
Proof with auto.
  induction Γ2; intros; simpl in *; auto.
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ aworklist_empty) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1);
    constructor; simpl...
    replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X1 ~ᵃ ⬒ ;ᵃ aworklist_empty ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1);
    constructor; simpl...
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) x ab) with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar Γ2 x ab) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1);
    constructor; simpl...
    replace (X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) x ab) with
      ((X1 ~ᵃ ⬒ ;ᵃ aworklist_consvar Γ2 x ab) ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1); 
    constructor; simpl...
    + dependent destruction H...
      simpl.
      constructor; auto.
      eapply IHΓ2 with (X1:=X1) (X2:=X2) in H1 as Hws...
      dependent destruction Hws...
      * simpl in *. solve_notin_eq X2.
      * simpl in *. solve_notin_eq X2.
      * replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) with 
        ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) in x by auto.
        apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
        dependent destruction Hws; auto; simpl in *.
        -- solve_notin_eq X1.
        -- solve_notin_eq X1.
        -- replace (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) 
            with  (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1)) in x by auto.
            apply worklist_split_etvar_det in x; auto.
            destruct x; subst...
            apply a_wf_wl_tvar_notin_remaining in H1; auto.
        -- simpl. apply a_wf_wl_tvar_notin_remaining in H1...
           solve_notin_dom.
    + solve_notin_dom.
    + solve_notin_dom.
  - dependent destruction H.
    + replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ □ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ □ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1);
      constructor; simpl; auto.
      replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ □ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X1 ~ᵃ ⬒ ;ᵃ (X ~ᵃ □ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1));
      constructor; simpl; auto.
      * constructor; auto.
        eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
        dependent destruction Hws; auto.
        -- simpl in *. solve_notin_eq X2.
        -- simpl in *. solve_notin_eq X2.
        -- replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
             ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) in x by auto.
           apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
           dependent destruction Hws; auto; simpl in *.
           ++ solve_notin_eq X1.
           ++ solve_notin_eq X1.
           ++ replace (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) 
                with (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1)) in x by auto.
              apply worklist_split_etvar_det in x; auto.
              destruct x; subst; auto.
              apply a_wf_wl_tvar_notin_remaining in H0; auto.
              ++ simpl. apply a_wf_wl_tvar_notin_remaining in H0; auto.
                 solve_notin_dom.
        -- solve_notin_dom.
      * solve_notin_dom.
      * solve_notin_dom.
    + replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ■ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ■ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1);
      constructor; simpl; auto.
      replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ■ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X1 ~ᵃ ⬒ ;ᵃ (X ~ᵃ ■ ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1));
      constructor; simpl; auto.
      * constructor; auto.
        eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
        dependent destruction Hws; auto.
        -- simpl in *. solve_notin_eq X2.
        -- simpl in *. solve_notin_eq X2.
        -- replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
            ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) in x by auto.
          apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
          dependent destruction Hws; auto; simpl in *.
          ++ solve_notin_eq X1.
          ++ solve_notin_eq X1.
          ++ replace (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) 
                with (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1)) in x by auto.
              apply worklist_split_etvar_det in x; auto.
              destruct x; subst; auto.
              apply a_wf_wl_tvar_notin_remaining in H0; auto.
              ++ simpl. apply a_wf_wl_tvar_notin_remaining in H0; auto.
                 solve_notin_dom.
        -- solve_notin_dom.
      * solve_notin_dom.
      * solve_notin_dom.
    + replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒  ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1);
      constructor; simpl; auto.
      replace (X1 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) with 
      (X1 ~ᵃ ⬒ ;ᵃ (X ~ᵃ ⬒  ;ᵃ Γ2) ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1));
      constructor; simpl; auto.
      * constructor; auto.
        eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
        dependent destruction Hws; auto.
        -- simpl in *. solve_notin_eq X2.
        -- simpl in *. solve_notin_eq X2.
        -- replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
            ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) in x by auto.
          apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
          dependent destruction Hws; auto; simpl in *.
          ++ solve_notin_eq X1.
          ++ solve_notin_eq X1.
          ++ replace (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) 
                with (Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1)) in x by auto.
              apply worklist_split_etvar_det in x; auto.
              destruct x; subst; auto.
              apply a_wf_wl_tvar_notin_remaining in H0; auto.
              ++ simpl. apply a_wf_wl_tvar_notin_remaining in H0; auto.
                 solve_notin_dom.
        -- solve_notin_dom.
      * solve_notin_dom.
      * solve_notin_dom.
 - dependent destruction H. 
   replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ w ⫤ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) with 
    (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ w ⫤ᵃ Γ2) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1);
   constructor; simpl; auto.
   replace (X1 ~ᵃ ⬒ ;ᵃ w ⫤ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) with 
    (X1 ~ᵃ ⬒ ;ᵃ (w ⫤ᵃ Γ2) ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1));
   constructor; simpl; auto.
   + constructor; auto.
     eapply IHΓ2 with (X1:=X1) (X2:=X2) in H0 as Hws; eauto.
     dependent destruction Hws; auto.
     * simpl in *. solve_notin_eq X2.
     * simpl in *. solve_notin_eq X2.
     * replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) with 
         ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) in x by auto.
       apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
       dependent destruction Hws; auto; simpl in *.
       -- solve_notin_eq X1.
       -- solve_notin_eq X1.
       -- replace (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) with 
           (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1)) in x; auto.
          apply worklist_split_etvar_det in x; auto.
          destruct x; subst; auto.
          apply a_wf_wl_tvar_notin_remaining in H0; auto.
       -- apply a_wf_wl_tvar_notin_remaining in H0; auto. solve_notin_dom.
   + solve_notin_dom.
   + solve_notin_dom.
Qed.




Lemma worklist_subst_fresh_etvar_total' : forall Γ X X1 X2,
  ⊢ᵃʷ Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  X1 `notin` dom (awl_to_aenv Γ) ->
  X2 `notin` add X1 (dom (awl_to_aenv Γ)) ->
  exists Γ1 Γ2, aworklist_subst (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
      (typ_arrow ` X1 ` X2) Γ1 Γ2.
Proof.
  intros. apply aworklist_binds_split in H0.
  destruct H0 as [Γ1 [Γ2 Heq]].
  rewrite <- Heq in *.
  eapply worklist_subst_fresh_etvar_total in H; eauto.
  auto.
Qed.


Ltac rewrite_close_open_subst :=
  match goal with
  | H : _ |- context [open_typ_wrt_typ (close_typ_wrt_typ ?X ?A) ?B] =>
      erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X A)) by apply close_typ_wrt_typ_notin;
      rewrite open_typ_wrt_typ_close_typ_wrt_typ
  | H : _ |- context [open_exp_wrt_typ (close_exp_wrt_typ ?X ?e) ?B] =>
      erewrite (subst_tvar_in_exp_intro X (close_exp_wrt_typ X e)) by apply close_exp_wrt_typ_notin;
      rewrite open_exp_wrt_typ_close_exp_wrt_typ
  | H : _ |- context [open_exp_wrt_exp (close_exp_wrt_exp ?x ?e) ?e'] =>
      erewrite (subst_var_in_exp_intro x (close_exp_wrt_exp x e)) by apply close_exp_wrt_exp_notin;
      rewrite open_exp_wrt_exp_close_exp_wrt_exp
  | H : _ |- _ => idtac
  end.

Ltac simpl_open_subst_typ' :=
  match goal with
  | H : context [ {?B /ᵗ ?X} (?A ^ᵗ (?X')) ] |- _ =>
    rewrite subst_tvar_in_typ_open_typ_wrt_typ in H; auto;
    simpl in H; try destruct_eq_atom; auto
    (* try solve [rewrite subst_tvar_in_typ_fresh_eq in H; auto] *)
  | H1 : context [ {?B /ᵗ ?X} ?A ], H2 : context [ftvar_in_typ ?A] |- _ =>
      let H := fresh "H" in
      try (
        assert (H : X `notin` ftvar_in_typ A) by auto;
        rewrite subst_tvar_in_typ_fresh_eq in H1; auto; clear H)
end.

Ltac  simpl_open_subst_typ :=
  repeat simpl_open_subst_typ'.

Ltac solve_trans_typ_open_close' :=
  match goal with
  | H : ?θ ⫦ᵗ ?A1ᵃ ⇝ ?Aᵈ |- ?θ' ⫦ᵗ ?A2ᵃ ⇝ ({(` ?X1') /ᵗ ?X} ?Aᵈ) => 
      apply trans_typ_rename_tvar_cons with (X':=X1') in H; eauto
  end.


Ltac solve_trans_typ_open_close :=
  rewrite_close_open_subst;
  solve_trans_typ_open_close';
  simpl_open_subst_typ.

#[local] Hint Resolve trans_wl_wf_ss trans_typ_wf_ss wf_ss_uniq : core.
#[local] Hint Resolve trans_typ_lc_atyp : core.


Lemma trans_apply_conts : forall θ csᵃ csᵈ Aᵃ Aᵈ wᵃ wᵈ,
  θ ⫦ᶜˢ csᵃ ⇝ csᵈ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ ⫦ʷ wᵃ ⇝ wᵈ ->
  apply_conts csᵃ Aᵃ wᵃ ->
  apply_conts csᵈ Aᵈ wᵈ.
Proof.
  intros. dependent destruction H2; destruct_trans;
    try unify_trans_contd; try unify_trans_conts; 
    try repeat unify_trans_typ; try unify_trans_exp; try constructor.
Qed.

Lemma trans_apply_contd : forall θ cdᵃ cdᵈ Aᵃ Aᵈ Bᵃ Bᵈ wᵃ wᵈ,
  θ ⫦ᶜᵈ cdᵃ ⇝ cdᵈ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ ⫦ʷ wᵃ ⇝ wᵈ ->
  apply_contd cdᵃ Aᵃ Bᵃ wᵃ ->
  apply_contd cdᵈ Aᵈ Bᵈ wᵈ.
Proof with eauto.
Proof.
  intros. dependent destruction H3; destruct_trans;
    try unify_trans_contd; try unify_trans_conts; 
    try repeat unify_trans_typ; try unify_trans_exp; try constructor.
Qed.


#[local] Hint Resolve trans_typ_wf_ss trans_wl_a_wf_typ_d_wf_typ : core.

Open Scope dworklist_scope.

Theorem a_wl_red_soundness: forall Γ,
  ⊢ᵃʷ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto.
  intros * Hwfa Hared. dependent induction Hared; auto; unfold transfer in *;
    try _apply_IH_a_wl_red; try destruct_trans; try trans_all_typ; try rename_typ.
  - exists dworklist_empty. intuition...
  - exists (dworklist_consvar Ω x (dbind_typ Aᵈ))...
  - exists (dworklist_constvar Ω X dbind_tvar_empty)...
    split... exists ((X, dbind_tvar_empty) :: θ)...
    constructor... admit.
  - exists (dworklist_constvar Ω X dbind_stvar_empty)...
    split... exists ((X, dbind_stvar_empty) :: θ)...
    constructor... admit.
  - exists Ω.
    split... exists ((X, dbind_typ typ_unit) :: θ)...
    constructor... admit.
  - exists (dworklist_conswork Ω (work_sub B1ᵈ typ_top)); split...
  - exists (dworklist_conswork Ω (work_sub typ_bot Aᵈ)); split... 
  - exists (dworklist_conswork Ω (work_sub typ_unit typ_unit)).
    split... exists θ... 
  - clear H0. dependent destruction H.
    + exists (dworklist_conswork Ω (work_sub ` X ` X)). split.
      * exists θ... 
        eapply trans_wl_a_wl_binds_tvar_ss in H; eauto...
      * eapply trans_wl_a_wl_binds_tvar_d_wl in H...
    + exists (dworklist_conswork Ω (work_sub ` X ` X)). split.
      * exists θ... 
        eapply trans_wl_a_wl_binds_stvar_ss in H...
      * eapply trans_wl_a_wl_binds_stvar_d_wl in H... 
    + assert (Hbinds: exists Tᵈ, binds X (dbind_typ Tᵈ) θ) by admit.
      destruct Hbinds as [Tᵈ Hbinds].
      exists (dworklist_conswork Ω (work_sub Tᵈ Tᵈ)). split.
      * exists θ. constructor...
      * constructor... apply dsub_refl...
  - exists ((work_sub (typ_arrow B1ᵈ B2ᵈ) (typ_arrow A1ᵈ A2ᵈ) ⫤ᵈ Ω)).
    split. exists θ. auto...
    econstructor.
    econstructor.
    + apply d_wl_red_weaken_work1 in Hdred. dependent destruction Hdred...
    + apply d_wl_red_weaken_work2 in Hdred. dependent destruction Hdred...
    + dependent destruction Hdred. dependent destruction Hdred...
  (* forall x. A < B  *)
  - inst_cofinites_by (L `union` ftvar_in_typ A1 `union` ftvar_in_typ B1) using_name X.
    assert ( ⊢ᵃʷ (work_sub (B1 ^ᵗ X) A1 ⫤ᵃ aworklist_constvar Γ X abind_etvar_empty)) by admit.
    destruct_a_wf_wl.
    _apply_IH_a_wl_red.
    destruct_trans.
    rename Aᵈ into B1tᵈ. rename Bᵈ into A1ᵈ.
    apply trans_typ_etvar_tvar_subst_cons in H13...
    destruct H13 as [B1xᵈ [Hsubst Htransa]].
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) A1ᵈ ⫤ᵈ Ω).
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all. intros.
        solve_trans_typ_open_close.
      * admit. (* trans_typ_strengthen *)
    + econstructor. 
      eapply d_sub__alll with (T:=T) (L:=L)...
      * intros. inst_cofinites_with X0.
        rewrite_close_open_subst.
        admit. (* *, s_in *)
      * admit. (* *, mono *)
      * rewrite_close_open_subst.
        rewrite Hsubst.
        dependent destruction Hdred...
      * dependent destruction Hdred...
  - destruct_a_wf_wl.
    dependent destruction H. dependent destruction H1.
    inst_cofinites_by (L `union` L0 `union` L1 `union` dom (awl_to_aenv Γ)) using_name X.
    assert ( ⊢ᵃʷ (work_sub (B1 ^ᵗ X) (A1 ^ᵗ X) ⫤ᵃ aworklist_constvar Γ X abind_stvar_empty) ) by admit.
    _apply_IH_a_wl_red.
    destruct_trans...
    rename Aᵈ into B1xᵈ. rename Bᵈ into A1xᵈ.
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) (typ_all (close_typ_wrt_typ X A1xᵈ)) ⫤ᵈ Ω).
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all. intros.
        rewrite_close_open_subst.
        admit. (* *, trans_typ_rename *)
      * inst_cofinites_for trans_typ__all. intros.
        rewrite_close_open_subst.
        admit. (* *, trans_typ_rename *)
    + dependent destruction Hdred. 
      econstructor...
      inst_cofinites_for d_sub__all; intros.
      * rewrite_close_open_subst.
        admit. (* *, s_in *)
      * rewrite_close_open_subst.
        admit. (* *, s_in *)
      * repeat rewrite_close_open_subst.
        admit. (* *, sub_rename *)
      * dependent destruction Hdred...
  (* ^X < A1 -> A2 *)
  - inst_cofinites_by (L `union` singleton X `union`  dom (awl_to_aenv Γ)) using_name X1.
    inst_cofinites_by (L `union` singleton X1 `union` singleton X `union` dom (awl_to_aenv Γ)) using_name X2.
    assert (Hws: exists Γ1 Γ2, 
      aworklist_subst (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
        (typ_arrow ` X1 ` X2) Γ1 Γ2). {
      eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
      destruct H as [Γ1 [Γ2 Hws]].
      exists Γ1, (work_sub `X (typ_arrow A1 A2) ⫤ᵃ Γ2).
      econstructor. auto.
      destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H3 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: binds X1 (dbind_typ T0)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      assert (Hbindsx2: binds X2 (dbind_typ T)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      apply trans_typ_binds_etvar in Hbindsx1...
      apply trans_typ_binds_etvar in Hbindsx2...
      apply trans_typ_binds_etvar in Hbindsx as Htransx3...
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_sub (typ_arrow T0 T) (typ_arrow A1ᵈ A2ᵈ))). split.
      * exists θ'. econstructor...
        constructor. 
        -- apply trans_typ_binds_etvar; eauto.
           destruct_binds. destruct_in...
        -- constructor. rewrite_env (nil ++ θ'). 
           eapply trans_typ_strengthen_etvar with (X:=X1) (T:=T0).
           eapply trans_typ_strengthen_etvar with (X:=X2) (T:=T). auto...
           admit. (* *, notin *)
           admit. (* *, notin *)
           admit. (* *, binds X *)
      * auto.
      * admit. (* *, wf *)
      * admit. (* *, mono *)
    + admit. (* *, wf *)
  (* A1 -> A2 < ^X  *)
  - pick fresh X1. pick fresh X2.
    assert (Hws: exists Γ1 Γ2, 
      aworklist_subst (work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
        (typ_arrow ` X1 ` X2) Γ1 Γ2). {
      eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
      destruct H as [Γ1 [Γ2 Hws]].
      exists Γ1, (work_sub (typ_arrow A1 A2) `X ⫤ᵃ Γ2).
      econstructor. auto.
      destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]]...
    apply H3 in Hsubst as Hwsred...
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ⫦ᵗ `X1 ⇝ T0 ) by eauto.
      assert (Hbindsx2: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ⫦ᵗ `X2 ⇝ T ) by eauto.
      apply trans_typ_binds_etvar in Hbindsx as Htransx3...
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_sub(typ_arrow A1ᵈ A2ᵈ) (typ_arrow T0 T) )). split.
      * exists θ'. econstructor...
        constructor.
        -- constructor. 
           ++ eapply trans_typ_strengthen_cons... 
              eapply trans_typ_strengthen_cons...
           ++ eapply trans_typ_strengthen_cons... 
              eapply trans_typ_strengthen_cons...
        -- apply trans_typ_binds_etvar; eauto.
           destruct_binds. destruct_in...
      * auto.
      * admit. (* *, wf *)
      * simpl... constructor...
    + auto. admit. (* *, wf *)
    (* τ < ^X *)
  - destruct_a_wf_wl. 
    apply a_worklist_subst_wf_wl in H4 as Hwf... 
    _apply_IH_a_wl_red. 
    eapply a_worklist_subst_transfer_same_dworklist in H4 as Hws; eauto.
    destruct Hws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ᵈ Ω). split.
    + exists θ'1.
      constructor...
    + econstructor...
      apply dsub_refl...
  (* ^X < τ *)
  - destruct_a_wf_wl. 
    apply a_worklist_subst_wf_wl in H4 as Hwf... 
    _apply_IH_a_wl_red.
    eapply a_worklist_subst_transfer_same_dworklist in H4 as Hws; eauto.
    destruct Hws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ᵈ Ω). split.
    + exists θ'1.
      constructor...
    + econstructor...
      apply dsub_refl...
  (* A < B1 /\ B2 *)
  - exists (work_sub A1ᵈ (typ_intersection B1ᵈ B2ᵈ) ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* A1 /\ A2 < B *)
  - exists (work_sub (typ_intersection B1ᵈ B2ᵈ) A1ᵈ ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* A1 /\ A2 < B *)
  - exists (work_sub (typ_intersection B1ᵈ B2ᵈ) A1ᵈ ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* A < B1 \/ B2 *)
  - exists (work_sub B1ᵈ (typ_union A1ᵈ A2ᵈ) ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* A < B1 \/ B2 *)
  - exists (work_sub B1ᵈ (typ_union A1ᵈ A2ᵈ) ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* A1 \/ A2 < B *)
  - exists (work_sub (typ_union B1ᵈ B2ᵈ) A1ᵈ ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* e <= A *)
  - exists (work_check eᵈ A1ᵈ ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  (* \ x. e <= A1 -> A2 *)
  - destruct_a_wf_wl. inst_cofinites_by (L `union` L0)... 
    assert (⊢ᵃʷ (work_check (open_exp_wrt_exp e (exp_var_f x)) A2 ⫤ᵃ (aworklist_consvar Γ x (abind_var_typ A1)))) by admit.
    apply H2 in H3.
    destruct H3 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans. rename_typ.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) (typ_arrow A1ᵈ A2ᵈ) ⫤ᵈ Ω). split.
    + exists θ.
      econstructor...
      econstructor...
      eapply trans_exp__abs with (L:=fvar_in_exp e). intros.
      rewrite_close_open_subst.
      admit. (* *, trans rename *)
    + destruct_d_wl_del_red.
      econstructor; auto.
      inst_cofinites_for d_chk_inf__chk_abs; auto.
      * admit. (* *, wf *)
      * intros. rewrite_close_open_subst.
        apply d_chk_inf_rename_var_cons...
  (* \ x. e <= ^X *)
  - pick fresh x.
    pick fresh X1. pick fresh X2.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.  
    assert (Hws: exists Γ1 Γ2, aworklist_subst 
       (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
       (typ_arrow ` X1 ` X2) Γ1 Γ2). {
       eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
       destruct H as [Γ1 [Γ2 Hws]].
       exists Γ1, (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1 ;ᵃ Γ2)...
       destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H1 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ⫦ᵗ `X1 ⇝ T0 ) by eauto.
      assert (Hbindsx2: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ⫦ᵗ `X2 ⇝ T ) by eauto.
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) (typ_arrow T0 T)))... split.
      * exists θ'... constructor; auto.
        constructor.
        -- inst_cofinites_for trans_exp__abs. intros.
           rewrite_close_open_subst.
           admit. (* Ok, trans rename *)
        -- apply trans_typ_binds_etvar; auto...
           destruct_binds. destruct_in...
      * constructor; auto.
         admit. 
         destruct_d_wl_del_red...
      * admit. (* *, wf *)
      * admit. (* mono *)   
    + admit. (* *, wf *)
  (* \ x. e <= ⊤ *)
  - destruct_a_wf_wl. inst_cofinites_by (L `union` L0).
    assert ( ⊢ᵃʷ (work_check (e ^ᵉₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ)) by admit.
    apply H3 in H4. 
    destruct H4 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ].
    destruct_trans.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) typ_top ⫤ᵈ Ω). split.
    + exists θ. 
      econstructor...
      econstructor...
      inst_cofinites_for trans_exp__abs. intros.
      rewrite_close_open_subst.
      admit. (* *, inf rename *)
    + destruct_d_wl_del_red...
      econstructor; auto.
      inst_cofinites_for d_chk_inf__chk_abstop. intros.
      rewrite_close_open_subst.
      admit. (* *, chk rename h*)
  (* e <= A1 /\ A2 *)
  - exists (work_check eᵈ (typ_intersection A1ᵈ A2ᵈ) ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
  (* e <= A1 \/ A2 *)
  - exists (work_check eᵈ (typ_union A1ᵈ A2ᵈ) ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
  (* e <= A1 \/ A2 *)
  - exists (work_check eᵈ (typ_union A1ᵈ A2ᵈ) ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
  (* x => _ *)
  - destruct_a_wf_wl.
    apply binds_unique with (a:=abind_var_typ A0) in H; auto.
    dependent destruction H; subst.
    assert (⊢ᵃʷ (work_applys cs A ⫤ᵃ Γ)). econstructor... econstructor...
    admit. (* *, wf *)
    apply IHHared in H as IH. destruct IH as [Ω [[θ Htrans] Hdred]].
    destruct_trans. rename_typ.
    exists (work_infer (exp_var_f x) csᵈ ⫤ᵈ Ω).
    split... econstructor... econstructor...
    eapply trans_wl_a_wl_binds_var_trans_typ_d_wl in H1...
  (* e : A => _ *)
  - exists (work_infer (exp_anno eᵈ Aᵈ) csᵈ ⫤ᵈ Ω)...
    split. exists θ...
    destruct_d_wl_del_red.
    econstructor...
  (* /\ a. e : A => _ *)
  - destruct_a_wf_wl. 
    pick fresh X. inst_cofinites_with X.
    assert (Hwf: ⊢ᵃʷ (work_check (e ^ᵉₜ ` X) (A ^ᵗ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    dependent destruction H9.
    (*  *)
    exists (work_infer (exp_tabs (body_anno (close_exp_wrt_typ X eᵈ) (close_typ_wrt_typ X Aᵈ0))) csᵈ ⫤ᵈ Ω). split.
    + exists θ...
      econstructor...
      econstructor...
      inst_cofinites_for trans_exp__tabs.
      intros. simpl. repeat rewrite open_body_wrt_typ_anno. 
      constructor.
      -- rewrite_close_open_subst.
         apply trans_exp_rename_tvar_cons with (X':=X0) in H12; eauto.          
          admit. (* *, inf rename *)
      -- solve_trans_typ_open_close.
    + assert (θ ⫦ᵗ typ_all A ⇝ typ_all A1ᵈ). {
        inst_cofinites_for trans_typ__all. intros.
        inst_cofinites_with X0. auto.
      }
      assert (θ ⫦ᵗ typ_all A ⇝ typ_all (close_typ_wrt_typ X Aᵈ0)). {
        inst_cofinites_for trans_typ__all. intros.
        solve_trans_typ_open_close.
      }
      unify_trans_typ. inversion H15. subst.
      apply d_wl_del_red__inf with (A:=typ_all (close_typ_wrt_typ X Aᵈ0)).
      * inst_cofinites_for  d_chk_inf__inf_tabs. 
        admit. (* *, wf *)
        intros. inst_cofinites_with X0. rewrite_close_open_subst.
        rewrite_close_open_subst. admit. (* *, chk rename *)
      * destruct_d_wl_del_red...
  (* \x. e => _ *)
  - destruct_a_wf_wl.
    pick fresh x. pick fresh X1. pick fresh X2.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    assert (Hwf: ⊢ᵃʷ (work_check (e ^ᵉₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1;ᵃ work_applys cs (typ_arrow ` X1 ` X2)
            ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)) by admit.
    apply H3 in Hwf.
    destruct Hwf as [Ω [[θ Htrans] Hdred]].
    destruct_trans. unify_trans_typ.
    exists (work_infer (exp_abs (close_exp_wrt_exp x eᵈ)) csᵈ ⫤ᵈ Ω).
    split.
    + exists θ'...
      econstructor...
      econstructor...
      * admit. (* trans_typ *)
      * admit. (* trans_cont_strengthen *)
    + eapply d_wl_del_red__inf with (A:=typ_arrow A1ᵈ Aᵈ0). 
      * assert (Hbindsx1: ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ') ⫦ᵗ `X1 ⇝ T1 ) by eauto.
        assert (Hbindsx2: ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ') ⫦ᵗ `X2 ⇝ T0 ) by eauto.
        repeat unify_trans_typ.
        destruct_d_wl_del_red... simpl in *...
        inst_cofinites_for d_chk_inf__inf_abs_mono; auto.
        admit. (* *, mono *)
        intros. rewrite_close_open_subst; auto. admit. (* **, chk rename *)
      * destruct_d_wl_del_red...
  (* () => _ *)
  - exists (work_infer exp_unit csᵈ ⫤ᵈ Ω)...
    split. exists θ... 
    econstructor...
  (* e1 e2 => _ *)
  - exists (work_infer (exp_app eᵈ eᵈ0) csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
    eapply d_wl_del_red__inf with (A:=B)...
    econstructor...
      apply d_wl_red_weaken_work1 in Hdred. dependent destruction Hdred...
    apply d_wl_red_weaken_work2 in Hdred...
  - exists (work_infapp Aᵈ Bᵈ eᵈ csᵈ ⫤ᵈ Ω)...
    split. destruct_d_wl_del_red. exists θ...
    econstructor...
  - exists (work_infabs (typ_arrow Aᵈ Bᵈ) cdᵈ ⫤ᵈ Ω)...
    split. destruct_d_wl_del_red. exists θ... 
    econstructor... 
  - exists (work_infabs typ_bot cdᵈ ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
    dependent destruction H5...
  (* ∀ a. A ▹ _ *)
  - destruct_a_wf_wl. 
    dependent destruction H.
    inst_cofinites_by (L `union` L0 `union` ftvar_in_typ A) using_name X.
    assert (⊢ᵃʷ (work_infabs (A ^ᵗ X) cd ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    eapply trans_typ_etvar_tvar_subst_cons in H11...
    destruct H11 as [Axᵈ [Hsubst Htransa]].
    exists (work_infabs (typ_all (close_typ_wrt_typ X Axᵈ)) cdᵈ ⫤ᵈ Ω). split.
    exists θ'.
    + constructor...
      constructor...
      * inst_cofinites_for trans_typ__all.
        intros.
        solve_trans_typ_open_close.
      * admit. (* *, trans_cont_strengthen *)
    + dependent destruction Hdred.  
      eapply d_wl_del_red__infabs with (B:=B) (C:=C); auto.
      eapply d_infabs__all with (T:=T)...
      * admit. (* *, mono *)
      * admit. (* *, wf *)
      * admit. (* *, wf *)
      * rewrite_close_open_subst. rewrite Hsubst...
  - exists (work_infabs (typ_intersection A1ᵈ A2ᵈ) cdᵈ ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
  - exists (work_infabs (typ_intersection A1ᵈ A2ᵈ) cdᵈ ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
  - exists (work_infabs (typ_union A1ᵈ A2ᵈ) cdᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_infabsunion B1ᵈ C1ᵈ A2ᵈ cdᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_unioninfabs B1ᵈ C1ᵈ B2ᵈ C2ᵈ cdᵈ ⫤ᵈ Ω).
    split...
  (* ^X ▹ _ *)
  - pick fresh X1. pick fresh X2.
    inst_cofinites_with X1. inst_cofinites_with X2.
    assert (Hws: exists Γ1 Γ2, aworklist_subst 
      (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
      (typ_arrow ` X1 ` X2) Γ1 Γ2). {
      eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
      destruct H as [Γ1 [Γ2 Hws]].
      exists Γ1, (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ Γ2).
      econstructor. 
      auto.
      destruct_a_wf_wl; auto.
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H1 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply a_worklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ⫦ᵗ `X1 ⇝ T0 ) by eauto.
      assert (Hbindsx2: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ⫦ᵗ `X2 ⇝ T ) by eauto.
      repeat unify_trans_typ.
      exists (dworklist_conswork Ω (work_infabs (typ_arrow T0 T) cdᵈ)). split.
      * exists θ'. constructor; auto.
        constructor.
        -- apply trans_typ_binds_etvar...
           destruct_binds. destruct_in...
        -- admit. (* trans_cont_stengthen *)
      * destruct_d_wl_del_red...       
      * destruct_a_wf_wl... 
        admit.  (* *, wf *)
      * simpl. auto.
    + admit. (* *, wf *)
  - exists (work_infer (exp_tapp eᵈ Bᵈ) cᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  (* ∀ a. A ∘ B =>=> _ *)
  - assert (⊢ᵃʷ (work_applys cs (A ^^ᵗ B) ⫤ᵃ Γ)) by admit.
    _apply_IH_a_wl_red.
    destruct_trans.
    inst_cofinites_by (dom (awl_to_aenv Γ) `union` dom θ `union` ftvar_in_typ A) using_name X.
    trans_all_typ.
    erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H6; eauto.
    eapply trans_typ_subst_tvar_cons in H6...
    destruct H6 as [Axᵈ [Hsubst Htransa]].
    exists (work_inftapp (typ_all (close_typ_wrt_typ X Axᵈ)) Bᵈ csᵈ ⫤ᵈ Ω).
    split.
    + exists θ.
      econstructor...
      econstructor...
      inst_cofinites_for trans_typ__all. intros.
      solve_trans_typ_open_close.
    + eapply d_wl_del_red__inftapp with (C:=open_typ_wrt_typ (close_typ_wrt_typ X Axᵈ) Bᵈ)...
      econstructor; auto.
      * admit. (* *, wf *)
      * admit. (* *, wf *)
      * admit. (* *, wf *)
      * rewrite_close_open_subst. rewrite Hsubst...
    + eapply lc_typ_subst_inv with (X:=X) (T:=B)...
  - exists (work_inftapp typ_bot Bᵈ csᵈ ⫤ᵈ Ω).
    split...
  - exists (work_inftapp (typ_intersection A1ᵈ A2ᵈ) Bᵈ csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_inftapp (typ_intersection A1ᵈ A2ᵈ) Bᵈ csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_inftapp (typ_union A1ᵈ A2ᵈ) Bᵈ cᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_inftappunion C1ᵈ A2ᵈ Bᵈ cᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_unioninftapp C1ᵈ C2ᵈ csᵈ ⫤ᵈ Ω).
    split...
  - destruct_a_wf_wl.
    eapply a_wf_work_apply_conts in H1 as Hwf...
    assert ( ⊢ᵃʷ (w ⫤ᵃ Γ) ) by auto.
    apply IHHared in H2...
    destruct H2 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    trans_all_typ.
    assert (exists csᵈ, θ' ⫦ᶜˢ cs ⇝ csᵈ) by admit. (* *, trans cont total *)
    destruct H4 as [csᵈ Htransc].
    exists (work_applys csᵈ Aᵈ ⫤ᵈ Ω). split.
    exists θ'. econstructor...
    eapply trans_apply_conts in H2; eauto.
  - destruct_a_wf_wl.
    eapply a_wf_work_apply_contd with (A:=A) (B:=B) in H1 as Hwf...
    assert ( ⊢ᵃʷ (w ⫤ᵃ Γ) ) by auto.
    apply IHHared in H3...
    destruct H3 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    trans_all_typ.
    assert (exists cdᵈ, θ' ⫦ᶜᵈ cd ⇝ cdᵈ) by admit. (* *, trans cont total *)
    destruct H6 as [cdᵈ Htransc].
    exists (work_applyd cdᵈ Aᵈ Bᵈ ⫤ᵈ Ω). split.
    exists θ'. econstructor...
    eapply trans_apply_contd in H2; eauto.
Admitted.
