Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni_monoiu.notations.
Require Import uni_monoiu.decl.prop_basic.
Require Import uni_monoiu.decl.prop_subtyping.
Require Import uni_monoiu.decl.prop_typing.
Require Import uni_monoiu.decl.prop_rename.
Require Import uni_monoiu.decl_worklist.prop_equiv.
Require Import uni_monoiu.algo_worklist.def_extra.
Require Import uni_monoiu.algo_worklist.prop_basic.
Require Import uni_monoiu.algo_worklist.transfer.
Require Import uni_monoiu.ltac_utils.  

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
    | H : trans_typ ?θ (open_typ_wrt_typ ?Aᵃ (typ_var_f ?X)) ?Aᵈ |- _ => 
      let A1ᵃ1 := fresh Aᵃ"xᵈ" in 
      rename Aᵈ into A1ᵃ1;
      generalize dependent H
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
Ltac destruct_trans' :=
  lazymatch goal with
    | H : trans_worklist ?θ (aworklist_cons_work ?Γ ?w) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_worklist ?θ (aworklist_cons_var ?Γ ?x ?b) ?Ω ?θ' |- _ => dependent destruction H
    | H : trans_work ?θ (subst_typ_in_work _ _ _) ?wᵈ |- _ => fail
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
    | H : trans_typ ?θ (subst_typ_in_typ _ _ _) ?Aᵈ |- _ => fail
    | H : trans_typ ?θ (?C_T _ _) ?Aᵈ |- _ => dependent destruction H
    end;
  try unify_trans_typ;
  try unify_trans_exp.

Ltac destruct_trans :=
  repeat destruct_trans'.

Theorem a_mono_typ_wf : forall Σ A,
  a_mono_typ Σ A -> a_wf_typ Σ A.
Proof.
  intros. induction H; auto.
Qed.

#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp : core.
#[local] Hint Resolve a_mono_typ_wf : core.
#[local] Hint Resolve wf_ss_weaken_tvar wf_ss_weaken_stvar wf_ss_weaken_etvar : core.

(* assert the well-formedness and apply the induction hypothesis  *)

Ltac solve_a_wf_wl Γ :=
  lazymatch goal with 
  | H : ⊢ᵃʷₛ Γ |- _ => idtac
  | _ : _ |- _ =>   
    destruct_a_wf_wl; 
    let H1 := fresh "H" in
    assert (H1 : ⊢ᵃʷₛ Γ) by eauto 7
  end.

Ltac _apply_IH_a_wl_red :=
  match goal with 
  | H : (⊢ᵃʷₛ ?Γ) -> ?P |- _ => 
    solve_a_wf_wl Γ
  end;
  match goal with
  | H : (⊢ᵃʷₛ ?Γ) -> ?P, H1 : ⊢ᵃʷₛ ?Γ |- _ => 
    let Hdred := fresh "IHHdred" in
    apply H in H1 as Hdred;
    destruct Hdred as [Ω [Htrans Hdred]];
    destruct Htrans as [θ Htrans]
  end.

Ltac trans_all_typ :=
  match goal with 
  | H5 : nil ⊩ ?Γ ⇝ ?Ω ⫣ ?θ |- _ => 
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
  X ∉ dom (θ2 ++ θ1) ->
  θ1 ᵗ⊩ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ᵗ⊩ {Bᵃ ᵗ/ₜ X} Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {Bᵈ ᵗ/ₜ X} Aᵈ = A'ᵈ /\ θ2 ++ (X, dbind_tvar_empty) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
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
      * apply subst_typ_in_typ_fresh_eq...
      * rewrite_env (θ2 ++ (X0 ~ □) ++ θ1). apply trans_typ_weaken... 
        apply wf_ss_weaken_tvar...
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ]. 
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ]. 
    exists (typ_arrow A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
  - dependent destruction Hinst.  
    pick fresh X0. inst_cofinites_with X0.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in *...
    rewrite_env (((X0, dbind_tvar_empty) :: θ2) ++ θ1) in H2.
    apply H0 in H2; simpl...
    destruct H2 as [Aᵈ].
    exists (typ_all (close_typ_wrt_typ X0 Aᵈ)). simpl.
    rewrite subst_typ_in_typ_close_typ_wrt_typ... 
    split...
    + apply f_equal. erewrite typ_open_r_close_l... intuition.
    + eapply trans_typ__all with (L:=L `union` dom (θ2 ++ (X, □) :: θ1)); intros.
      * eapply s_in_subst in H1... apply s_in_rename with (Y:=X1) in H1.
        rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in *...
      * intuition.
      erewrite subst_typ_in_typ_intro by auto.
      erewrite (subst_typ_in_typ_intro X0 (close_typ_wrt_typ X0 Aᵈ)) by apply close_typ_wrt_typ_notin.
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
  - dependent destruction Hinst. exists (typ_label l); split...
Qed.

Lemma trans_typ_subst_tvar_cons : forall θ Bᵃ Bᵈ X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X ∉ dom θ ->
  θ ᵗ⊩ Bᵃ ⇝ Bᵈ ->
  θ ᵗ⊩ {Bᵃ ᵗ/ₜ X} Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {Bᵈ ᵗ/ₜ X} Aᵈ = A'ᵈ /\ (X, dbind_tvar_empty) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  rewrite_env (nil ++ θ) in H2.
  eapply trans_typ_subst_tvar in H2...
Qed.

Lemma trans_typ_subst_etvar : forall θ1 θ2 Tᵃ Tᵈ X Aᵃ Aᵈ,
  lc_typ Aᵃ -> 
  wf_ss (θ2 ++ θ1) ->
  X ∉ dom (θ2 ++ θ1) ->
  ss_to_denv θ1 ᵗ⊢ᵈₘ Tᵈ ->
  θ2 ++ θ1 ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ2 ++ θ1 ᵗ⊩ {Tᵃ ᵗ/ₜ X} Aᵃ ⇝ Aᵈ -> 
  θ2 ++ X ~ dbind_typ Tᵈ ++ θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
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
    inst_cofinites_for trans_typ__all; intros;
    inst_cofinites_with X0. rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in *; eauto.
    + apply s_in_subst in H1; eauto. 
    + rewrite_env (((X0, □) :: θ2) ++ (X, dbind_typ Tᵈ) :: θ1).
      apply H0; auto.
      * simpl. constructor; auto.
      * simpl. rewrite_env (nil ++ (X0 ~ □) ++ (θ2 ++ θ1)). 
        apply trans_typ_weaken; auto.
        constructor; auto.
      * rewrite subst_typ_in_typ_open_typ_wrt_typ.
        -- simpl. destruct_eq_atom. auto.
        -- eapply trans_typ_lc_atyp; eauto.
  - simpl in Hinsta.
    dependent destruction Hinsta. constructor; auto.
  - simpl in Hinsta.
    dependent destruction Hinsta. constructor; auto.
  - dependent destruction Hinsta. constructor; auto.
Qed.

Lemma trans_typ_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X Aᵃ Aᵈ,
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᵗ⊩ {Tᵃ ᵗ/ₜ X} Aᵃ ⇝ Aᵈ -> 
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof.
  intros.
  apply ls_binds_split in H0 as Hsplit.
  destruct Hsplit as [θ2 [θ1 Heq]]. subst.
  apply trans_typ_strengthen_etvar in H2; auto.
  apply trans_typ_strengthen_etvar in H3; auto.
  eapply trans_typ_subst_etvar; eauto.
  - apply lc_typ_subst_inv with (B:=Tᵃ) (X:=X).
    eapply trans_typ_lc_atyp; eauto.
    eapply trans_typ_lc_atyp; eauto.
  - eapply wf_ss_notin_remaining; eauto. 
  - clear H0 H1 H2 H3. induction θ2; simpl in *. 
    + inversion H; auto.
    + inversion H; apply IHθ2; eauto.
  - apply subst_typ_in_typ_fresh_same; auto.
Qed.

Lemma trans_exp_subst_etvar_same_ss' : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᵉ⊩ (subst_typ_in_exp Tᵃ X eᵃ) ⇝ eᵈ -> 
  θ ᵉ⊩ eᵃ ⇝ eᵈ.
Proof.
  intros * Hlc.
  generalize dependent θ. generalize dependent eᵈ.
  induction Hlc; simpl in *; intros.
  - dependent destruction H3; constructor; auto.
  - dependent destruction H3; constructor; auto.
  - dependent destruction H5.
    inst_cofinites_for trans_exp__abs. intros.
    apply H0; auto.
    rewrite subst_typ_in_exp_open_exp_wrt_exp.
    simpl. auto.
  - dependent destruction H3; eauto.
  - dependent destruction H5; eauto.
    destruct e; simpl in x; try solve [inversion x].
    inst_cofinites_for trans_exp__tabs; intros; inst_cofinites_with X0.
    + dependent destruction x. 
      assert (Htrans: (X0, □) :: θ ᵉ⊩ {Tᵃ ᵉ/ₜ X} exp_anno e A ᵉ^^ₜ ` X0 ⇝ exp_anno (eᵈ ᵉ^^ₜ ` X0) (Aᵈ ᵗ^ₜ X0)). {
        simpl. constructor. rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2 in H5; eauto.
        rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H6; eauto.
      }
      apply H0 in Htrans; eauto.
      * dependent destruction Htrans; eauto.
      * apply trans_typ_weaken_cons; eauto.
    + dependent destruction x.
      assert (Htrans: (X0, □) :: θ ᵉ⊩ {Tᵃ ᵉ/ₜ X} exp_anno e A ᵉ^^ₜ ` X0 ⇝ exp_anno (eᵈ ᵉ^^ₜ ` X0) (Aᵈ ᵗ^ₜ X0)). {
        simpl. constructor. rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2 in H5; eauto.
        rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H6; eauto.
      }
      apply H0 in Htrans; eauto.
      * dependent destruction Htrans; eauto.
      * apply trans_typ_weaken_cons; eauto.
  - dependent destruction H4.
    constructor.
    * apply IHHlc; eauto.
    * eapply trans_typ_subst_etvar_same_ss; eauto.
  - dependent destruction H4.
    constructor.
    * apply IHHlc; eauto.
    * eapply trans_typ_subst_etvar_same_ss; eauto.
  - dependent destruction H3. constructor; auto.
  - dependent destruction H3. constructor; auto.
  - dependent destruction H3. constructor; auto.
Qed.

Lemma trans_exp_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X eᵃ eᵈ,
  wf_ss θ ->
  binds X (dbind_typ Tᵈ) θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᵉ⊩ (subst_typ_in_exp Tᵃ X eᵃ) ⇝ eᵈ -> 
  θ ᵉ⊩ eᵃ ⇝ eᵈ.
Proof.
  intros.
  apply trans_exp_lc_aexp in H3 as Hlce.
  apply trans_typ_lc_atyp in H2 as Hlct.
  apply lc_exp_subst_typ_in_exp_inv in Hlce; auto.
  eapply trans_exp_subst_etvar_same_ss'; eauto. 
Qed.

Lemma trans_conts_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X csᵃ csᵈ,
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᶜˢ⊩ {Tᵃ ᶜˢ/ₜ X} csᵃ ⇝ csᵈ -> 
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ
with trans_contd_subst_etvar_same_ss : forall θ Tᵃ Tᵈ X cdᵃ cdᵈ,
  wf_ss θ ->
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ᶜᵈ⊩ {Tᵃ ᶜᵈ/ₜ X} cdᵃ ⇝ cdᵈ -> 
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ.
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
  X ~ Tᵈ ∈ᵈ θ ->
  X ∉ ftvar_in_typ Tᵃ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  θ ʷ⊩ {Tᵃ ʷ/ₜ X} wᵃ ⇝ wᵈ -> 
  θ ʷ⊩ wᵃ ⇝ wᵈ.
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
  X ∉ dom (θ2 ++ θ1) ->
  ss_to_denv θ1 ᵗ⊢ᵈₘ T ->
  θ2 ++ (X, dbind_typ T) :: θ1 ᵗ⊩ Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {T ᵗ/ₜ X} Aᵈ = A'ᵈ /\ θ2 ++ (X, dbind_tvar_empty) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
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
        -- rewrite subst_typ_in_typ_fresh_eq...
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
    rewrite_env (((X0, dbind_tvar_empty) :: θ2) ++ (X, dbind_typ T) :: θ1) in H2.
    apply H0 in H2...
    destruct H2 as [Aᵈ].
    exists (typ_all (close_typ_wrt_typ X0 Aᵈ)). simpl. 
    rewrite subst_typ_in_typ_close_typ_wrt_typ... 
    split.
    + apply f_equal. erewrite typ_open_r_close_l... intuition.
    + eapply trans_typ__all with (L:=L `union` (dom (θ2 ++ (X, □) :: θ1))); intros.
      * apply s_in_rename with (Y:=X1) in H1. rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H1...
      * intuition.
        erewrite subst_typ_in_typ_intro by auto.
        erewrite (subst_typ_in_typ_intro X0 (close_typ_wrt_typ X0 Aᵈ)) by apply close_typ_wrt_typ_notin.
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
  - dependent destruction Hinst. exists (typ_label l); split...
Qed.

Lemma trans_typ_etvar_tvar_subst_cons : forall θ1 T X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X ∉ dom θ1 ->
  ss_to_denv θ1 ᵗ⊢ᵈₘ T ->
  (X, dbind_typ T) :: θ1 ᵗ⊩ Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {T ᵗ/ₜ X} Aᵈ = A'ᵈ /\ (X, dbind_tvar_empty) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with auto. 
  intros. 
  rewrite_env (nil ++ (X, □) :: θ1).  
  apply trans_typ_etvar_tvar_subst...
Qed.

#[local] Hint Immediate trans_wl_wf_ss : core.

Lemma tvar_notin_dom_neq_tvar_in_ss_wf_typ : forall θ T X Y,
  ss_to_denv θ ᵗ⊢ᵈₘ T ->
  X `in` ftvar_in_typ T ->
  Y ∉ dom θ ->
  X <> Y.
Proof.
  intros. dependent induction H; simpl in *; try fsetdec. 
  - apply singleton_iff in H0. subst. 
    apply binds_ss_to_denv_binds_ss in H. unfold not. intros. subst.
    apply binds_dom_contradiction in H; auto.
  - simpl in *. apply union_iff in H1. inversion H1; eauto.
  - simpl in *. apply union_iff in H1. inversion H1; eauto.
  - simpl in *. apply union_iff in H1. inversion H1; eauto.
Qed.

Lemma wf_ss_move_etvar_before : forall θ1 θ2 X1 X2 T1 T2,
  wf_ss (θ2 ++ (X1, dbind_typ T1) :: (X2, dbind_typ T2) :: θ1) ->
  wf_ss ((X2, dbind_typ T2) :: θ2 ++ (X1, dbind_typ T1) :: θ1).
Proof.
  constructor; auto.
  - rewrite_env ((θ2 ++ (X1 ~ dbind_typ T1)) ++ (X2, dbind_typ T2) :: θ1) in H.  
    eapply wf_ss_strengthen_etvar with (X:=X2) in H. 
    rewrite_env ((θ2 ++ X1 ~ dbind_typ T1) ++ θ1). auto.
  - rewrite_env ((θ2 ++ (X1 ~ dbind_typ T1)) ++ (X2, dbind_typ T2) :: θ1) in H. 
    apply wf_ss_notin_remaining in H.
    rewrite_env ((θ2 ++ X1 ~ dbind_typ T1) ++ θ1). auto.
  - apply wf_ss_strengthen_app in H. simpl in *. 
    dependent destruction H. dependent destruction H. simpl in *.
    rewrite ss_to_denv_app. apply d_mono_typ_weaken_app. simpl. auto.
Qed.

Lemma a_mono_typ_move_etvar_back : forall Γ1 Γ2 A X Y ,  
  ⌊ Y ~ᵃ ⬒;ᵃ Γ2 ⧺ X ~ᵃ ⬒;ᵃ Γ1 ⌋ᵃ ᵗ⊢ᵃₘ A ->
  ⌊ Γ2 ⧺ X ~ᵃ ⬒;ᵃ Y ~ᵃ ⬒;ᵃ Γ1 ⌋ᵃ ᵗ⊢ᵃₘ A.
Proof.
  intros. dependent induction H; auto.
  - simpl in *. rewrite awl_to_aenv_app in *.
    destruct_binds. simpl in *. apply binds_app_iff in H1; destruct H1; auto.
    destruct_binds. eauto.
  - apply a_mono_typ__etvar. simpl in *. rewrite awl_to_aenv_app in *.
    destruct_binds. eauto.
    apply binds_app_iff in H1; destruct H1; auto.
    destruct_binds; eauto.
Qed.

Lemma aworklist_subst_transfer_same_dworklist': forall Γ Ω θ X T Γ1 Γ2,
  ⊢ᵃʷ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ T->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X ∉ ftvar_in_typ T ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  nil ⊩ {T ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⇝ Ω ⫣ θ ->
  exists θ' Tᵈ, 
      nil ⊩ Γ ⇝ Ω ⫣ θ' /\ 
      θ ᵗ⊩ T ⇝ Tᵈ /\ 
      θ' ᵗ⊩ T ⇝ Tᵈ /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      binds X (dbind_typ Tᵈ) θ' /\
      wf_ss θ'.
Proof with auto.
  intros. generalize dependent θ. generalize dependent Ω. dependent induction H3; intros.
  - simpl in *.
    apply a_mono_typ_strengthen_mtvar in H0...
    apply a_mono_typ_wf in H0 as Hwf.
    eapply trans_typ_total in Hwf; eauto.
    destruct Hwf as [Aᵈ].
    dependent destruction H.
    exists ((X ~ dbind_typ Aᵈ) ++ θ). 
    exists Aᵈ.
    assert (wf_ss ((X ~ dbind_typ Aᵈ) ++ θ)). { 
      constructor; eauto. 
       erewrite trans_wl_ss_dom_upper; eauto. 
      eapply trans_wl_a_mono_typ_d_mono_typ with (Tᵃ:=A); eauto.
    }
    dependent destruction H6.
    repeat split; auto.
    + econstructor; auto.  
    + apply trans_typ_weaken_cons...
    + intros. destruct_binds...
    + constructor...
  - simpl in *. destruct_trans. 
    apply IHaworklist_subst in H4 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].
    exists θ'1. exists Tᵈ. repeat (split; eauto).
    + constructor. auto.
      eapply trans_typ_subst_etvar_same_ss; eauto.
      eapply trans_typ_reorder_ss with (θ:=θ'); eauto.
      intros. apply Hbinds... 
      unfold not. intros. subst.
      apply subst_typ_in_typ_fresh_same in H6...
    + simpl in *. dependent destruction H... 
    + simpl in *. eapply a_mono_typ_strengthen_var; eauto. 
    + destruct_binds... 
    + auto.
  - dependent destruction H6.
    apply IHaworklist_subst in H6 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists ((Y , dbind_tvar_empty) :: θ'1), Tᵈ. repeat (split; auto).
    + econstructor; auto.
      eapply notin_dom_reorder; eauto.
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
    + simpl. constructor; eauto.
      eapply notin_dom_reorder...
    + simpl in *. dependent destruction H... 
    + simpl in *. 
      eapply a_mono_typ_strengthen_mtvar with (b:=abind_tvar_empty); eauto. 
    + destruct_binds...
    + auto.
  - simpl in *. destruct_trans. 
    apply IHaworklist_subst in H6 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists (Y ~ dbind_stvar_empty ++ θ'1), Tᵈ. repeat split; auto.
    + econstructor; auto. eapply notin_dom_reorder...
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
    + simpl in *. dependent destruction H... 
    + simpl in *. eapply a_mono_typ_strengthen_stvar; eauto...
    + destruct_binds... 
    + auto.
  (* work_stay *)
  - simpl in *. destruct_trans. 
    apply IHaworklist_subst in H4 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists θ'1. exists Tᵈ. repeat (split; auto).
    + constructor; auto.
      eapply trans_work_subst_etvar_same_ss; eauto.
      apply trans_work_reorder_ss with (θ:=θ'); eauto.
      * intros. apply Hbinds; auto.
        unfold not. intros. subst.
        apply subst_typ_in_work_fresh_same in H6; auto.
    + dependent destruction H... 
    + simpl in H0...
    + auto.
    + auto.
  - simpl in *. destruct_trans. 
    apply IHaworklist_subst in H6 as IH.
    destruct IH as [θ'1 [Tᵈ [Htrans [Htranst [Htranst' [Hbinds [Htransx Hwfss]]]]]]].    
    exists (Y ~ dbind_typ T ++ θ'1). exists Tᵈ.
    assert (ss_to_denv θ'1 ᵗ⊢ᵈₘ T). {
      apply d_mono_typ_reorder_ss with (θ:=θ'); eauto.
      intros. apply Hbinds; auto. apply neq_symm.
      eapply tvar_notin_dom_neq_tvar_in_ss_wf_typ with (X:=X0); eauto.
      rewrite trans_wl_ss_dom_upper; eauto.
      eapply aworklist_subst_remove_target_tvar with (Γ:=Γ); eauto...
      dependent destruction H... 
      dependent destruction H... destruct_binds... 
    }
    repeat split; auto.
    + econstructor; auto. 
      eapply notin_dom_reorder...
    + rewrite_env (nil ++ (Y ~ dbind_typ T) ++ θ'). apply trans_typ_weaken...
      constructor; auto.
      eapply trans_wl_wf_ss; eauto.
    + rewrite_env (nil ++ (Y ~ dbind_typ T) ++ θ'1). apply trans_typ_weaken...
      constructor; auto.
      eapply notin_dom_reorder...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + intros. destruct_binds... 
      * simpl. apply binds_cons... apply Hbinds...
    + constructor; auto. 
      eapply notin_dom_reorder...
    + simpl in *. dependent destruction H... 
    + simpl in *. eapply a_mono_typ_strengthen_mtvar; eauto. 
    + destruct_binds...
    + auto.
  - simpl in *. 
    apply IHaworklist_subst in H6 as IH.
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
      * rewrite_env ((X ~ dbind_typ T) ++ (Y, dbind_typ T0) :: θ') in Htrans2.
        rewrite_env ((θ'' ++ X ~ dbind_typ T) ++ (Y, dbind_typ T0) :: θ') in Htrans2.
        apply trans_wl_strengthen_etvar in Htrans2.
        -- subst.
           eapply trans_wl_app with (θ2:= X ~ dbind_typ T ++ θ'); eauto.
           constructor; eauto.
           rewrite_env ((θ'' ++ X ~ dbind_typ T) ++ θ'). auto.
        -- dependent destruction H. rewrite <- ftvar_in_a_wf_wwl_upper in H...
           rewrite ftvar_in_aworklist'_awl_app in H...
      * subst. rewrite_env ((θ'' ++ (X ~ dbind_typ T)) ++ (Y, dbind_typ T0) :: θ') in Hwfss. 
        apply wf_ss_notin_remaining in Hwfss...
      * rewrite ss_to_denv_app. simpl. apply d_mono_typ_weaken_app...
    + eapply trans_typ_reorder_ss with (θ:=θ'' ++ (X, dbind_typ T) :: (Y, dbind_typ T0) :: θ'); auto.
      * subst. apply wf_ss_move_etvar_before...
      * intros. apply binds_same_move_etvar_before...
    + intros. 
      apply binds_same_move_etvar_before...
      apply Hbinds...
    + intros. 
      apply Hbinds...
      apply binds_same_move_etvar_before...
    + subst. apply binds_same_move_etvar_before... 
    + apply wf_ss_move_etvar_before...
    + apply a_wf_wwl_move_etvar_back... 
    + apply a_mono_typ_move_etvar_back...
    + rewrite awl_to_aenv_app; simpl...
    + auto.
Qed.

Lemma aworklist_subst_transfer_same_dworklist: forall Γ Ω θ X T Γ1 Γ2,
  ⊢ᵃʷₛ Γ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ T->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X ∉ ftvar_in_typ T ->
  aworklist_subst Γ X T Γ1 Γ2 ->
  nil ⊩ {T ᵃʷ/ₜ X} Γ2 ⧺ Γ1 ⇝ Ω ⫣ θ ->
  exists θ' Tᵈ, 
      trans_worklist nil Γ Ω θ' /\ 
      θ ᵗ⊩ T ⇝ Tᵈ /\ 
      θ' ᵗ⊩ T ⇝ Tᵈ /\
      (forall Y b, X <> Y -> binds Y b θ <-> binds Y b θ') /\ 
      X ~ Tᵈ ∈ᵈ θ' /\
      wf_ss θ'.
Proof.
  intros. eapply aworklist_subst_transfer_same_dworklist'; eauto.
  apply a_wf_wl_a_wf_wwl. auto.
Qed.

Lemma trans_wl_a_wl_binds_var_trans_typ_d_wl : forall θ Γ Ω x Aᵃ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  x ~ Aᵃ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  x ~ Aᵈ ∈ᵈ dwl_to_denv Ω.
Proof.
  intros.
  eapply trans_wl_a_wl_binds_var_binds_d_wl_and_trans in H; eauto.
  destruct H as [Aᵈ' [Hbinds Htrans]].
  unify_trans_typ... auto.
Qed.
  
Ltac solve_notin_dom :=
  rewrite awl_to_aenv_app in *; rewrite dom_aenv_app_comm in *; simpl in *; auto.

Lemma worklist_subst_fresh_etvar_total : forall Γ1 Γ2 X X1 X2,
  uniq (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) ->
  X1 ∉ dom (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) ->
  X2 ∉ add X1 (dom (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ)) ->
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
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ aworklist_cons_var (Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) X ab) with 
      (X2 ~ᵃ ⬒ ;ᵃ (X1 ~ᵃ ⬒ ;ᵃ aworklist_cons_var Γ2 X ab) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1);
    constructor; simpl...
    replace (X1 ~ᵃ ⬒ ;ᵃ aworklist_cons_var (Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) X ab) with
      ((X1 ~ᵃ ⬒ ;ᵃ aworklist_cons_var Γ2 X ab) ⧺ X0 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1); 
    constructor; simpl...
    + dependent destruction H.
      eapply IHΓ2 with (X1:=X1) (X2:=X2) in H as Hws...
      dependent destruction Hws...
      * simpl in *. solve_notin_eq X2.
      * simpl in *. solve_notin_eq X2.
      * replace (X1 ~ᵃ ⬒ ;ᵃ Γ'2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) with 
        ((X1 ~ᵃ ⬒ ;ᵃ Γ'2) ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1) in x by auto.
        apply worklist_split_etvar_det in x; destruct x; subst. simpl in *.
        dependent destruction Hws; auto; simpl in *.
        -- solve_notin_eq X1.
        -- solve_notin_eq X1.
        -- replace (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) 
            with  (Γ'2 ⧺ X ~ᵃ ⬒ ;ᵃ (X2 ~ᵃ ⬒ ;ᵃ Γ1)) in x by auto.
            apply worklist_split_etvar_det in x; auto.
            destruct x; subst...
            destruct ab; auto.
            ++ constructor... rewrite awl_to_aenv_app in H0. 
               rewrite dom_app in H0... simpl in *. solve_notin. 
            ++ constructor... rewrite awl_to_aenv_app in H0. 
               rewrite dom_app in H0... simpl in *. solve_notin.
            ++ constructor... rewrite awl_to_aenv_app in H0. 
               rewrite dom_app in H0... simpl in *. solve_notin.
            ++ simpl. rewrite awl_to_aenv_app in H. simpl in H. 
               apply uniq_notin_remaining in H. solve_notin.  
        -- simpl. rewrite awl_to_aenv_app in *. rewrite dom_app in *. simpl in *. 
           apply uniq_notin_remaining in H. simpl. solve_notin. 
    + solve_notin_dom.
    + solve_notin_dom.
  - replace (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ w ⫤ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) with 
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
          simpl. rewrite awl_to_aenv_app in *. rewrite dom_app in *. simpl in *. 
           apply uniq_notin_remaining in H. simpl. solve_notin. 
       -- simpl. rewrite awl_to_aenv_app in *. rewrite dom_app in *. simpl in *. 
       apply uniq_notin_remaining in H. simpl. solve_notin. 
   + solve_notin_dom.
   + solve_notin_dom.
Qed.

Lemma worklist_subst_fresh_etvar_total' : forall Γ X X1 X2,
  uniq (⌊ Γ ⌋ᵃ) ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X1 ∉ dom (awl_to_aenv Γ) ->
  X2 ∉ add X1 (dom (awl_to_aenv Γ)) ->
  exists Γ1 Γ2, aworklist_subst (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
      (typ_arrow ` X1 ` X2) Γ1 Γ2.
Proof.
  intros. apply awl_split_etvar in H0.
  destruct H0 as [Γ1 [Γ2 Heq]].
  rewrite <- Heq in *.
  eapply worklist_subst_fresh_etvar_total in H; eauto.
Qed.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

#[local] Hint Resolve trans_wl_wf_ss trans_typ_wf_ss wf_ss_uniq : core.
#[local] Hint Resolve trans_typ_lc_atyp : core.

Lemma trans_apply_conts : forall θ csᵃ csᵈ Aᵃ Aᵈ wᵃ wᵈ,
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ ʷ⊩ wᵃ ⇝ wᵈ ->
  apply_conts csᵃ Aᵃ wᵃ ->
  apply_conts csᵈ Aᵈ wᵈ.
Proof.
  intros. dependent destruction H2; destruct_trans;
    try unify_trans_contd; try unify_trans_conts; 
    try repeat unify_trans_typ; try unify_trans_exp; try constructor.
Qed.

Lemma trans_apply_contd : forall θ cdᵃ cdᵈ Aᵃ Aᵈ Bᵃ Bᵈ wᵃ wᵈ,
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ ᵗ⊩ Bᵃ ⇝ Bᵈ ->
  θ ʷ⊩ wᵃ ⇝ wᵈ ->
  apply_contd cdᵃ Aᵃ Bᵃ wᵃ ->
  apply_contd cdᵈ Aᵈ Bᵈ wᵈ.
Proof with eauto.
Proof.
  intros. dependent destruction H3; destruct_trans;
    try unify_trans_contd; try unify_trans_conts; 
    try repeat unify_trans_typ; try unify_trans_exp; try constructor.
Qed.

#[local] Hint Resolve trans_typ_wf_ss trans_wl_a_wf_typ_d_wf_typ trans_wl_a_wf_twl_d_wf_twl d_wf_twl_wf_tenv : core.

#[local] Hint Resolve a_wf_wl_a_wf_bind_typ : core.

Open Scope dworklist_scope.

Theorem a_wl_red_soundness: forall Γ,
  ⊢ᵃʷₛ Γ -> Γ ⟶ᵃʷ⁎⋅ -> exists Ω, transfer Γ Ω /\ Ω ⟶ᵈ⁎⋅.
Proof with eauto.
  intros * Hwfa Hared. dependent induction Hared; auto; unfold transfer in *;
    try _apply_IH_a_wl_red; try destruct_trans; try trans_all_typ; try rename_typ.
  - exists dworklist_empty. intuition...
  - exists (dworklist_cons_var Ω X (dbind_typ Aᵈ))...
  - exists (dworklist_cons_var Ω X dbind_tvar_empty)...
    split... exists ((X, dbind_tvar_empty) :: θ)...
    constructor... rewrite trans_wl_ss_dom_upper; eauto.
  - exists Ω.
    split... exists ((X, dbind_typ typ_unit) :: θ)...
    constructor... rewrite trans_wl_ss_dom_upper; eauto.
  - exists (dworklist_cons_var Ω X dbind_stvar_empty)...
    split... exists ((X, dbind_stvar_empty) :: θ)...
    constructor... rewrite trans_wl_ss_dom_upper; eauto. 
  - exists Ω.
    split... exists ((X, dbind_typ typ_unit) :: θ)...
    constructor... rewrite trans_wl_ss_dom_upper; eauto.
  - exists (work_sub B1ᵈ typ_top ⫤ᵈ Ω); split...
  - exists (work_sub typ_bot Aᵈ ⫤ᵈ Ω); split... 
  - exists (work_sub typ_unit typ_unit ⫤ᵈ Ω).
    split... exists θ... 
  - exists (work_sub (typ_label l) (typ_label l) ⫤ᵈ Ω).
    split... exists θ... 
  - clear H0. dependent destruction H.
    + exists (work_sub ` X ` X ⫤ᵈ Ω). split.
      * exists θ... 
        eapply trans_wl_a_wl_binds_tvar_ss in H; eauto...
      * eapply trans_wl_a_wl_binds_tvar_d_wl in H...
    + exists (work_sub ` X ` X ⫤ᵈ Ω). split.
      * exists θ... 
        eapply trans_wl_a_wl_binds_stvar_ss in H...
      * eapply trans_wl_a_wl_binds_stvar_d_wl in H... 
    + eapply trans_wl_a_wl_binds_etvar_ss in H as Ht; eauto. 
      destruct Ht as [Tᵈ Hbinds].
      exists (dworklist_cons_work Ω (work_sub Tᵈ Tᵈ)). split.
      * exists θ. constructor...
      * constructor... apply d_sub_reflexivity...
  - exists ((work_sub (typ_arrow B1ᵈ B2ᵈ) (typ_arrow A1ᵈ A2ᵈ) ⫤ᵈ Ω)).
    split. exists θ. auto...
    econstructor.
    econstructor.
    + apply d_wl_red_weaken_work1 in IHHdred. dependent destruction IHHdred...
    + apply d_wl_red_weaken_work2 in IHHdred. dependent destruction IHHdred...
    + dependent destruction IHHdred. dependent destruction IHHdred...
  (* forall x. A < B  *)
  - destruct_a_wf_wl.  
    dependent destruction H. 
    pick fresh X. inst_cofinites_with X.  
    assert (⊢ᵃʷₛ (work_sub (B1 ᵗ^ₜ X) A1 ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ)). {
      apply a_wf_wl__conswork_sub...
      repeat (constructor; simpl; auto).
      apply a_wf_typ_tvar_etvar_cons in H0...
      apply a_wf_typ_weaken_cons...
    }
    _apply_IH_a_wl_red.
    destruct_trans.
    rename Aᵈ into B1tᵈ. rename Bᵈ into A1ᵈ.
    apply trans_typ_etvar_tvar_subst_cons in H8...
    destruct H8 as [B1xᵈ [Hsubst Htransa]].
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) A1ᵈ ⫤ᵈ Ω).
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all; intros.
        solve_s_in.
        solve_trans_typ_open_close.
      * eapply trans_typ_strengthen_cons...
    + econstructor. 
      eapply d_sub__alll with (T:=T) (L:=L `union` ftvar_in_typ B1 `union` singleton X)...
      * eapply trans_wl_a_wneq_all_d_wneq_all...
        eapply trans_typ_strengthen_cons...
      * intros. inst_cofinites_with X0.
        rewrite_close_open_subst.
        apply s_in_rename.
        eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=dbind_tvar_empty)...
      * eapply trans_wl_ss_mono_typ_d_wl_mono_typ... 
      * rewrite_close_open_subst.
        rewrite Hsubst.
        dependent destruction IHHdred...
      * dependent destruction IHHdred...
  - destruct_a_wf_wl.
    dependent destruction H. dependent destruction H1.
    pick fresh X. inst_cofinites_with X.
    assert ( ⊢ᵃʷₛ (work_sub (B1 ᵗ^ₜ X) (A1 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ). {
      apply a_wf_wl__conswork_sub...
      apply a_wf_typ_tvar_stvar_cons...
      apply a_wf_typ_tvar_stvar_cons...    }
    _apply_IH_a_wl_red.
    destruct_trans...
    rename Aᵈ into B1xᵈ. rename Bᵈ into A1xᵈ.
    exists (work_sub (typ_all (close_typ_wrt_typ X B1xᵈ)) (typ_all (close_typ_wrt_typ X A1xᵈ)) ⫤ᵈ Ω).
    split.
    + exists θ'. econstructor...
      econstructor...
      * inst_cofinites_for trans_typ__all; intros. 
        solve_s_in.
        apply trans_typ_stvar_tvar_cons in H7.
        solve_trans_typ_open_close.
      * inst_cofinites_for trans_typ__all; intros.
        solve_s_in. 
        apply trans_typ_stvar_tvar_cons in H8.
        solve_trans_typ_open_close.
    + dependent destruction IHHdred. 
      econstructor...
      inst_cofinites_for d_sub__all; intros.
      * rewrite_close_open_subst.
        apply s_in_rename.
        eapply trans_typ_dtvar_atyp_s_in_dtyp...
      * rewrite_close_open_subst.
        apply s_in_rename.
        eapply trans_typ_dtvar_atyp_s_in_dtyp...
      * repeat rewrite_close_open_subst.
        simpl in *. eapply d_sub_rename_dtvar_cons in H9; eauto.
      * dependent destruction IHHdred...
  (* ^X < A1 -> A2 *)
  - pick fresh X1. pick fresh X2. 
    assert (Hws: exists Γ1 Γ2, 
      aworklist_subst (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
        (typ_arrow ` X1 ` X2) Γ1 Γ2). {
      eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H; auto.
      destruct H as [Γ1 [Γ2 Hws]].
      exists Γ1, (work_sub `X (typ_arrow A1 A2) ⫤ᵃ Γ2).
      econstructor. auto.
      destruct_a_wf_wl; auto.
    }
    assert (⊢ᵃʷₛ (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)). {
      destruct_a_wf_wl... 
      apply a_wf_wl__conswork_sub; 
      repeat (constructor; simpl; auto);
      apply a_wf_typ_weaken_cons; apply a_wf_typ_weaken_cons...
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H2 in Hsubst as Hwsred...
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply aworklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: binds X1 (dbind_typ T0)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      assert (Hbindsx2: binds X2 (dbind_typ T)  ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ')) by auto.
      apply trans_typ_binds_etvar in Hbindsx1...
      apply trans_typ_binds_etvar in Hbindsx2...
      apply trans_typ_binds_etvar in Hbindsx as Htransx3...
      repeat unify_trans_typ.
      exists (dworklist_cons_work Ω (work_sub (typ_arrow T0 T) (typ_arrow A1ᵈ A2ᵈ))). split.
      * exists θ'. econstructor...
        constructor. 
        -- apply trans_typ_binds_etvar; eauto.
           destruct_binds. destruct_in...
        -- constructor; rewrite_env (nil ++ θ'); 
           eapply trans_typ_strengthen_etvar with (X:=X1) (T:=T0); eauto;
           eapply trans_typ_strengthen_etvar with (X:=X2) (T:=T); eauto.
      * auto.
      * constructor; simpl; apply a_mono_typ__etvar...
      * simpl...
    + eapply aworklist_subst_wf_wl with (Γ:=(work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ); 
      simpl in *; eauto.
      constructor...
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
    assert (⊢ᵃʷₛ (work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)). {
      destruct_a_wf_wl... apply a_wf_wl__conswork_sub; repeat (constructor; simpl; auto);
      apply a_wf_typ_weaken_cons; apply a_wf_typ_weaken_cons...
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]]...
    apply H2 in Hsubst as Hwsred...
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply aworklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ᵗ⊩ `X1 ⇝ T0 ) by eauto.
      assert (Hbindsx2: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ᵗ⊩ `X2 ⇝ T ) by eauto.
      apply trans_typ_binds_etvar in Hbindsx as Htransx3...
      repeat unify_trans_typ.
      exists (work_sub (typ_arrow A1ᵈ A2ᵈ) (typ_arrow T0 T) ⫤ᵈ Ω). split.
      * exists θ'. econstructor...
        constructor. 
        -- constructor; rewrite_env (nil ++ θ'); 
           eapply trans_typ_strengthen_etvar with (X:=X1) (T:=T0); eauto;
           eapply trans_typ_strengthen_etvar with (X:=X2) (T:=T); eauto.
        -- apply trans_typ_binds_etvar; eauto.
           destruct_binds. destruct_in...
      * auto. 
      * constructor; simpl; apply a_mono_typ__etvar...
      * simpl...
    + eapply aworklist_subst_wf_wl with (Γ:=(work_sub (typ_arrow A1 A2) ` X ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); 
      simpl in *; eauto.
      constructor...
    (* τ < ^X *)
  - destruct_a_wf_wl. 
    apply aworklist_subst_wf_wl in H4 as Hwf... 
    _apply_IH_a_wl_red. 
    eapply aworklist_subst_transfer_same_dworklist in H4 as Hws; eauto.
    destruct Hws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ᵈ Ω). split.
    + exists θ'1.
      constructor...
    + econstructor...
      apply d_sub_reflexivity...
  (* ^X < τ *)
  - destruct_a_wf_wl. 
    apply aworklist_subst_wf_wl in H4 as Hwf... 
    _apply_IH_a_wl_red.
    eapply aworklist_subst_transfer_same_dworklist in H4 as Hws; eauto.
    destruct Hws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
    exists (work_sub Tᵈ Tᵈ ⫤ᵈ Ω). split.
    + exists θ'1.
      constructor...
    + econstructor...
      apply d_sub_reflexivity...
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
  - destruct_a_wf_wl.
    remember (fvar_in_exp e).
    pick fresh x. 
    assert (⊢ᵃʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ)). {
      repeat (constructor; simpl; auto).
      eapply a_wf_exp_var_binds_another_cons...
      apply a_wf_typ_weaken_cons...
    }
    inst_cofinites_with x.
    _apply_IH_a_wl_red.   
    destruct_trans. rename_typ.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) (typ_arrow A1ᵈ A2ᵈ) ⫤ᵈ Ω). split.
    + exists θ.
      econstructor...
      econstructor...
      eapply trans_exp__abs with (L:=fvar_in_exp e). intros.
      rewrite_close_open_subst.
      apply trans_exp_rename_var with (x:=x) (x':=x0) in H7...
      rewrite subst_exp_in_exp_open_exp_wrt_exp in H7. simpl in H7. destruct_eq_atom.
      subst. rewrite subst_exp_in_exp_fresh_eq in H7... constructor.
    + destruct_d_wl_del_red.
      econstructor; auto.
      inst_cofinites_for d_chk_inf__chk_abs; auto.
      * eapply trans_wl_a_wf_typ_d_wf_typ...
      * intros. rewrite_close_open_subst.
        apply d_chk_inf_rename_var_cons...
  (* \ x. e <= ^X *)
  - destruct_a_wf_wl.
    pick fresh x. pick fresh X1. pick fresh X2.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.  
    assert (Hws: exists Γ1 Γ2, aworklist_subst 
       (work_check (e ᵉ^^ₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X
       (typ_arrow ` X1 ` X2) Γ1 Γ2). {
       eapply worklist_subst_fresh_etvar_total' with (X1:=X1) (X2:=X2) in H4 as Hws; auto.
       destruct Hws as [Γ1 [Γ2 Hws]].
       exists Γ1, (work_check (e ᵉ^^ₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1 ;ᵃ Γ2)...
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H6 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply aworklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ') ᵗ⊩ `X1 ⇝ T1 ) by eauto.
      assert (Hbindsx2: ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ') ᵗ⊩ `X2 ⇝ T0 ) by eauto.
      repeat unify_trans_typ.
      exists (dworklist_cons_work Ω (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) (typ_arrow T1 T0)))... split.
      * exists θ'... constructor; auto.
        constructor.
        -- inst_cofinites_for trans_exp__abs. intros.
           solve_trans_exp_open_close.
           rewrite_env (nil ++ θ').
           eapply trans_exp_strengthen_etvar with (X:=X1) (T:=T1); eauto.
           eapply trans_exp_strengthen_etvar with (X:=X2) (T:=T0); eauto.
           rewrite ftvar_in_exp_open_exp_wrt_exp_upper... 
           rewrite ftvar_in_exp_open_exp_wrt_exp_upper... 
        -- apply trans_typ_binds_etvar; auto...
           destruct_binds. destruct_in...
      * constructor; auto.
        inst_cofinites_for d_chk_inf__chk_abs; auto...
        -- apply d_mono_typ_d_wf_typ. eapply trans_wl_ss_mono_typ_d_wl_mono_typ...
        -- intros. destruct_d_wl_del_red...
           rewrite_close_open_subst.
           simpl in *.
           eapply d_chk_inf_rename_var_cons in H7...
        -- destruct_d_wl_del_red...
      * repeat (constructor; simpl; eauto).
        eapply a_wf_exp_weaken_etvar_twice...
      * simpl. constructor... 
      * simpl...  
    + eapply aworklist_subst_wf_wl with 
        (Γ:=(work_check (e ᵉ^^ₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); eauto. 
      * repeat (constructor; simpl; auto).
        apply a_wf_exp_var_binds_another_cons with (A1:=T)...
        rewrite_env ((x ~ abind_var_typ T) ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ).
        apply a_wf_exp_weaken...
      * simpl... constructor...
  (* \ x. e <= ⊤ *)
  - destruct_a_wf_wl. pick fresh x. inst_cofinites_with x. 
    assert ( ⊢ᵃʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ)). 
    { repeat (constructor; simpl; auto). 
      eapply a_wf_exp_var_binds_another_cons; eauto.
    }
    _apply_IH_a_wl_red.
    destruct_trans.
    exists (work_check (exp_abs (close_exp_wrt_exp x eᵈ)) typ_top ⫤ᵈ Ω). split.
    + exists θ.
      repeat constructor...
      inst_cofinites_for trans_exp__abs. intros.
      solve_trans_exp_open_close.
    + destruct_d_wl_del_red...
      econstructor; auto.
      inst_cofinites_for d_chk_inf__chk_abstop. intros.
      rewrite_close_open_subst.
      simpl in *.
      eapply d_chk_inf_rename_var_cons in H10...
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
    unify_binds.
    _apply_IH_a_wl_red.
    destruct_trans. rename_typ.
    exists (work_infer (exp_var_f x) csᵈ ⫤ᵈ Ω).
    split... econstructor... econstructor...
    eapply trans_wl_a_wl_binds_var_trans_typ_d_wl in H3...
  (* e : A => _ *)
  - exists (work_infer (exp_anno eᵈ Aᵈ) csᵈ ⫤ᵈ Ω)...
    split. exists θ...
    destruct_d_wl_del_red.
    econstructor...
  (* /\ a. e : A => _ *)
  - destruct_a_wf_wl. 
    pick fresh X. inst_cofinites_with X.
    assert (Hwf: ⊢ᵃʷₛ (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ)). {
      dependent destruction H0.
      repeat (constructor; simpl; auto).
      inst_cofinites_for a_wf_typ__all; intros.
      solve_s_in.
      apply a_wf_typ_rename_tvar_cons with (Y:=X0) in H0. 
      simpl_open_subst_typ.
    }
    _apply_IH_a_wl_red.
    destruct_trans.
    rename_typ.
    dependent destruction H6.
    exists (work_infer (exp_tabs (exp_anno (close_exp_wrt_typ X eᵈ) (close_typ_wrt_typ X Axᵈ))) csᵈ ⫤ᵈ Ω). split.
    + exists θ...
      econstructor...
      econstructor...
      inst_cofinites_for trans_exp__tabs; intros; simpl.
      -- rewrite_close_open_subst.
         apply trans_exp_rename_tvar_cons with (X':=X0) in H10; eauto. 
         rewrite subst_typ_in_exp_open_exp_wrt_typ in H10...
         simpl in *. destruct_eq_atom.
         rewrite subst_typ_in_exp_fresh_eq in H10; eauto.
      -- solve_trans_typ_open_close.
    + assert (θ ᵗ⊩ typ_all A ⇝ typ_all A1ᵈ). {
        inst_cofinites_for trans_typ__all; intros;
        inst_cofinites_with X0; auto.
      }
      assert (θ ᵗ⊩ typ_all A ⇝ typ_all (close_typ_wrt_typ X Axᵈ)). {
        inst_cofinites_for trans_typ__all; intros; auto;
        solve_trans_typ_open_close.
      }
      unify_trans_typ. inversion H13. subst.
      apply d_wl_del_red__inf with (A:=typ_all (close_typ_wrt_typ X Axᵈ)).
      * inst_cofinites_for d_chk_inf__inf_tabs. 
        -- intros. 
           rewrite_close_open_subst. apply s_in_rename. 
           eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=dbind_tvar_empty)...
        -- intros. inst_cofinites_with X0. rewrite_close_open_subst.
           rewrite_close_open_subst.
           destruct_d_wl_del_red. simpl in *.
           eapply d_chk_inf_rename_tvar_cons in H11...
      * destruct_d_wl_del_red... 
  (* ⟨ l ↦ e1 ⟩ => _  *)
  - exists (work_infer (exp_rcd_single l eᵈ) csᵈ ⫤ᵈ Ω)...
    split. exists θ...
    destruct_d_wl_del_red...
  (* ⟨ l ↦ e1 , e2 ⟩ => _ *)
  - exists (work_infer (exp_rcd_cons l1 eᵈ eᵈ0) csᵈ ⫤ᵈ Ω)...
    split. exists θ...
    destruct_d_wl_del_red...
  (* \x. e => _ *)
  - destruct_a_wf_wl.
    pick fresh x. pick fresh X1. pick fresh X2.
    inst_cofinites_with x. inst_cofinites_with X1. inst_cofinites_with X2.
    assert (Hwf: ⊢ᵃʷₛ (work_check (e ᵉ^^ₑ exp_var_f x) ` X2  ⫤ᵃ x ~ᵃ ` X1;ᵃ work_applys cs (typ_arrow ` X1 ` X2)
            ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)). {
      repeat (constructor; simpl; auto).
      apply a_wf_exp_var_binds_another_cons with (A1:=T)...
      rewrite_env (x ~ abind_var_typ T ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ). apply a_wf_exp_weaken...
      rewrite_env (nil ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ). apply a_wf_conts_weaken...        
    }
    _apply_IH_a_wl_red.
    destruct_trans. unify_trans_typ.
    exists (work_infer (exp_abs (close_exp_wrt_exp x eᵈ)) csᵈ ⫤ᵈ Ω).
    split.
    + exists θ'...
      econstructor...
      econstructor...
      * inst_cofinites_for trans_exp__abs. intros.
        solve_trans_exp_open_close.
        rewrite_env (nil ++ θ').
        eapply trans_exp_strengthen_etvar with (X:=X1) (T:=T1); eauto.
        eapply trans_exp_strengthen_etvar with (X:=X2) (T:=T0); eauto.
        rewrite ftvar_in_exp_open_exp_wrt_exp_upper... 
        rewrite ftvar_in_exp_open_exp_wrt_exp_upper... 
      * rewrite_env (nil ++ θ').
        eapply trans_conts_strengthen_etvar with (X:=X1) (T:=T1); eauto.
        eapply trans_conts_strengthen_etvar with (X:=X2) (T:=T0); eauto.
    + eapply d_wl_del_red__inf with (A:=typ_arrow A1ᵈ Aᵈ0). 
      * assert (Hbindsx1: ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ') ᵗ⊩ `X1 ⇝ T1 ) by eauto.
        assert (Hbindsx2: ((X2, dbind_typ T0) :: (X1, dbind_typ T1) :: θ') ᵗ⊩ `X2 ⇝ T0 ) by eauto.
        repeat unify_trans_typ.
        destruct_d_wl_del_red... simpl in *...
        inst_cofinites_for d_chk_inf__inf_abs_mono; auto.
        constructor; eapply trans_wl_ss_mono_typ_d_wl_mono_typ...
        intros. rewrite_close_open_subst; auto. 
        eapply d_chk_inf_rename_var_cons in H10... auto.
      * destruct_d_wl_del_red...
  (* () => _ *)
  - exists (work_infer exp_unit csᵈ ⫤ᵈ Ω)...
    split. exists θ... 
    econstructor...
  (* e1 e2 => _ *)
  - exists (work_infer (exp_app eᵈ eᵈ0) csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_infer (exp_rcd_proj eᵈ l) csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
    econstructor... econstructor; eauto.
    dependent destruction H5. simpl in *... 
  (* A -> B ∙ e =>=> _ *)
  - exists (work_infapp Aᵈ Bᵈ eᵈ csᵈ ⫤ᵈ Ω)...
    split. destruct_d_wl_del_red. exists θ...
    econstructor...
  (* A -> B ∙ C =>=> _ *)
  - exists (work_infproj Aᵈ Bᵈ Cᵈ csᵈ ⫤ᵈ Ω)...
    split. destruct_d_wl_del_red. exists θ...
    econstructor...
  - exists (work_infabs (typ_arrow Aᵈ Bᵈ) cdᵈ ⫤ᵈ Ω)...
    split. destruct_d_wl_del_red. exists θ... 
    econstructor... constructor... 
  - exists (work_infabs typ_bot cdᵈ ⫤ᵈ Ω)...
    split...
    destruct_d_wl_del_red...
    dependent destruction H7... 
  (* ∀ a. A ▹ _ *)
  - destruct_a_wf_wl. 
    dependent destruction H.
    pick fresh X. inst_cofinites_with X.
    assert (⊢ᵃʷₛ (work_infabs (A ᵗ^ₜ X) cd ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ)). {
      repeat (constructor; simpl; auto).
      apply a_wf_typ_tvar_etvar_cons...
      rewrite_env (nil ++ (X ~ ⬒) ++ ⌊ Γ ⌋ᵃ).
      apply a_wf_contd_weaken...
    }
    _apply_IH_a_wl_red.
    destruct_trans.
    eapply trans_typ_etvar_tvar_subst_cons in H9...
    destruct H9 as [Axᵈ [Hsubst Htransa]].
    exists (work_infabs (typ_all (close_typ_wrt_typ X Axᵈ)) cdᵈ ⫤ᵈ Ω). split.
    exists θ'.
    + constructor...
      constructor...
      * inst_cofinites_for trans_typ__all;
        intros... solve_s_in.
        solve_trans_typ_open_close.
      * rewrite_env (nil ++ θ'). 
        eapply trans_contd_strengthen_etvar; eauto.
    + dependent destruction IHHdred.  
      eapply d_wl_del_red__infabs with (B:=B) (C:=C); auto.
      eapply d_infabs__all with (T:=T)...
      * eapply trans_wl_ss_mono_typ_d_wl_mono_typ... 
      * inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X0; rewrite_close_open_subst.
        apply s_in_rename. eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=dbind_tvar_empty)...
        apply d_wf_typ_rename_tvar_cons.
        rewrite_env (dwl_to_denv (X ~ᵈ □ ;ᵈ Ω)).
        eapply trans_wl_a_wf_typ_d_wf_typ with (Γ:= X ~ᵃ □ ;ᵃ Γ)...
        constructor...
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
    assert (⊢ᵃʷₛ (work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)). {
      destruct_a_wf_wl...
      repeat (constructor; simpl; auto).
      rewrite_env (nil ++ ((X2, ⬒) :: (X1 ~ ⬒)) ++ ⌊ Γ ⌋ᵃ).
      apply a_wf_contd_weaken...
    }
    destruct Hws as [Γ1 [Γ2 Hsubst]].
    apply H1 in Hsubst as Hwsred.
    destruct Hwsred as [Ω [[θ Htrans] Hdred]].
    + eapply aworklist_subst_transfer_same_dworklist in Hsubst as Htransws; eauto...
      destruct Htransws as [θ'1 [Tᵈ [Htrans_rev [Htransa [Htransa' [Hbinds [Hbindsx Hwfss]]]]]]].
      destruct_trans.
      assert (Hbindsx1: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ᵗ⊩ `X1 ⇝ T0 ) by eauto.
      assert (Hbindsx2: ((X2, dbind_typ T) :: (X1, dbind_typ T0) :: θ') ᵗ⊩ `X2 ⇝ T ) by eauto.
      repeat unify_trans_typ.
      exists (dworklist_cons_work Ω (work_infabs (typ_arrow T0 T) cdᵈ)). split.
      * exists θ'. constructor; auto.
        constructor.
        -- apply trans_typ_binds_etvar...
           destruct_binds. destruct_in...
        -- rewrite_env (nil ++ θ').  
           eapply trans_contd_strengthen_etvar; eauto.  
           eapply trans_contd_strengthen_etvar; eauto. 
      * destruct_d_wl_del_red...       
      * simpl. auto.
      * simpl...
    + apply aworklist_subst_wf_wl with 
        (Γ:=(work_infabs (typ_arrow ` X1 ` X2) cd ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); simpl...
      simpl. constructor...
  - exists (work_infer (exp_tapp eᵈ Bᵈ) csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  (* ∀ a. A ∘ B =>=> _ *)
  - destruct_a_wf_wl. 
    assert (⊢ᵃʷₛ (work_applys cs (A ᵗ^^ₜ B) ⫤ᵃ Γ)). {
      repeat (constructor; simpl; auto).
      apply a_wf_typ_all_open...
    }
    _apply_IH_a_wl_red.
    destruct_trans.  
    trans_all_typ.
    dependent destruction H.
    pick fresh X. inst_cofinites_with X.
    erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H6; eauto.
    eapply trans_typ_subst_tvar_cons in H6...
    destruct H6 as [Axᵈ [Hsubst Htransa]].
    exists (work_inftapp (typ_all (close_typ_wrt_typ X Axᵈ)) Bᵈ csᵈ ⫤ᵈ Ω).
    split.
    + exists θ.
      econstructor...
      econstructor...
      inst_cofinites_for trans_typ__all; intros.
      solve_s_in. 
      solve_trans_typ_open_close.
    + eapply d_wl_del_red__inftapp with (C:=open_typ_wrt_typ (close_typ_wrt_typ X Axᵈ) Bᵈ)...
      econstructor; auto...
      * inst_cofinites_for d_wf_typ__all; intros; rewrite_close_open_subst. 
        -- apply s_in_rename... eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=dbind_tvar_empty)...
        -- apply d_wf_typ_rename_tvar_cons.
           rewrite_env (dwl_to_denv (dworklist_cons_var Ω X dbind_tvar_empty)).
           eapply trans_wl_a_wf_typ_d_wf_typ with (Γ:=aworklist_cons_var Γ X abind_tvar_empty)...
           constructor...
      * rewrite_close_open_subst. rewrite Hsubst...
  - exists (work_inftapp typ_bot Bᵈ csᵈ ⫤ᵈ Ω).
    split... econstructor; eauto.
  - exists (work_inftapp (typ_intersection A1ᵈ A2ᵈ) Bᵈ csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_inftapp (typ_intersection A1ᵈ A2ᵈ) Bᵈ csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_inftapp (typ_union A1ᵈ A2ᵈ) Bᵈ csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_inftappunion C1ᵈ A2ᵈ Bᵈ csᵈ ⫤ᵈ Ω).
    split...
    destruct_d_wl_del_red...
  - exists (work_unioninftapp C1ᵈ C2ᵈ csᵈ ⫤ᵈ Ω).
    split...
  - dependent destruction H4_.
    exists (work_infrcdsingle l Aᵈ csᵈ ⫤ᵈ Ω). split...
  - dependent destruction H6_.
    rename_typ.
    exists (work_infrcdconsintersection l1 A1ᵈ eᵈ csᵈ ⫤ᵈ Ω). split...
    destruct_d_wl_del_red...
  - exists (work_intersectioninfrcdcons A1ᵈ A2ᵈ csᵈ ⫤ᵈ Ω). split...
  - destruct_a_wf_wl.
    eapply a_wf_work_apply_conts in H3 as Hwf...
    assert ( ⊢ᵃʷₛ (w ⫤ᵃ Γ) ) by (eapply a_wf_wl_strengthen_work; eauto).
    apply IHHared in H4...
    destruct H4 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    trans_all_typ.
    eapply trans_conts_total in H0... 
    destruct H0 as [csᵈ Htransc].
    exists (work_applys csᵈ Aᵈ ⫤ᵈ Ω). split.
    exists θ'. econstructor...
    eapply trans_apply_conts in H4; eauto.
  - destruct_a_wf_wl.
    eapply a_wf_work_apply_contd with (A:=A) (B:=B) in H1 as Hwf...
    assert ( ⊢ᵃʷₛ (w ⫤ᵃ Γ) ) by (eapply a_wf_wl_strengthen_work; eauto).
    apply IHHared in H5...
    destruct H5 as [Ω [Htrans Hdred]].
    destruct Htrans as [θ Htrans].
    dependent destruction Htrans.
    trans_all_typ.
    eapply trans_contd_total in H1... 
    destruct H1 as [cdᵈ Htransc].
    exists (work_applyd cdᵈ Aᵈ Bᵈ ⫤ᵈ Ω). split.
    exists θ'. econstructor...
    eapply trans_apply_contd in H5; eauto.
Qed.