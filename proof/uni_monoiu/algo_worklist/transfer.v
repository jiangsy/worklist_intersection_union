Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni_monoiu.notations.
Require Import uni_monoiu.decl.prop_basic.
Require Import uni_monoiu.decl_worklist.prop_equiv.
Require Import uni_monoiu.decl.prop_subtyping.
Require Import uni_monoiu.algo_worklist.def_extra.
Require Import uni_monoiu.algo_worklist.prop_basic.
Require Import uni_monoiu.ltac_utils.

Definition subst_set := denv.

Open Scope dbind.

Fixpoint ss_to_denv (θ : subst_set) : denv := 
  match θ with 
  | nil => nil
  | (X , dbind_tvar_empty) :: θ' => (X ~ dbind_tvar_empty) ++ ss_to_denv θ'
  | (X , dbind_stvar_empty) :: θ' => (X ~ dbind_stvar_empty) ++ ss_to_denv θ'
  | (X , dbind_typ T) :: θ' => ss_to_denv θ'
  end.

Notation " ⌈ θ ⌉ᵈ " :=
  (ss_to_denv θ)
    (at level 49, no associativity) : type_scope.

Fixpoint ss_to_aenv (θ : subst_set) : aenv := 
  match θ with 
  | nil => nil
  | (X , dbind_tvar_empty) :: θ' => (X ~ abind_tvar_empty) ++ ss_to_aenv θ'
  | (X , dbind_stvar_empty) :: θ' => (X ~ abind_stvar_empty) ++ ss_to_aenv θ'
  | (X , dbind_typ T) :: θ' => (X ~ abind_etvar_empty) ++ ss_to_aenv θ'
  end.

Notation " ⌈ θ ⌉ᵃ " :=
  (ss_to_aenv θ)
    (at level 49, no associativity) : type_scope.
  
Inductive wf_ss : subst_set -> Prop :=
  | wfss__nil : wf_ss nil
  | wfss__tvar : forall θ X,
      wf_ss θ -> 
      X ∉ dom θ ->
      wf_ss ((X , dbind_tvar_empty) :: θ)
  | wf_ss__stvar : forall θ X,
    wf_ss θ ->
    X ∉ dom θ ->
    wf_ss ((X, dbind_stvar_empty) :: θ)
  | wf_ss__etvar : forall θ X T, 
    wf_ss θ  -> 
    X ∉ dom θ  ->
    d_mono_typ (ss_to_denv θ) T -> 
    wf_ss ((X , dbind_typ T) :: θ).

Inductive trans_typ : subst_set -> typ -> typ -> Prop := 
  | trans_typ__tvar : forall θ X, 
      wf_ss θ -> 
      X ~ □ ∈ᵈ θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__stvar : forall θ X, 
      wf_ss θ -> 
      X ~ ■ ∈ᵈ θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__etvar : forall θ X A1,
      wf_ss θ ->
      X ~ A1 ∈ᵈ θ ->
      trans_typ θ (typ_var_f X) A1
  | trans_typ_unit : forall θ,
      wf_ss θ ->
      trans_typ θ typ_unit typ_unit
  | trans_typ__bot : forall θ,
      wf_ss θ ->
      trans_typ θ typ_bot typ_bot
  | trans_typ__top : forall θ,
      wf_ss θ ->
      trans_typ θ typ_top typ_top
  | trans_typ__arrow : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_typ θ (typ_arrow A1ᵃ A2ᵃ) (typ_arrow A1ᵈ A2ᵈ)
  | trans_typ__all : forall θ L A1ᵃ A1ᵈ,
      (forall X, X ∉ L -> s_in X (open_typ_wrt_typ A1ᵃ (typ_var_f X))) ->
      (forall X, X ∉ L -> 
        trans_typ ((X, dbind_tvar_empty) :: θ) (open_typ_wrt_typ A1ᵃ (typ_var_f X)) (open_typ_wrt_typ A1ᵈ (typ_var_f X))
      ) ->
      trans_typ θ (typ_all A1ᵃ) (typ_all A1ᵈ)
  | ins_typ__intersection : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_typ θ (typ_intersection A1ᵃ A2ᵃ) (typ_intersection A1ᵈ A2ᵈ)
  | trans_typ__union : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_typ θ (typ_union A1ᵃ A2ᵃ) (typ_union A1ᵈ A2ᵈ)
  . 

Inductive trans_exp : subst_set -> exp -> exp -> Prop :=
  | trans_exp__unit : forall θ,
      wf_ss θ ->
      trans_exp θ exp_unit exp_unit
  | trans_exp__var : forall θ x,
      wf_ss θ ->
      trans_exp θ (exp_var_f x) (exp_var_f x)
  | trans_exp__abs : forall L θ eᵃ eᵈ,
      (forall x, x ∉ L -> 
        trans_exp θ (open_exp_wrt_exp eᵃ (exp_var_f x))
                   (open_exp_wrt_exp eᵈ (exp_var_f x))
        ) ->
      trans_exp θ (exp_abs eᵃ) (exp_abs eᵈ)
  | trans_exp__app : forall θ e1ᵃ e2ᵃ e1ᵈ e2ᵈ,
      trans_exp θ e1ᵃ e1ᵈ ->
      trans_exp θ e2ᵃ e2ᵈ ->
      trans_exp θ (exp_app e1ᵃ e2ᵃ) (exp_app e1ᵈ e2ᵈ)
  | trans_exp__tabs : forall L θ eᵃ eᵈ Aᵃ Aᵈ,
      ( forall X, X ∉ L -> 
          trans_exp ((X, dbind_tvar_empty) :: θ) (open_exp_wrt_typ eᵃ (typ_var_f X)) (open_exp_wrt_typ eᵈ (typ_var_f X))) ->
      ( forall X, X ∉ L -> 
          trans_typ ((X, dbind_tvar_empty) :: θ) (open_typ_wrt_typ Aᵃ (typ_var_f X)) (open_typ_wrt_typ Aᵈ (typ_var_f X))) ->
      trans_exp θ (exp_tabs (exp_anno eᵃ Aᵃ)) (exp_tabs (exp_anno eᵈ Aᵈ))
  | trans_exp__tapp : forall θ eᵃ eᵈ A1ᵃ A1ᵈ,
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_exp θ (exp_tapp eᵃ A1ᵃ) (exp_tapp eᵈ A1ᵈ)
  | trans_exp__anno : forall θ eᵃ eᵈ A1ᵃ A1ᵈ, 
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_exp θ (exp_anno eᵃ A1ᵃ) (exp_anno eᵈ A1ᵈ).

Inductive trans_conts : subst_set -> conts -> conts -> Prop :=
  | trans_conts__infabs : forall θ cdᵃ cdᵈ,
    trans_contd θ cdᵃ cdᵈ ->
    trans_conts θ (conts_infabs cdᵃ) (conts_infabs cdᵈ)
  | trans_cont__inftapp : forall θ Aᵃ Aᵈ cᵃ cᵈ,
    trans_typ θ Aᵃ Aᵈ ->
    trans_conts θ cᵃ cᵈ ->
    trans_conts θ (conts_inftapp Aᵃ cᵃ) (conts_inftapp Aᵈ cᵈ)
  | trans_cont__inftappunion : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_typ θ A2ᵃ A2ᵈ ->
    trans_conts θ cᵃ cᵈ ->
    trans_conts θ (conts_inftappunion A1ᵃ A2ᵃ cᵃ) (conts_inftappunion A1ᵈ A2ᵈ cᵈ)
  | trans_cont__unioninftapp : forall θ Aᵃ Aᵈ cᵃ cᵈ,
    trans_typ θ Aᵃ Aᵈ ->
    trans_conts θ cᵃ cᵈ ->
    trans_conts θ (conts_unioninftapp Aᵃ cᵃ) (conts_unioninftapp Aᵈ cᵈ)
  | trans_cont__sub : forall θ Aᵃ Aᵈ,
    trans_typ θ Aᵃ Aᵈ ->
    trans_conts θ (conts_sub Aᵃ) (conts_sub Aᵈ)
with trans_contd : subst_set -> contd -> contd -> Prop :=
  | trans_contd__infapp : forall θ eᵃ eᵈ csᵃ csᵈ,
    trans_exp θ eᵃ eᵈ ->
    trans_conts θ csᵃ csᵈ ->
    trans_contd θ (contd_infapp eᵃ csᵃ) (contd_infapp eᵈ csᵈ)
  | trans_contd__infabs_union : forall θ Aᵃ Aᵈ cdᵃ cdᵈ,
    trans_typ θ Aᵃ Aᵈ ->
    trans_contd θ cdᵃ cdᵈ ->
    trans_contd θ (contd_infabsunion Aᵃ cdᵃ) (contd_infabsunion Aᵈ cdᵈ)
  | trans_contd__unioninfabs : forall θ Aᵃ Aᵈ Bᵃ Bᵈ cdᵃ cdᵈ,
    trans_typ θ Aᵃ Aᵈ ->
    trans_typ θ Bᵃ Bᵈ ->
    trans_contd θ cdᵃ cdᵈ ->
    trans_contd θ (contd_unioninfabs Aᵃ Bᵃ cdᵃ) (contd_unioninfabs Aᵈ Bᵈ cdᵈ).

Inductive trans_work : subst_set -> work -> work -> Prop :=
  | trans_work__inf : forall θ eᵃ eᵈ csᵃ csᵈ,
      trans_exp θ eᵃ eᵈ ->
      trans_conts θ csᵃ csᵈ ->
      trans_work θ (work_infer eᵃ csᵃ) (work_infer eᵈ csᵈ)
  | trans_work__chk : forall θ eᵃ eᵈ Aᵃ Aᵈ,
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ Aᵃ Aᵈ ->
      trans_work θ (work_check eᵃ Aᵃ) (work_check eᵈ Aᵈ)
  | trans_work__infabs : forall θ Aᵃ Aᵈ  cdᵃ cdᵈ,
      trans_typ θ Aᵃ Aᵈ ->
      trans_contd θ cdᵃ cdᵈ ->
      trans_work θ (work_infabs Aᵃ cdᵃ ) (work_infabs Aᵈ cdᵈ)
  | trans_work__infabsunion : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ B1ᵃ B1ᵈ cdᵃ cdᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_typ θ B1ᵃ B1ᵈ ->
      trans_contd θ cdᵃ cdᵈ ->
      trans_work θ (work_infabsunion A1ᵃ B1ᵃ A2ᵃ cdᵃ) (work_infabsunion A1ᵈ B1ᵈ A2ᵈ cdᵈ)
  | trans_work__infapp : forall θ Aᵃ Aᵈ Bᵃ Bᵈ eᵃ eᵈ csᵃ csᵈ,
      trans_typ θ Aᵃ Aᵈ ->
      trans_typ θ Bᵃ Bᵈ ->
      trans_exp θ eᵃ eᵈ ->
      trans_conts θ csᵃ csᵈ ->
      trans_work θ (work_infapp Aᵃ Bᵃ eᵃ csᵃ) (work_infapp Aᵈ Bᵈ eᵈ csᵈ)
  | trans_work__inftapp : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ csᵃ csᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_conts θ csᵃ csᵈ ->
      trans_work θ (work_inftapp A1ᵃ A2ᵃ csᵃ) (work_inftapp A1ᵈ A2ᵈ csᵈ)
  | trans_work__sub : forall θ Aᵃ Aᵈ Bᵃ Bᵈ,
      trans_typ θ Aᵃ Aᵈ ->
      trans_typ θ Bᵃ Bᵈ ->
      trans_work θ (work_sub Aᵃ Bᵃ) (work_sub Aᵈ Bᵈ)
  | trans_work__inftappunion : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ B1ᵃ B1ᵈ csᵃ csᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_typ θ B1ᵃ B1ᵈ ->
      trans_conts θ csᵃ csᵈ ->
      trans_work θ (work_inftappunion A1ᵃ A2ᵃ B1ᵃ csᵃ) (work_inftappunion A1ᵈ A2ᵈ B1ᵈ csᵈ)
  | trans_work__unioninftapp : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ csᵃ csᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_conts θ csᵃ csᵈ ->
      trans_work θ (work_unioninftapp A1ᵃ A2ᵃ csᵃ) (work_unioninftapp A1ᵈ A2ᵈ csᵈ)
  | trans_work__unioninfabs : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ B1ᵃ B1ᵈ B2ᵃ B2ᵈ cdᵃ cdᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ A2ᵃ A2ᵈ ->
      trans_typ θ B1ᵃ B1ᵈ ->
      trans_typ θ B2ᵃ B2ᵈ ->
      trans_contd θ cdᵃ cdᵈ ->
      trans_work θ (work_unioninfabs A1ᵃ B1ᵃ A2ᵃ B2ᵃ cdᵃ) (work_unioninfabs A1ᵈ B1ᵈ A2ᵈ B2ᵈ cdᵈ)
  | trans_work__applys : forall θ Aᵃ Aᵈ csᵃ csᵈ,
      trans_typ θ Aᵃ Aᵈ ->
      trans_conts θ csᵃ csᵈ ->
      trans_work θ (work_applys csᵃ Aᵃ) (work_applys csᵈ Aᵈ)
  | trans_work__applyd : forall θ Aᵃ Aᵈ Bᵃ Bᵈ cdᵃ cdᵈ,
      trans_typ θ Aᵃ Aᵈ ->
      trans_typ θ Bᵃ Bᵈ ->
      trans_contd θ cdᵃ cdᵈ ->
      trans_work θ (work_applyd cdᵃ Aᵃ Bᵃ) (work_applyd cdᵈ Aᵈ Bᵈ)
.

Notation "θ ᵗ⊩ Aᵃ ⇝ Aᵈ" := (trans_typ θ Aᵃ Aᵈ)
  (at level 65, Aᵃ at next level, no associativity).

Notation "θ ᵉ⊩ eᵃ ⇝ eᵈ" := (trans_exp θ eᵃ eᵈ)
  (at level 65, eᵃ at next level, no associativity).

Notation "θ ᶜˢ⊩ csᵃ ⇝ csᵈ" := (trans_conts θ csᵃ csᵈ)
  (at level 65, csᵃ at next level, no associativity).

Notation "θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ" := (trans_contd θ cdᵃ cdᵈ)
  (at level 65, cdᵃ at next level, no associativity).

Notation "θ ʷ⊩ wᵃ ⇝ wᵈ" := (trans_work θ wᵃ wᵈ)
  (at level 65, wᵃ at next level, no associativity).

Reserved Notation "θ ⊩ Γ ⇝ Ω ⫣ θ'"
  (at level 65, Γ at next level, Ω at next level, no associativity).
Inductive trans_worklist : subst_set -> aworklist -> dworklist -> subst_set -> Prop := 
  | trans_wl__empty : forall θ, 
      wf_ss θ -> 
      θ ⊩ aworklist_empty ⇝ dworklist_empty ⫣ θ
  | trans_wl__cons_work : forall θ θ' Γ Ω  wᵃ wᵈ, 
      θ ⊩ Γ ⇝ Ω ⫣ θ' ->
      trans_work θ' wᵃ wᵈ ->
      θ ⊩ aworklist_cons_work Γ wᵃ ⇝ dworklist_cons_work Ω wᵈ ⫣ θ'
  | trans_wl__cons_tvar : forall θ θ' Γ Ω X, 
      θ ⊩ Γ ⇝ Ω ⫣ θ' ->
      X ∉ dom θ' -> 
      θ ⊩ aworklist_cons_var Γ X abind_tvar_empty ⇝ dworklist_cons_var Ω X dbind_tvar_empty ⫣ (X, dbind_tvar_empty) :: θ'
  | trans_wl__cons_stvar : forall θ θ' Γ Ω X, 
      θ ⊩ Γ ⇝ Ω ⫣ θ' ->
      X ∉ dom θ' -> 
      θ ⊩ aworklist_cons_var Γ X abind_stvar_empty ⇝ dworklist_cons_var Ω X dbind_stvar_empty ⫣ (X, dbind_stvar_empty) :: θ'
  | trans_wl__cons_var : forall θ θ' Γ Ω A1ᵃ A1ᵈ x, 
      θ ⊩ Γ ⇝ Ω ⫣ θ' ->
      trans_typ θ' A1ᵃ A1ᵈ ->
      θ ⊩ aworklist_cons_var Γ x (abind_var_typ A1ᵃ) ⇝ dworklist_cons_var Ω x (dbind_typ A1ᵈ) ⫣ θ'
  | trans_wl__cons_etvar : forall θ θ' Γ Ω T X, 
      θ ⊩ Γ ⇝ Ω ⫣ θ' -> 
      X ∉ dom θ' -> 
      d_mono_typ (ss_to_denv θ' ) T ->
      θ ⊩ aworklist_cons_var Γ X abind_etvar_empty ⇝ Ω ⫣  (X, dbind_typ T) :: θ'
where "θ ⊩ Γ ⇝ Ω ⫣ θ'" := (trans_worklist θ Γ Ω θ').

Definition transfer (Γ : aworklist) (Ω : dworklist)  : Prop :=
  exists θ', trans_worklist nil Γ Ω θ'.

#[export] Hint Constructors trans_typ trans_exp trans_conts trans_contd trans_work trans_worklist wf_ss : core.

Lemma binds_same_move_etvar_before : forall θ1 θ2 X1 X2 b1 b2 Y (b : dbind),
  binds Y b (θ2 ++ (X2, b2) :: (X1, b1) :: θ1) <->
  binds Y b ((X1, b1) :: θ2 ++ (X2, b2) :: θ1).
Proof.
  intros;
  split; intros; 
  try rewrite_env (((X1, b1) :: θ2) ++ (X2, b2) :: θ1) in H; 
  try rewrite_env (((X1, b1) :: θ2) ++ (X2, b2) :: θ1);
  apply binds_app_iff in H; apply binds_app_iff; inversion H; destruct_binds; try destruct_in; eauto.
Qed.

Lemma notin_dom_reorder : forall X X0 θ θ',
  X ∉ dom θ ->
  X <> X0 ->
  (forall Y (b: dbind), X0 <> Y -> binds Y b θ <-> binds Y b θ') ->
  X ∉ dom θ'.
Proof.
  intros. unfold not. intros.
  apply binds_In_inv in H2. destruct H2 as [b Hbinds].
  apply H1 in Hbinds...
  eapply binds_dom_contradiction in Hbinds; auto.
  unfold not. intros. subst. contradiction.
Qed.

Lemma wf_ss_uniq : forall θ,
  wf_ss θ -> uniq θ.
Proof.
  intros. induction H; auto.
Qed.

Lemma dom_ss_to_denv_upper : forall θ,
  dom (ss_to_denv θ) [<=] dom θ.
Proof.
  intros. induction θ; simpl.
  + fsetdec.
  + destruct a as [X b]; destruct b; simpl; fsetdec.
Qed.  

(* Lemma wf_ss_d_wf_env : forall θ,
  wf_ss θ ->
  d_wf_env (ss_to_denv θ).
Proof.
  intros. induction H; auto; simpl in *.
  - constructor; auto. constructor; auto.
    rewrite dom_ss_to_denv_upper; auto.
  - constructor; eauto.
    rewrite dom_ss_to_denv_upper; auto.
Qed. *)

Lemma ss_to_denv_app : forall θ1 θ2,
  ss_to_denv (θ2 ++ θ1) = (ss_to_denv θ2) ++ (ss_to_denv θ1).
Proof.
  intros. induction θ2; simpl in *; auto.
  - destruct a as [X b]; destruct b; 
      simpl in *; rewrite IHθ2; auto.
Qed.

Lemma ss_to_denv_subst_typ_in_dbind_comm : forall θ X A,
  ss_to_denv (map (subst_typ_in_dbind A X) θ) = map (subst_typ_in_dbind A X) (ss_to_denv θ). 
Proof.
  intros. induction θ; simpl; auto.
  - destruct a as [Y]; destruct d; simpl; rewrite IHθ; auto.
Qed.

#[local] Hint Rewrite ss_to_denv_app : core.

Lemma binds_ss_to_denv_binds_ss : forall X b θ,
  binds X b (ss_to_denv θ) ->
  binds X b θ.  
Proof.
  intros. induction θ; auto.
  - destruct a; destruct d; simpl in *; try inversion H; auto;
      destruct_binds; eauto.
Qed.

Lemma binds_tvar_ss_to_aenv_binds_ss : forall X (θ: subst_set),
  X ~ □ ∈ᵃ ⌈ θ ⌉ᵃ ->
  X ~ □ ∈ᵈ θ.  
Proof.
  intros. induction θ; auto.
  - destruct a; destruct d; simpl in *; try inversion H; auto;
      destruct_binds; eauto.
Qed.

Lemma binds_etvar_ss_to_aenv_binds_ss : forall X (θ: subst_set),
  wf_ss θ ->
  X ~ ⬒ ∈ᵃ ⌈ θ ⌉ᵃ ->
  exists T, X ~ T ∈ᵈ θ.
Proof.
  intros. induction H; auto; simpl in *; destruct_binds.
  - inversion H0.
  - apply IHwf_ss in H3; auto. destruct H3 as [T]. eauto. 
  - apply IHwf_ss in H3; auto. destruct H3 as [T]. eauto. 
  - exists T. eauto.  
  - apply IHwf_ss in H4; auto. destruct H4 as [T0]. eauto. 
Qed.

Lemma binds_ss_etvar_binds_ss_to_aenv : forall X T θ,
  wf_ss θ ->
  X ~ T ∈ᵈ θ ->
  X ~ ⬒ ∈ᵃ ⌈ θ ⌉ᵃ.
Proof.
  intros. induction H; auto; simpl in *; destruct_binds; eauto.
Qed.

Lemma binds_stvar_ss_to_aenv_binds_ss : forall X (θ: subst_set),
  X ~ ■ ∈ᵃ ⌈ θ ⌉ᵃ ->
  X ~ ■ ∈ᵈ θ.  
Proof.
  intros. induction θ; auto.
  - destruct a; destruct d; simpl in *; try inversion H; auto; 
      destruct_binds; eauto.
Qed.

Lemma binds_tvar_ss_binds_ss_to_denv : forall X b θ,
  b = □ \/ b = ■ ->
  binds X b θ ->
  binds X b (⌈ θ ⌉ᵈ).
Proof.
  intros. induction θ; auto.
  - destruct a; destruct d; simpl in *; try inversion H0; destruct_binds; eauto.
    + inversion H; dependent destruction H0.
Qed.

Lemma binds_tvar_ss_binds_ss_to_aenv : forall X θ,
  X ~ □ ∈ᵈ θ ->
  X ~ □ ∈ᵃ ⌈ θ ⌉ᵃ.
Proof.
  intros. induction θ; auto.
  - destruct a; destruct d; simpl in *; try inversion H0; 
    auto; destruct_binds; eauto.
Qed.

Lemma binds_stvar_ss_binds_ss_to_aenv : forall X θ,
  X ~ ■ ∈ᵈ θ -> 
  X ~ ■ ∈ᵃ ⌈ θ ⌉ᵃ.
Proof.
  intros. induction θ; auto.
  - destruct a; destruct d; simpl in *; try inversion H0; 
    auto; destruct_binds; eauto.
Qed.

#[global] Hint Resolve wf_ss_uniq : core.

Lemma wf_ss_notin_remaining : forall θ1 θ2 X b,
  wf_ss (θ2 ++ (X , b) :: θ1) ->
  X ∉ dom (θ2 ++ θ1).
Proof.
  intros. induction θ2; simpl in *; auto.
  - dependent destruction H; auto.
  - destruct a; destruct d; simpl in *; dependent destruction H; auto.  
Qed.

Lemma wf_ss_etvar_same_denv: forall θ θ' X T,
  ss_to_denv (θ' ++ θ) = ss_to_denv (θ' ++ (X, dbind_typ T) :: θ).
Proof.
  intros. induction θ'.
  - auto.
  - destruct a. destruct d; auto; simpl; now rewrite IHθ'.
Qed.

Lemma wf_ss_binds_mono_typ : forall θ X T,
  wf_ss θ ->
  X ~ T ∈ᵈ θ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ T.
Proof.
  intros. induction H; auto.
  - inversion H0.
  - inversion H0.
    + inversion H2.
    + simpl. rewrite_env ((X0 ~ □) ++ ss_to_denv θ).
      apply d_mono_typ_weaken_app. apply IHwf_ss; auto.
  - inversion H0.
    + inversion H2.
    + simpl. rewrite_env ((X0 ~ ■) ++ ss_to_denv θ).
      apply d_mono_typ_weaken_app. apply IHwf_ss; auto.
  - inversion H0.
    + dependent destruction H3. simpl. auto. 
    + simpl. apply IHwf_ss; auto.
Qed.

Lemma wf_ss_binds_typ_lc : forall θ X T,
  wf_ss θ ->
  X ~ T ∈ᵈ θ ->
  lc_typ T.
Proof.
  intros.
  eapply d_mono_typ_lc; eapply wf_ss_binds_mono_typ; eauto.
Qed.

Lemma wf_ss_binds_wf_typ : forall θ X T,
  wf_ss θ -> 
  X ~ T ∈ᵈ θ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈ T.
Proof.
  intros. apply d_mono_typ_d_wf_typ. eapply wf_ss_binds_mono_typ; eauto.
Qed.

Lemma wf_ss_strengthen_app : forall θ1 θ2,
  wf_ss (θ2 ++ θ1) ->
  wf_ss θ1.
Proof.
  intros. induction θ2; auto.
  - destruct a; destruct d; dependent destruction H; auto.
Qed.

Lemma wf_ss_weaken_tvar: forall θ1 θ2 X,
  wf_ss (θ2 ++ θ1) ->
  X ∉ dom (θ2 ++ θ1) ->
  wf_ss (θ2 ++ (X, dbind_tvar_empty) :: θ1).
Proof with auto.
  intros. induction θ2; simpl in *...
  - destruct a; destruct d; simpl in *...
    + dependent destruction H... 
    + dependent destruction H...
    + dependent destruction H... econstructor...
      autorewrite with core in *; simpl.
      rewrite_env (ss_to_denv θ2 ++ (X ~ □) ++ ss_to_denv θ1).
      apply d_mono_typ_weaken...
Qed.

Lemma wf_ss_weaken_stvar: forall θ1 θ2 X,
  wf_ss (θ2 ++ θ1) ->
  X ∉ dom (θ2 ++ θ1) ->
  wf_ss (θ2 ++ (X, ■) :: θ1).
Proof with auto.
  intros. induction θ2; simpl in *...
  - destruct a; destruct d; simpl in *...
    + dependent destruction H... 
    + dependent destruction H...
    + dependent destruction H... econstructor...
      autorewrite with core in *; simpl.
      rewrite_env (ss_to_denv θ2 ++ (X ~ ■) ++ ss_to_denv θ1).
      apply d_mono_typ_weaken...
Qed.

Lemma wf_ss_weaken_etvar: forall θ θ' T X,
  wf_ss (θ' ++ θ) ->
  d_mono_typ (ss_to_denv θ) T ->
  X ∉ dom (θ' ++ θ) ->
  wf_ss (θ' ++ (X, dbind_typ T) :: θ).
Proof with auto.
  intros. induction θ'.
  - simpl in *. constructor...
  - destruct a. destruct d; simpl in *.
    + dependent destruction H. econstructor...
    + dependent destruction H. econstructor...
    + dependent destruction H. econstructor...
      rewrite <- wf_ss_etvar_same_denv...
Qed.

Lemma in_ss_denv_in_ss : forall X b θ,
  binds X b (⌈ θ ⌉ᵈ) ->
  binds X b θ.
Proof with auto.
  intros. induction θ...
  - destruct a. destruct d...
    + inversion H... 
      dependent destruction H0...
    + inversion H... 
      dependent destruction H0...
Qed.

Lemma wf_ss_strengthen_etvar: forall θ1 θ2 T X,
  wf_ss (θ2 ++ (X, dbind_typ T) :: θ1) ->
  wf_ss (θ2 ++ θ1).
Proof.
  intros.
  induction θ2; auto.
  - dependent destruction H; auto.
  - destruct a; destruct d; simpl; dependent destruction H; 
    try constructor; auto.
    rewrite <- wf_ss_etvar_same_denv in H1. auto.
Qed.

Lemma wf_ss_etvar_tvar : forall θ1 θ2 T X,
  wf_ss (θ2 ++ (X, dbind_typ T) :: θ1) ->
  wf_ss (θ2 ++ (X, □) :: θ1).
Proof with auto.
  intros. induction θ2; simpl in *.
  - dependent destruction H...
  - destruct a. destruct d.
    dependent destruction H...
    dependent destruction H...
    dependent destruction H...
    econstructor...
    rewrite <- wf_ss_etvar_same_denv in H1.
    autorewrite with core in *; simpl in *.
    rewrite_env (ss_to_denv θ2 ++ (X ~ □) ++ ss_to_denv θ1).
    apply d_mono_typ_weaken...
Qed.

Lemma wf_ss_typ_no_etvar: forall θ X A T,
  wf_ss θ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈ A ->
  X ~ T ∈ᵈ θ ->
  X ∉ ftvar_in_typ A.
Proof with eauto.
  intros. dependent induction H0...
  + destruct (X == X0)...
    subst. apply in_ss_denv_in_ss in H0.
    unify_binds.
  + destruct (X == X0)...
    subst. apply in_ss_denv_in_ss in H0.
    unify_binds.
  + inst_cofinites_by (L `union` dom θ `union` singleton X) using_name X.
    simpl.
    rewrite ftvar_in_typ_open_typ_wrt_typ_lower.
    eapply H1 with (θ:=(X0 ~ dbind_tvar_empty ++ θ))...
    econstructor...
Qed.

Corollary etvar_bind_no_etvar: forall θ X1 X2 A1 A2,
  wf_ss θ ->
  X1 ~ A1 ∈ᵈ θ ->
  X2 ~ A2 ∈ᵈ θ ->
  X1 ∉ ftvar_in_typ A2.
Proof with eauto.
  intros; eapply wf_ss_typ_no_etvar...
  eapply wf_ss_binds_wf_typ...
Qed.

#[local] Hint Resolve wf_ss_uniq : core.

Lemma trans_wl_not_in_ss : forall θ Γ Ω X,
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  X ∉ dom (awl_to_aenv Γ) ->
  X ∉ dom θ.
Proof with auto.
  intros. dependent induction H; simpl in *...
Qed.

Lemma trans_wl_wf_ss : forall θ θ' Γ Ω,  
  θ ⊩ Γ ⇝ Ω ⫣ θ' -> wf_ss θ'.
Proof with eauto.
  intros. dependent induction H; auto.
Qed.

Lemma trans_typ_wf_ss : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  wf_ss θ.
Proof with auto.
  intros. induction H...
  - inst_cofinites_by L.
    dependent destruction H1...
Qed.

Lemma trans_typ_lc_atyp : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  lc_typ Aᵃ.
Proof with auto.
  intros. induction H...
Qed.

Lemma trans_typ_lc_dtyp : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  lc_typ Aᵈ.
Proof with auto.
  intros. induction H...
  eapply wf_ss_binds_typ_lc; eauto.
Qed.

Lemma trans_exp_lc_aexp : forall θ eᵃ eᵈ,
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  lc_exp eᵃ.
Proof.
  intros. induction H; auto. 
  - inst_cofinites_by L using_name X.   
    apply lc_exp_tabs_exists with (X1:=X). 
    econstructor; eauto using trans_typ_lc_atyp.
  - constructor; auto.
    eapply trans_typ_lc_atyp; eauto.
  - constructor; auto.
    eapply trans_typ_lc_atyp; eauto.
Qed.

Lemma trans_exp_lc_dexp : forall θ eᵃ eᵈ,
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  lc_exp eᵈ.
Proof.
  intros. induction H; auto. 
  - inst_cofinites_by L using_name X.   
    apply lc_exp_tabs_exists with (X1:=X).
    econstructor; eauto using trans_typ_lc_dtyp.
  - constructor; auto.
    eapply trans_typ_lc_dtyp; eauto.
  - constructor; auto.
    eapply trans_typ_lc_dtyp; eauto.
Qed.

#[local] Hint Resolve trans_typ_wf_ss : core.
#[local] Hint Resolve trans_typ_lc_atyp trans_typ_lc_dtyp : core.


Lemma trans_typ_neq_all : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  neq_all Aᵃ -> 
  neq_all Aᵈ.
Proof.
  intros. dependent destruction H0; dependent destruction H; eauto.
  + apply wf_ss_binds_mono_typ in H0; auto.
    eapply d_mono_typ_neq_all. eauto.
Qed.

Lemma trans_typ_neq_all_rev : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  neq_all Aᵈ -> 
  neq_all Aᵃ.
Proof.
  intros. dependent destruction H0; dependent destruction H; eauto.
Qed.

Lemma trans_typ_neq_union_rev : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  neq_union Aᵈ ->
  neq_union Aᵃ.
Proof.
  intros. dependent destruction H0; dependent destruction H; eauto.
Qed.

Lemma trans_typ_neq_intersection_rev : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  neq_intersection Aᵈ -> 
  neq_intersection Aᵃ.
Proof.
  intros. dependent destruction H0; dependent destruction H; eauto.
Qed.

#[export] Hint Resolve 
  trans_typ_neq_all trans_typ_neq_all_rev 
  trans_typ_neq_union_rev trans_typ_neq_intersection_rev
  : core.
  

Lemma trans_typ_det : forall θ Aᵃ A₁ᵈ A₂ᵈ,
  uniq θ -> 
  θ ᵗ⊩ Aᵃ ⇝ A₁ᵈ -> 
  θ ᵗ⊩ Aᵃ ⇝ A₂ᵈ -> 
  A₁ᵈ = A₂ᵈ.
Proof with eauto.
  intros * Huniq Htrans1 Htrans2. generalize dependent A₂ᵈ.
  induction Htrans1; (intros A₂ᵈ Htrans2; dependent destruction Htrans2; auto; try solve unify_binds).
  - unify_binds. auto.
  - apply f_equal2... 
  - inst_cofinites_by (L `union` L0 `union` (ftvar_in_typ A1ᵈ) `union` (ftvar_in_typ A1ᵈ0) `union`  dom θ) using_name X.  
    apply f_equal.
    + eapply open_typ_wrt_typ_inj with (X1:=X); auto.
  - apply f_equal2... 
  - apply f_equal2...
Qed.

Ltac unify_trans_typ :=
  match goal with
  | H_1 : trans_typ ?θ ?Aᵃ ?A1ᵈ, H_2 : trans_typ ?θ ?Aᵃ ?A2ᵈ |- _ => eapply trans_typ_det with (A₁ᵈ:=A1ᵈ) in H_2; 
      eauto; subst
  end.

  Lemma trans_exp_det : forall θ eᵃ e₁ᵈ e₂ᵈ,
  uniq θ -> 
  θ ᵉ⊩ eᵃ ⇝ e₁ᵈ -> 
  θ ᵉ⊩ eᵃ ⇝ e₂ᵈ -> 
  e₁ᵈ = e₂ᵈ.
Proof with eauto.
  intros * Huniq Htrans1 Htrans2. generalize dependent e₂ᵈ.
  induction Htrans1; (intros; dependent destruction Htrans2; auto).
  - inst_cofinites_by (L `union` L0 `union` (fvar_in_exp eᵈ) `union` (fvar_in_exp eᵈ0) `union`  dom θ) using_name x.
    apply f_equal.
    eapply open_exp_wrt_exp_inj with (x1:=x); auto.  
  - apply f_equal2...
  - pick fresh X. inst_cofinites_with X.
    apply f_equal.
    apply f_equal2.
    + eapply open_exp_wrt_typ_inj with (X1:=X); auto.
    + eapply open_typ_wrt_typ_inj with (X1:=X); auto. unify_trans_typ.
  - apply f_equal2... unify_trans_typ.
  - apply f_equal2... unify_trans_typ.
 Qed.

Ltac unify_trans_exp :=
  match goal with
  | H_1 : trans_exp ?θ ?eᵃ ?e1ᵈ, H_2 : trans_exp ?θ ?eᵃ ?e2ᵈ |- _ => eapply trans_exp_det in H_1; 
      eauto; subst
  end.

Lemma trans_conts_det : forall θ csᵃ cs₁ᵈ cs₂ᵈ,
  uniq θ -> 
  θ ᶜˢ⊩ csᵃ ⇝ cs₁ᵈ -> 
  θ ᶜˢ⊩ csᵃ ⇝ cs₂ᵈ -> 
  cs₁ᵈ = cs₂ᵈ
with trans_contd_det : forall θ cdᵃ cd₁ᵈ cd₂ᵈ,
  uniq θ -> 
  θ ᶜᵈ⊩ cdᵃ ⇝ cd₁ᵈ -> 
  θ ᶜᵈ⊩ cdᵃ ⇝ cd₂ᵈ -> 
  cd₁ᵈ = cd₂ᵈ.
Proof with eauto.
  - intros. generalize dependent cs₂ᵈ.
    induction H0; (intros cs₂ᵈ Htrans2; dependent destruction Htrans2).
    + apply f_equal...
    + apply f_equal2... unify_trans_typ.
    + apply f_equal3; repeat unify_trans_typ. 
    + apply f_equal2... unify_trans_typ.
    + apply f_equal. unify_trans_typ.
  - intros. generalize dependent cd₂ᵈ.
    induction H0; (intros cd₂ᵈ Htrans2; dependent destruction Htrans2).
    + apply f_equal2... unify_trans_exp.
    + apply f_equal2... unify_trans_typ.
    + apply f_equal3; repeat unify_trans_typ.
Qed.

Ltac unify_trans_contd :=
  match goal with
  | H_1 : trans_contd ?θ ?cdᵃ ?cd1ᵈ, H_2 : trans_contd ?θ ?cdᵃ ?cd2ᵈ |- _ => eapply trans_contd_det in H_1; 
      eauto; subst
  end.

Ltac unify_trans_conts :=
  match goal with
  | H_1 : trans_conts ?θ ?csᵃ ?cs1ᵈ, H_2 : trans_conts ?θ ?csᵃ ?cs2ᵈ |- _ => eapply trans_conts_det in H_1; 
      eauto; subst
  end.

Lemma trans_wl_split_ss : forall Γ Ω θ θ', 
  θ ⊩ Γ ⇝ Ω ⫣ θ' ->
  exists θ'', θ' = θ'' ++ θ.
Proof.  
  intros. induction H; eauto.
  - exists (@nil (atom * dbind)); auto.
  - destruct IHtrans_worklist as [θ''].
    exists ((X, □) :: θ''). rewrite H1. auto.
  - destruct IHtrans_worklist as [θ''].
    exists ((X, ■) :: θ''). rewrite H1. auto.
  - destruct IHtrans_worklist as [θ''].
    exists ((X, dbind_typ T):: θ''). rewrite H2. auto.
Qed.

Open Scope dworklist.

Lemma trans_wl_split : forall Γ1 Γ2 Ω θ θ',
  θ ⊩ (Γ2 ⧺ Γ1) ⇝ Ω ⫣ θ' ->
  exists Ω1 Ω2 θ'', 
    Ω =  Ω2 ⧺ Ω1 /\ 
    θ  ⊩ Γ1 ⇝ Ω1 ⫣ θ'' /\ 
    θ'' ⊩ Γ2 ⇝ Ω2 ⫣ θ'.
Proof.
  induction Γ2; simpl; intros.
  - exists Ω. exists dworklist_empty. exists θ'.
    simpl; repeat split; auto.
    econstructor. eapply trans_wl_wf_ss; eauto.
  - inversion H; subst.
    + pose proof (IHΓ2 _ _ _ H6) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, (X ~ᵈ □ ;ᵈ Ω2), Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2 _ _ _ H6) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, (X ~ᵈ ■ ;ᵈ Ω2), Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2 _ _ _ H6) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, (X ~ᵈ A1ᵈ ;ᵈ Ω2), Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2 _ _ _ H4) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, Ω2, Θ0.
      subst. repeat split; eauto.
  - inversion H; subst.
    pose proof (IHΓ2 _ _ _ H3) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
    exists Ω1, (wᵈ ⫤ᵈ Ω2), Θ0.
    subst. repeat split; eauto.
Qed.

Lemma trans_wl_app : forall Γ1 Γ2 Ω1 Ω2 θ1 θ2 θ3,
  θ1 ⊩ Γ1 ⇝ Ω1 ⫣ θ2 ->
  θ2 ⊩ Γ2 ⇝ Ω2 ⫣ θ3 -> 
  θ1 ⊩ Γ2 ⧺ Γ1 ⇝ Ω2 ⧺ Ω1 ⫣ θ3.
Proof.
  intros.
  induction H0; simpl; try solve [eauto].
Qed.

Lemma trans_wl_a_wl_binds_etvar_ss : forall Γ X Ω θ θ',
  θ ⊩ Γ ⇝ Ω ⫣ θ' ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  exists T, X ~ T ∈ᵈ θ'.
Proof with eauto.
  intros. dependent induction H.
  - inversion H0.
  - auto...
  - inversion H1. inversion H2; subst...
    apply IHtrans_worklist in H2...
    destruct H2 as [T]. exists T...
  - inversion H1. inversion H2; subst...
    apply IHtrans_worklist in H2...
    destruct H2 as [T]. exists T...
  - inversion H1. inversion H2; subst...
    apply IHtrans_worklist in H2...
  - inversion H2. inversion H3; subst...
    apply IHtrans_worklist in H3...
    destruct H3 as [T']. exists T'...
Qed.

Lemma trans_wl_a_wl_binds_tvar_ss : forall Γ X Ω θ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ □ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X ~ □ ∈ᵈ θ.
Proof with eauto.
  intros. dependent induction H; destruct_binds...
Qed.

Lemma trans_wl_a_wl_binds_tvar_d_wl : forall Γ X Ω θ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ □ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X ~ □ ∈ᵈ ⌊ Ω ⌋ᵈ.
Proof with eauto.
  intros. dependent induction H; destruct_binds...
Qed.

Lemma trans_wl_ss_binds_tvar_a_wl : forall θ Γ Ω X,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ □ ∈ᵈ θ ->
  X ~ □ ∈ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  intros. dependent induction H; destruct_binds; auto.
Qed. 

Lemma trans_wl_ss_binds_stvar_a_wl : forall θ Γ Ω X,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ ■ ∈ᵈ θ ->
  X ~ ■ ∈ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  intros. dependent induction H; destruct_binds; auto.
Qed. 

Lemma trans_wl_ss_binds_etvar_a_wl : forall θ Γ Ω X T,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ T ∈ᵈ θ ->
  X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ.
Proof.
  intros. dependent induction H; eauto.
  - inversion H1; simpl in *.
    + dependent destruction H2.
    + apply binds_cons; auto.
  - inversion H1; simpl in *.
    + dependent destruction H2.
    + apply binds_cons; auto. 
  - simpl.
    + apply binds_cons; auto.
  - inversion H2; simpl in *.
    + dependent destruction H3. auto.
    + apply binds_cons; auto.
Qed. 

Lemma trans_wl_a_wl_binds_stvar_ss : forall Γ X Ω θ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ ■ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  X ~ ■ ∈ᵈ θ.
Proof with eauto.
  intros. dependent induction H; destruct_binds...
Qed.

Lemma trans_wl_a_wl_binds_stvar_d_wl : forall Γ X Ω θ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  binds X abind_stvar_empty (awl_to_aenv Γ) ->
  binds X dbind_stvar_empty (dwl_to_denv Ω).
Proof with eauto.
  intros. dependent induction H; destruct_binds...
Qed.

Lemma trans_wl_d_wl_binds_tvar_ss : forall Γ X Ω θ θ',
  θ ⊩ Γ ⇝ Ω ⫣ θ' ->
  X ~ □ ∈ᵈ ⌊ Ω ⌋ᵈ ->
  X ~ □ ∈ᵈ ⌈ θ' ⌉ᵈ.
Proof with eauto.
  intros. dependent induction H; destruct_binds...
  - inversion H0.
Qed.

Lemma trans_wl_d_wl_binds_stvar_ss : forall Γ X Ω θ θ',
  θ ⊩ Γ ⇝ Ω ⫣ θ' ->
  X ~ ■ ∈ᵈ ⌊ Ω ⌋ᵈ -> 
  X ~ ■ ∈ᵈ ⌈ θ' ⌉ᵈ.
Proof with eauto.
  intros. dependent induction H; destruct_binds...
  - inversion H0.
Qed.

Lemma trans_wl_d_wl_mono_typ_ss_mono_typ : forall θ θ' Γ Ω T,
  θ ⊩ Γ ⇝ Ω ⫣ θ' ->
  d_mono_typ (dwl_to_denv Ω) T -> 
  d_mono_typ (ss_to_denv θ') T.
Proof.
  intros. dependent induction H0; eauto.
  - constructor. eapply trans_wl_d_wl_binds_tvar_ss; eauto.
Qed.

Lemma trans_wl_ss_mono_typ_d_wl_mono_typ : forall θ Γ Ω T,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ T -> 
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈₘ T.
Proof.
  intros. dependent induction H0; eauto.
  - constructor. eapply trans_wl_a_wl_binds_tvar_d_wl; eauto.
    eapply trans_wl_ss_binds_tvar_a_wl; eauto.
    apply binds_ss_to_denv_binds_ss. auto.
Qed.

Lemma wf_ss_uniq_ss_to_denv : forall θ,
  wf_ss θ -> uniq (ss_to_denv θ).
Proof.
  intros. induction H; simpl; auto.
  - constructor; auto. rewrite dom_ss_to_denv_upper; auto.
  - constructor; auto. rewrite dom_ss_to_denv_upper; auto.
Qed.

Lemma wf_ss_rename_tvar : forall θ1 θ2 X X',
  wf_ss (θ2 ++ (X, □) :: θ1) ->
  X' ∉ dom (θ2 ++ θ1) ->
  wf_ss (map (subst_typ_in_dbind ` X' X) θ2 ++ (X', □) :: θ1).
Proof with eauto.
  intros. induction θ2; simpl in *...
  - inversion H; subst...
  - dependent destruction a.
    inversion H; subst...
    econstructor...
    replace (ss_to_denv (map (subst_typ_in_dbind ` X' X) θ2 ++ (X', □) :: θ1))
        with ((map (subst_typ_in_dbind ` X' X) (ss_to_denv θ2) ++ (X', □) :: (ss_to_denv θ1))).
    + simpl. apply d_mono_typ_rename_tvar...
      * replace (ss_to_denv θ2 ++ X ~ □ ++ ss_to_denv θ1) with (ss_to_denv (θ2 ++ (X, □) :: θ1))...
        apply wf_ss_uniq_ss_to_denv...
        autorewrite with core in *...
      * rewrite dom_app. repeat rewrite dom_ss_to_denv_upper...
      * rewrite ss_to_denv_app in *...
    + rewrite ss_to_denv_app. rewrite ss_to_denv_subst_typ_in_dbind_comm...
Qed.

Ltac destruct_mono_arrow :=
  repeat
    lazymatch goal with
    | H : d_mono_typ ?θ (typ_arrow ?A1 ?A2) |- _ => dependent destruction H
    | H : a_mono_typ ?θ (typ_arrow ?A1 ?A2) |- _ => dependent destruction H
    end. 

Ltac solve_binds_mono :=
  repeat
    match goal with
      | H1 : binds ?X (dbind_typ ?T) ?θ , H2 : wf_ss ?θ |- _ =>
        match goal with
          | H1 : d_mono_typ (ss_to_denv θ) T |- _ => fail 1
          | _ =>
            let Hmono := fresh "Hmono" in
            apply wf_ss_binds_mono_typ in H1 as Hmono; auto
        end
    end;
  destruct_mono_arrow.

Ltac solve_binds_nonmono_contradiction :=
  solve_binds_mono; 
  match goal with
    | H1 : d_mono_typ ?θ typ_bot |- _ => inversion H1
    | H1 : d_mono_typ ?θ typ_top |- _ => inversion H1
    | H1 : d_mono_typ ?θ (typ_all ?A) |- _ => inversion H1
    | H1 : d_mono_typ ?θ (typ_intersection ?A1 ?A2) |- _ => inversion H1
    | H1 : d_mono_typ ?θ (typ_union ?A1 ?A2) |- _ => inversion H1
  end.

Lemma trans_typ_dtvar_atyp_s_in_dtyp : forall θ X Aᵃ Aᵈ b,
  b = □ \/ b = ■ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  binds X b θ ->
  s_in X Aᵃ ->
  s_in X Aᵈ.
Proof.
  intros. induction H0; try dependent destruction H2; auto.
  - exfalso. dependent destruction H; subst; unify_binds.
  - econstructor; eauto.
  - eapply s_in__arrow2; auto. 
    eapply trans_typ_lc_dtyp; eauto.
  - eapply s_in__all with (L:=L `union` L0).
    intros. inst_cofinites_with Y.
    apply H4... apply binds_cons; auto.
    auto.
Qed.

Lemma trans_typ_wf_dtyp : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈ Aᵈ.
Proof with eauto.
  intros. induction H...
  - constructor; auto.
    eapply binds_tvar_ss_binds_ss_to_denv...
  - apply d_wf_typ__stvar.
    eapply binds_tvar_ss_binds_ss_to_denv...
  - eapply wf_ss_binds_wf_typ...
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X...
    simpl in *.
    eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=□) (Aᵃ:=A1ᵃ ᵗ^ₜ X); eauto.
Qed.

Lemma trans_typ_wf_atyp : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌈ θ ⌉ᵃ ᵗ⊢ᵃ Aᵃ.
Proof with eauto.
  intros. induction H...
  - constructor; auto.
    eapply binds_tvar_ss_binds_ss_to_aenv...
  - apply a_wf_typ__stvar.
    eapply binds_stvar_ss_binds_ss_to_aenv...
  - apply a_wf_typ__etvar.
    eapply binds_ss_etvar_binds_ss_to_aenv...
Qed.

Lemma trans_typ_dtvar_dtyp_s_in_atyp : forall θ X Aᵃ Aᵈ b,
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  binds X b θ ->
  (forall Y T, Y ~ T ∈ᵈ θ -> Y `in` ftvar_in_typ Aᵃ -> X `in` ftvar_in_typ T -> False) ->
  s_in X Aᵈ ->
  s_in X Aᵃ.
Proof.
  intros. induction H0; try dependent destruction H3; auto.
  - exfalso. eapply H2; eauto; simpl in *; fsetdec. 
  - exfalso. eapply H2; eauto; simpl in *. fsetdec.
    apply sin_in in H5. fsetdec.
  - exfalso. eapply H2; eauto; simpl in *. fsetdec. 
    apply sin_in in H5. fsetdec.
  - solve_binds_nonmono_contradiction.
  - exfalso. eapply H2; eauto; simpl in *. fsetdec. 
    apply sin_in in H3_. fsetdec. 
  - exfalso. eapply H2; eauto; simpl in *. fsetdec. 
    apply sin_in in H3_. fsetdec. 
  - eapply s_in__arrow1; eauto.
    apply IHtrans_typ1; auto.
    intros. eapply H2; simpl; eauto. 
  - eapply s_in__arrow2; eauto.
    apply IHtrans_typ2; auto.
    intros. eapply H2; simpl; eauto. 
  - inst_cofinites_for s_in__all.
    intros. inst_cofinites_with Y.
    apply H5; auto. intros. destruct_binds.
    eapply H2; eauto.
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H8.
    apply union_iff in H8. inversion H8.
    + assert (wf_ss ((Y, □) :: θ)) by eauto. 
      dependent destruction  H10.
      apply singleton_iff in H7. subst.
      apply binds_dom_contradiction in H11; eauto. contradiction.
    + auto.
  - simpl in *; eauto.
    constructor; eauto.
  - simpl in *; eauto.
    constructor; eauto.  
Qed.

Lemma d_mono_typ_ftvar_in_typ_upper : forall Ψ T,
  d_mono_typ Ψ T ->
  ftvar_in_typ T [<=] dom Ψ.
Proof.
  intros. induction H; simpl; try fsetdec.
  - apply binds_In in H. fsetdec.
Qed.

Lemma ss_to_denv_dom_upper : forall θ,
  dom (ss_to_denv θ) [<=] dom θ.
Proof.
  intros. induction θ; simpl; try fsetdec.
  destruct a; destruct d; simpl; fsetdec.
Qed.

Lemma wf_ss_ftvar_in_typ_upper : forall θ X T,
  wf_ss θ ->
  binds X (dbind_typ T) θ ->
  ftvar_in_typ T [<=] dom θ. 
Proof.
  intros. induction H.
  - inversion H0.
  - destruct_binds. rewrite IHwf_ss; auto. fsetdec.
  - destruct_binds. rewrite IHwf_ss; auto. fsetdec. 
  - destruct_binds. 
    + apply d_mono_typ_ftvar_in_typ_upper in H2. rewrite ss_to_denv_dom_upper in H2. fsetdec.
    + rewrite IHwf_ss; auto. fsetdec.
Qed.

Lemma wf_ss_ftvar_in_dbind_upper : forall θ X b,
  wf_ss θ ->
  binds X b θ ->
  ftvar_in_dbind b [<=] dom θ. 
Proof.
  intros. destruct b; simpl; try fsetdec. 
  eapply wf_ss_ftvar_in_typ_upper; eauto.
Qed.
  

Lemma ss_binds_rename_tvar : forall θ1 θ2 X X' Y b,
  wf_ss (θ2 ++ (X, □) :: θ1) ->
  binds X' b (θ2 ++ (X, □) :: θ1) ->
  X' <> X ->
  binds X' (subst_typ_in_dbind (` Y) X b) (map (subst_typ_in_dbind (`Y) X) θ2 ++ (Y, □) :: θ1).
Proof with eauto.
  intros. induction θ2.
  - simpl in *. destruct_binds; auto.
    dependent destruction H.
    rewrite <- wf_ss_ftvar_in_dbind_upper in H0; eauto.
    rewrite subst_typ_in_dbind_fresh_eq...
  - destruct a as [X0 b0]; destruct b0; destruct_binds; simpl in *; auto.
    + dependent destruction H...  
    + dependent destruction H...
    + dependent destruction H...
Qed.

Lemma trans_typ_rename_tvar : forall θ1 θ2 Aᵃ Aᵈ X X', 
  θ2 ++ (X, □) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X' ∉ dom (θ2 ++ θ1) ->
  map (subst_typ_in_dbind (` X') X) θ2  ++ (X', □) :: θ1 ᵗ⊩ {` X' ᵗ/ₜ X} Aᵃ ⇝ {` X' ᵗ/ₜ X} Aᵈ.
Proof with eauto using wf_ss_rename_tvar.
  intros. dependent induction H; simpl; auto...
  - destruct_eq_atom... 
    + econstructor...
      eapply ss_binds_rename_tvar in H0; eauto.
  - destruct_eq_atom... 
    + eapply trans_typ__stvar...
      eapply ss_binds_rename_tvar with (Y:=X') in H0; eauto.
  - destruct_eq_atom... 
    + assert (X ~ □ ∈ᵈ (θ2 ++ (X, □) :: θ1)) by auto.
      unify_binds.
    + econstructor... 
      eapply ss_binds_rename_tvar with (Y:=X') in H0; eauto.
  - inst_cofinites_for trans_typ__all;
    intros; inst_cofinites_with X0... 
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
      rewrite_env (map (subst_typ_in_dbind ` X' X) ((X0, □) :: θ2) ++ (X', □) :: θ1).
      eapply H1...
Qed.

Corollary trans_typ_rename_tvar_cons : forall θ Aᵃ Aᵈ X X', 
  (X, □) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X' ∉ dom θ ->
  (X', □) :: θ ᵗ⊩ {` X' ᵗ/ₜ X} Aᵃ ⇝ {` X' ᵗ/ₜ X} Aᵈ.
Proof.
  intros. 
  rewrite_env (map (subst_typ_in_dbind (` X') X) nil  ++ (X', dbind_tvar_empty) :: θ).
  eapply trans_typ_rename_tvar; auto.
Qed.

#[local] Hint Constructors wf_ss : core.

Lemma wf_ss_stvar_tvar : forall θ1 θ2 X,
  wf_ss (θ2 ++ (X, ■) :: θ1) ->
  wf_ss (θ2 ++ (X, □) :: θ1).
Proof with eauto; autorewrite with core in *.
  intros. dependent induction θ2; eauto; simpl in *...
  - dependent destruction H... 
  - dependent destruction H...
    constructor... simpl in *. 
    apply d_mono_typ_no_stvar in H1 as Hfv; eauto.
    + apply d_mono_typ_stvar_tvar...  
    + replace (ss_to_denv θ2 ++ X ~ ■ ++ ss_to_denv θ1) with (ss_to_denv (θ2 ++ (X, ■) :: θ1)).
      apply wf_ss_uniq_ss_to_denv...
      autorewrite with core in *...
Qed.

Lemma wf_ss_tvar_stvar : forall θ1 θ2 X,
  wf_ss (θ2 ++ (X, □) :: θ1) ->
  (forall Y T, Y ~ T ∈ᵈ (θ2 ++ θ1) -> X ∉ ftvar_in_typ T) ->
  wf_ss (θ2 ++ (X, ■) :: θ1).
Proof with eauto; autorewrite with core in *; simpl.
  intros. dependent induction θ2; eauto; simpl in *...
  - dependent destruction H... 
  - dependent destruction H...
    assert (X0 ~ T ∈ᵈ ((X0, dbind_typ T) :: θ2 ++ θ1)) by auto.
    apply H2 in H3.
    constructor...
    rewrite_env (ss_to_denv θ2 ++ (X ~ ■) ++ ss_to_denv θ1).
    apply d_mono_typ_weaken.
    simpl in *.
    apply d_mono_typ_strengthen in H1...
Qed.

Lemma trans_typ_stvar_tvar_same : forall θ1 θ2 X Aᵃ Aᵈ,
  θ2 ++ (X, ■) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ2 ++ (X, □) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with auto using wf_ss_stvar_tvar.
  intros. dependent induction H; eauto...
  - constructor... eapply binds_remove_mid_diff_bind in H0; eauto.
    + rewrite_env (θ2 ++ (X ~ □) ++ θ1). apply binds_weaken...
    + unfold not; intros; subst. inversion H1.
  - destruct (X0 == X). subst.
    eapply trans_typ__tvar...
    eapply trans_typ__stvar...
    apply binds_remove_mid in H0...
    apply binds_app_iff in H0; inversion H0...
  - eapply trans_typ__etvar... 
    apply binds_remove_mid in H0...
    apply binds_app_iff in H0; inversion H0...
    + assert (X ~ ■ ∈ᵈ (θ2 ++ (X, ■) :: θ1)) by auto. unfold not.
      intros. subst. unify_binds.
  - eapply trans_typ__all with (L:=L);
    intros; inst_cofinites_with X0...
    rewrite_env (((X0, □) :: θ2) ++ (X, □) :: θ1)...
Qed.

Lemma trans_typ_tvar_to_stvar_same : forall θ1 θ2 X Aᵃ Aᵈ,
  θ2 ++ (X, □) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  (forall Y T, Y ~ T ∈ᵈ (θ2 ++ θ1) -> X ∉ ftvar_in_typ T) ->
  θ2 ++ (X, ■) :: θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with auto using wf_ss_tvar_stvar.
  intros. dependent induction H; auto...
  - destruct (X==X0).
    + subst. eapply trans_typ__stvar; eauto...
    + apply binds_remove_mid in H0...
      constructor...
      apply binds_weaken_mid...
  - apply binds_remove_mid_diff_bind in H0.
    eapply trans_typ__stvar; eauto...
    + apply binds_weaken_mid...
    + solve_false.
  - apply binds_remove_mid in H0...
    constructor; eauto...
    + apply binds_weaken_mid...
    + unfold not; intros; subst. 
      assert (X ~ □ ∈ᵈ (θ2 ++ (X, □) :: θ1)) by auto.
      unify_binds.
  - eapply trans_typ__all with (L:=L);
    intros; inst_cofinites_with X0...
    rewrite_env (((X0, □) :: θ2) ++ (X, ■) :: θ1)...
    apply H1...
    intros. destruct_binds; eauto.
Qed.

Corollary trans_typ_tvar_stvar_cons : forall θ X Aᵃ Aᵈ,
  (X, □) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  (X, ■) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof.
  intros. rewrite_env (nil ++ (X, dbind_stvar_empty) :: θ).
  eapply trans_typ_tvar_to_stvar_same; eauto.
  intros. apply trans_typ_wf_ss in H.
  dependent destruction H. simpl in *.
  apply wf_ss_ftvar_in_typ_upper in H1; auto.
Qed.

Corollary trans_typ_stvar_tvar_cons : forall θ X Aᵃ Aᵈ,
  (X, ■) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  (X, □) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof.
  intros. rewrite_env (nil ++ (X, dbind_tvar_empty) :: θ).
  eapply trans_typ_stvar_tvar_same; eauto.
Qed.

#[local] Hint Resolve trans_wl_wf_ss : core.

Lemma trans_exp_rename_var : forall θ eᵃ eᵈ x x', 
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  θ ᵉ⊩ {(exp_var_f x') ᵉ/ₑ x} eᵃ ⇝ {(exp_var_f x') ᵉ/ₑ x} eᵈ.
Proof with auto.
  intros. dependent induction H; simpl; auto...
  - unfold eq_dec. destruct (EqDec_eq_of_X x0 x); subst.
    + econstructor... 
    + econstructor... 
  - eapply trans_exp__abs with (L:=L `union` singleton x). intros.
    inst_cofinites_with x0.
    erewrite subst_exp_in_exp_open_exp_wrt_exp in H0...
    erewrite subst_exp_in_exp_open_exp_wrt_exp in H0...
    simpl in H0...
    unfold eq_dec in H0. destruct (EqDec_eq_of_X x0 x).
    + subst. apply notin_union_2 in H1. apply notin_singleton_1 in H1. contradiction.
    + auto.
  - eapply trans_exp__tabs with (L:=L); intros;
    inst_cofinites_with X...
    + erewrite <- subst_exp_in_exp_open_exp_wrt_typ...
      erewrite <- subst_exp_in_exp_open_exp_wrt_typ...
Qed.

Lemma trans_exp_rename_tvar : forall θ1 θ2 eᵃ eᵈ X X', 
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ᵉ⊩ eᵃ ⇝ eᵈ ->
  X' ∉ dom (θ2 ++ θ1) ->
  map (subst_typ_in_dbind ` X' X) θ2 ++ (X', □) :: θ1 ᵉ⊩ {` X' ᵉ/ₜ X} eᵃ ⇝ {` X' ᵉ/ₜ X} eᵈ.
Proof with auto.
  intros. dependent induction H; simpl in *...
  - constructor...
    eapply wf_ss_rename_tvar; eauto.
  - constructor.
    eapply wf_ss_rename_tvar; eauto.
  - inst_cofinites_for trans_exp__abs.
    intros. inst_cofinites_with x.
    eapply H0 in H1; eauto.
    rewrite subst_typ_in_exp_open_exp_wrt_exp in H1...
    rewrite subst_typ_in_exp_open_exp_wrt_exp in H1...
  - inst_cofinites_for trans_exp__tabs;
    intros; inst_cofinites_with X0.
    + repeat (rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2; eauto).
      rewrite_env (map (subst_typ_in_dbind (` X') X) ((X0, □) :: θ2) ++ (X', □) :: θ1).
      eapply H0; eauto.
    + repeat (rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto).
      rewrite_env (map (subst_typ_in_dbind (` X') X) ((X0, □) :: θ2) ++ (X', □) :: θ1).
      apply trans_typ_rename_tvar; eauto.
  - constructor...
    apply trans_typ_rename_tvar...
  - constructor...
    apply trans_typ_rename_tvar...
Qed.

Lemma trans_exp_rename_tvar_cons : forall θ eᵃ eᵈ X X', 
  (X, □) :: θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  X' ∉ dom θ -> 
  (X', □) :: θ ᵉ⊩ {` X' ᵉ/ₜ X} eᵃ ⇝ {` X' ᵉ/ₜ X} eᵈ.
Proof.
  intros. rewrite_env (map (subst_typ_in_dbind (` X') X) nil ++ (X', □) :: θ). 
    apply trans_exp_rename_tvar; auto.
Qed.

Ltac rewrite_close_open_subst :=
  match goal with
  | H : _ |- context [open_typ_wrt_typ (close_typ_wrt_typ ?X ?A) ?B] =>
      erewrite (subst_typ_in_typ_intro X (close_typ_wrt_typ X A)) by apply close_typ_wrt_typ_notin;
      rewrite open_typ_wrt_typ_close_typ_wrt_typ
  | H : _ |- context [open_exp_wrt_typ (close_exp_wrt_typ ?X ?e) ?B] =>
      erewrite (subst_typ_in_exp_intro X (close_exp_wrt_typ X e)) by apply close_exp_wrt_typ_notin;
      rewrite open_exp_wrt_typ_close_exp_wrt_typ
  | H : _ |- context [open_exp_wrt_exp (close_exp_wrt_exp ?x ?e) ?e'] =>
      erewrite (subst_exp_in_exp_intro x (close_exp_wrt_exp x e)) by apply close_exp_wrt_exp_notin;
      rewrite open_exp_wrt_exp_close_exp_wrt_exp
  | H : _ |- _ => idtac
  end.

Ltac simpl_open_subst_typ' :=
  match goal with
  | H : context [ {?B ᵗ/ₜ ?X} (?A ᵗ^ₜ (?X')) ] |- _ =>
    rewrite subst_typ_in_typ_open_typ_wrt_typ in H; auto;
    simpl in H; try destruct_eq_atom; auto
    (* try solve [rewrite subst_typ_in_typ_fresh_eq in H; auto] *)
  | H1 : context [ {?B ᵗ/ₜ ?X} ?A ], H2 : context [ftvar_in_typ ?A] |- _ =>
      let H := fresh "H" in
      try (
        assert (H : X ∉ ftvar_in_typ A) by auto;
        rewrite subst_typ_in_typ_fresh_eq in H1; auto; clear H)
end.

Ltac  simpl_open_subst_typ :=
  repeat simpl_open_subst_typ'.

Ltac simpl_open_subst_exp' :=
  match goal with
  | H : context [ {?f ᵉ/ₑ ?x} (?e ᵉ^^ₑ (?x')) ] |- _ =>
    rewrite subst_exp_in_exp_open_exp_wrt_exp in H; auto;
    simpl in H; try destruct_eq_atom; auto
    (* try solve [rewrite subst_typ_in_typ_fresh_eq in H; auto] *)
  | H1 : context [ {?f ᵉ/ₑ ?x} ?e ], H2 : context [fvar_in_exp ?e] |- _ =>
      let H := fresh "H" in
      try (
        assert (H : x ∉ fvar_in_exp e) by auto;
        rewrite subst_exp_in_exp_fresh_eq in H1; auto; clear H)
end.

Ltac  simpl_open_subst_exp :=
  repeat simpl_open_subst_exp'.

Ltac solve_trans_typ_open_close' :=
  match goal with
  | H : ?θ ᵗ⊩ ?A1ᵃ ⇝ ?Aᵈ |- ?θ' ᵗ⊩ ?A2ᵃ ⇝ ({(` ?X1') ᵗ/ₜ ?X} ?Aᵈ) => 
      apply trans_typ_rename_tvar_cons with (X':=X1') in H; eauto
  end.

Ltac solve_trans_exp_open_close' :=
  match goal with
  | H : ?θ ᵉ⊩ ?e1ᵃ ⇝ ?eᵈ |- ?θ' ᵉ⊩ ?e2ᵃ ⇝ ({(exp_var_f ?x1') ᵉ/ₑ ?x} ?eᵈ) => 
      eapply trans_exp_rename_var with (x:=x) (x':=x1') in H
  (* | H : ?θ ᵉ⊩ ?e1ᵃ ⇝ ?eᵈ |- ?θ' ᵉ⊩ ?e2ᵃ ⇝ ({(exp_var_f ?x') ᵉ/ₑ ?x} ?eᵈ) => 
      assert (θ ᵉ⊩ e1ᵃ ⇝ eᵈ) by admit *)
  end.

Ltac solve_s_in' :=
  match goal with 
  | H : s_in ?X1 (?A ᵗ^ₜ ?X1) |- s_in ?X (?A ᵗ^ₜ ?X) => 
    eapply s_in_rename with (Y:=X) in H
  end.

Ltac solve_trans_typ_open_close :=
  rewrite_close_open_subst;
  solve_trans_typ_open_close';
  simpl_open_subst_typ.

Ltac solve_trans_exp_open_close :=
  rewrite_close_open_subst;
  solve_trans_exp_open_close';
  simpl_open_subst_exp.

Ltac solve_s_in :=
  solve_s_in';
  simpl_open_subst_typ.

Lemma trans_typ_total : forall θ Γ Ω Aᵃ,
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->  
  (* a_wf_env (awl_to_aenv Γ) ->  *)
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  exists Aᵈ, trans_typ θ Aᵃ Aᵈ.
Proof with eauto.
  intros. 
  generalize dependent Ω. 
  generalize dependent θ. 
  dependent induction H; intros...
  - exists (` X). econstructor... 
    eapply trans_wl_a_wl_binds_tvar_ss...
  - exists (` X). eapply trans_typ__stvar...
    eapply trans_wl_a_wl_binds_stvar_ss...
  - eapply trans_wl_a_wl_binds_etvar_ss in H...
    destruct H as [T].
    exists T...
  - apply IHa_wf_typ1 in H1 as Htrans_typ1...
    apply IHa_wf_typ2 in H1 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_arrow A1ᵈ A2ᵈ). econstructor...  
  - inst_cofinites_by (L `union` dom (awl_to_aenv Γ)  `union` ftvar_in_typ A `union` dom θ) using_name X.
    assert (nil ⊩ (X ~ᵃ □ ;ᵃ Γ) ⇝ (X ~ᵈ □ ;ᵈ Ω) ⫣ (X, □) :: θ) by auto.
    apply H1 in H3...
    destruct H3 as [Axᵈ].
    exists (typ_all (close_typ_wrt_typ X Axᵈ)).
    eapply trans_typ__all with (L:=L `union` dom θ); intros. 
    + solve_s_in.
    + solve_trans_typ_open_close.
  - apply IHa_wf_typ1 in H1 as Htrans_typ1...
    apply IHa_wf_typ2 in H1 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_union A1ᵈ A2ᵈ). econstructor...  
  - apply IHa_wf_typ1 in H1 as Htrans_typ1...
    apply IHa_wf_typ2 in H1 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_intersection A1ᵈ A2ᵈ). econstructor...  
Qed.

Lemma trans_exp_total : forall θ Γ Ω eᵃ,
  a_wf_exp (awl_to_aenv Γ) eᵃ ->  
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  exists eᵈ, trans_exp θ eᵃ eᵈ.
Proof with eauto using trans_typ_total.
  intros. generalize dependent Ω. 
  generalize dependent θ. 
  dependent induction H; intros...
  - pick fresh x. 
    eapply trans_typ_total in H...
    destruct H as [Tᵈ].
    assert ((nil ⊩ (x ~ᵃ T ;ᵃ Γ) ⇝ (x ~ᵈ Tᵈ ;ᵈ Ω) ⫣ θ)) by auto.
    eapply H1 with (θ:=θ) in H3...
    destruct H3 as [eᵈ].
    exists (exp_abs (close_exp_wrt_exp x eᵈ)). 
    inst_cofinites_for trans_exp__abs. intros.
    solve_trans_exp_open_close.
  - assert ((exists e1ᵈ, θ ᵉ⊩ e1 ⇝ e1ᵈ) -> (exists e2ᵈ, θ ᵉ⊩ e2 ⇝ e2ᵈ) -> exists eᵈ , θ ᵉ⊩ exp_app e1 e2 ⇝ eᵈ). {
      intros. destruct_conj...
    }
    apply H2...
  - pick fresh X; inst_cofinites_with X.
    assert (nil ⊩ (X ~ᵃ □ ;ᵃ Γ) ⇝ (X ~ᵈ □ ;ᵈ Ω) ⫣ (X, □) :: θ) by auto.
    replace (X ~ □ ++ ⌊ Γ ⌋ᵃ )%abind with (⌊ X ~ᵃ □ ;ᵃ Γ ⌋ᵃ) in * by auto.
    (* eapply trans_typ_total in H0... *)
    eapply H1 in H3...
    destruct H3 as [eᵈ]. dependent destruction H3... 
    exists (exp_tabs (exp_anno (close_exp_wrt_typ X eᵈ) (close_typ_wrt_typ X A1ᵈ))).
    inst_cofinites_for trans_exp__tabs; intros.
    + rewrite_close_open_subst. apply trans_exp_rename_tvar_cons with (X':=X0) in H3; eauto.
      rewrite subst_typ_in_exp_open_exp_wrt_typ in H3... simpl in H3. destruct_eq_atom...
      rewrite subst_typ_in_exp_fresh_eq in H3...
    + rewrite_close_open_subst. apply trans_typ_rename_tvar_cons with (X':=X0) in H4; eauto.
      rewrite subst_typ_in_typ_open_typ_wrt_typ in H4... simpl in H4. destruct_eq_atom...
      rewrite subst_typ_in_typ_fresh_eq in H4...
  - assert (Hex: (exists eᵈ, θ ᵉ⊩ e ⇝ eᵈ) -> (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> exists eᵈ, θ ᵉ⊩ exp_tapp e A ⇝ eᵈ). {
      intros. destruct_conj...
    } 
    apply Hex...
  - assert (Hex: (exists eᵈ, θ ᵉ⊩ e ⇝ eᵈ) -> (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> exists eᵈ, θ ᵉ⊩ exp_anno e A ⇝ eᵈ). {
      intros. destruct_conj...
    } 
    apply Hex...
Qed.

Lemma trans_conts_total : forall θ Γ Ω csᵃ,
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ csᵃ ->  
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  exists csᵈ, θ ᶜˢ⊩ csᵃ ⇝ csᵈ
with trans_contd_total : forall θ Γ Ω cdᵃ,
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cdᵃ ->  
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  exists cdᵈ, θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ.
Proof with eauto using trans_typ_total, trans_exp_total.
  - intros. clear trans_conts_total.
    generalize dependent Ω. 
    generalize dependent θ. 
    dependent induction H; intros...
    + assert (Hex: (exists cdᵈ, θ ᶜᵈ⊩ cd ⇝ cdᵈ) -> exists csᵈ, θ ᶜˢ⊩ conts_infabs cd ⇝ csᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
    + assert (Hex: (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> (exists csᵈ, θ ᶜˢ⊩ cs ⇝ csᵈ) -> 
              exists csᵈ, θ ᶜˢ⊩ conts_inftapp A cs ⇝ csᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
    + assert (Hex: (exists A1ᵈ, θ ᵗ⊩ A1 ⇝ A1ᵈ) -> (exists A2ᵈ, θ ᵗ⊩ A2 ⇝ A2ᵈ) -> (exists csᵈ, θ ᶜˢ⊩ cs ⇝ csᵈ) ->
              exists csᵈ, θ ᶜˢ⊩ conts_inftappunion A1 A2 cs ⇝ csᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
    + assert (Hex: (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> (exists csᵈ, θ ᶜˢ⊩ cs ⇝ csᵈ) ->
        exists csᵈ, θ ᶜˢ⊩ conts_unioninftapp A cs ⇝ csᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
    + assert (Hex: (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> exists csᵈ, θ ᶜˢ⊩ conts_sub A ⇝ csᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
  - intros. clear trans_contd_total.
    generalize dependent Ω. 
    generalize dependent θ. 
    dependent induction H; intros...
    + assert (Hex: (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> (exists cdᵈ, θ ᶜᵈ⊩ cd ⇝ cdᵈ) ->
        exists cdᵈ, θ ᶜᵈ⊩ contd_infabsunion A cd ⇝ cdᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
    + assert (Hex: (exists eᵈ, θ ᵉ⊩ e ⇝ eᵈ) -> (exists csᵈ, θ ᶜˢ⊩ cs ⇝ csᵈ) ->
        exists cdᵈ, θ ᶜᵈ⊩ contd_infapp e cs ⇝ cdᵈ). {
        intros. destruct_conj...
      }
      apply Hex...
    + assert (Hex:  (exists Aᵈ, θ ᵗ⊩ A ⇝ Aᵈ) -> (exists Bᵈ, θ ᵗ⊩ B ⇝ Bᵈ) -> (exists cdᵈ, θ ᶜᵈ⊩ cd ⇝ cdᵈ) ->
        exists cdᵈ, θ ᶜᵈ⊩ contd_unioninfabs A B cd ⇝ cdᵈ). {
        intros. destruct_conj...
      }
      dependent destruction H.
      apply Hex...
Qed.

Lemma trans_wl_wf_bind_typ : forall Γ Ω θ X T,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  X ~ T ∈ᵈ θ -> 
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ T.
Proof.
  intros.
  apply trans_wl_wf_ss in H as Hwfss.
  apply wf_ss_binds_mono_typ in H0; auto.
  apply d_mono_typ_d_wf_typ.
  eapply trans_wl_ss_mono_typ_d_wl_mono_typ; eauto.
Qed.

Lemma trans_typ_a_mono_typ_d_mono_typ : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌈ θ ⌉ᵃ ᵗ⊢ᵃₘ Aᵃ -> 
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ Aᵈ.
Proof with eauto using binds_ss_to_denv_binds_ss, binds_tvar_ss_binds_ss_to_denv.
  intros * Htrans Hmono. generalize dependent Aᵈ. dependent induction Hmono; 
    intros; dependent destruction Htrans; intros; eauto 6...
  - apply binds_tvar_ss_to_aenv_binds_ss in H.
    unify_binds. 
  - apply binds_tvar_ss_to_aenv_binds_ss in H. 
    unify_binds.
  - apply binds_etvar_ss_to_aenv_binds_ss in H...
    destruct H as [T].
    unify_binds.
  - eapply wf_ss_binds_mono_typ; eauto.
Qed.

Lemma trans_wl_a_mono_typ_d_mono_typ : forall Γ Ω θ Tᵃ Tᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Tᵃ ⇝ Tᵈ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ Tᵃ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈₘ Tᵈ.
Proof.
  intros * Htranswl Htransa Hmono. eapply trans_typ_a_mono_typ_d_mono_typ; eauto.
   generalize dependent Tᵈ. dependent induction Hmono; intros.
  - constructor.
  - constructor. eapply trans_wl_a_wl_binds_tvar_ss in H; eauto.
    apply binds_tvar_ss_binds_ss_to_aenv; eauto.
  - apply a_mono_typ__etvar. eapply trans_wl_a_wl_binds_etvar_ss in H; eauto.
    destruct H as [T].  
    eapply binds_ss_etvar_binds_ss_to_aenv; eauto.
  - dependent destruction Htransa; eauto.
  - dependent destruction Htransa; eauto.
  - dependent destruction Htransa; eauto.
Qed.

Lemma trans_wl_a_wneq_all_d_wneq_all : forall Γ Ω θ Aᵃ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  a_wneq_all (⌊ Γ ⌋ᵃ) Aᵃ -> 
  d_wneq_all (⌊ Ω ⌋ᵈ) Aᵈ.
Proof with eauto using a_wneq_all, d_wneq_all.
  intros * Htranswl Htrans Hneq. generalize dependent Aᵈ.
  dependent induction Hneq; intros; dependent destruction Htrans; eauto...
  - econstructor...
    eapply trans_wl_a_wl_binds_tvar_d_wl...
  - eapply trans_wl_a_wl_binds_tvar_ss in Htranswl...
    unify_binds.
  - eapply trans_wl_a_wl_binds_tvar_ss in Htranswl...
    unify_binds.
  - eapply trans_wl_a_wl_binds_etvar_ss in Htranswl...
    destruct Htranswl as [T]. 
    unify_binds.
  - eapply trans_wl_a_wl_binds_etvar_ss in Htranswl...
    destruct Htranswl as [T]. 
    unify_binds.
  - apply wf_ss_binds_mono_typ in H1; auto.
    eapply trans_wl_ss_mono_typ_d_wl_mono_typ in H1...
    eapply d_mono_typ_d_wneq_all...
Qed.

Lemma trans_wl_d_wneq_all_a_wneq_all : forall Γ Ω θ Aᵃ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ -> 
  d_wneq_all (⌊ Ω ⌋ᵈ) Aᵈ ->
  a_wneq_all (⌊ Γ ⌋ᵃ) Aᵃ. 
Proof with eauto using a_wneq_all, d_wneq_all.
  intros * Htranswl Htrans Hneq. generalize dependent Aᵃ.
  dependent induction Hneq; intros; dependent destruction Htrans; eauto;
    try solve [eapply trans_wl_ss_binds_etvar_a_wl in H0; eauto using a_wneq_all, d_wneq_all].
  - econstructor. 
    eapply trans_wl_ss_binds_tvar_a_wl...
  - eapply trans_wl_d_wl_binds_tvar_ss in H...
    apply binds_ss_to_denv_binds_ss in H. unify_binds.
  - eapply trans_wl_ss_binds_etvar_a_wl in H1...
  - eapply trans_wl_ss_binds_etvar_a_wl in H2...
  - eapply trans_wl_ss_binds_etvar_a_wl in H1...
  - eapply trans_wl_ss_binds_etvar_a_wl in H1...
Qed.

Lemma trans_typ_binds_etvar : forall θ X T,
  wf_ss θ ->
  X ~ T ∈ᵈ θ ->
  θ ᵗ⊩ ` X ⇝ T.
Proof.
  intros.
  constructor; auto.
Qed.

Lemma trans_typ_tvar_stvar_in_atyp_in_dtyp' : forall θ X Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ~ □ ∈ᵈ θ \/ X ~ ■ ∈ᵈ θ ->
  X `in` ftvar_in_typ Aᵃ -> 
  X `in` ftvar_in_typ Aᵈ.
Proof.
  intros * Hlc Htrans Hbinds Hfv. generalize dependent θ. generalize dependent Aᵈ.
  induction Hlc; simpl in *; intros; try fsetdec.
  - dependent destruction Htrans.
    + apply singleton_iff in Hfv. subst. simpl. auto.
    + apply singleton_iff in Hfv. subst. simpl. auto.
    + apply singleton_iff in Hfv. subst. 
      apply wf_ss_uniq in H.  inversion Hbinds; 
      pose proof (binds_unique _ _ _ _ _ H0 H1 H); inversion H2.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans.
    pick fresh X0. inst_cofinites_with X0.
    assert (X `in` ftvar_in_typ (A1ᵈ ᵗ^ₜ X0)). {
      eapply H0; eauto.
      rewrite ftvar_in_typ_open_typ_wrt_typ_lower  with (A2:=` X0) in Hfv.
      auto. inversion Hbinds; auto.
    }
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H3.
    apply union_iff in H3. inversion H3; simpl; eauto.
    + apply singleton_iff in H4. subst. solve_notin_eq X. 
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
Qed.

Lemma trans_typ_tvar_stvar_in_atyp_in_dtyp : forall θ X Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ~ □ ∈ᵈ θ \/ X ~ ■ ∈ᵈ θ ->
  X `in` ftvar_in_typ Aᵃ -> 
  X `in` ftvar_in_typ Aᵈ.
Proof.
  intros * Htrans Hbinds Hfv. 
  apply trans_typ_lc_atyp in Htrans as Hlc.
  eapply trans_typ_tvar_stvar_in_atyp_in_dtyp'; eauto.
Qed.

Lemma trans_typ_tvar_stvar_in_etvar_binds_in_atyp' : forall θ X T Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ~ T ∈ᵈ θ ->
  X `in` ftvar_in_typ Aᵃ ->
  (forall Y, Y `in` ftvar_in_typ T -> Y `in` ftvar_in_typ Aᵈ). 
Proof.
  intros * Hlc Htrans Hbinds Hfv. generalize dependent θ. generalize dependent Aᵈ.
  induction Hlc; simpl in *; intros; try fsetdec.
  - apply singleton_iff in Hfv.
    subst. apply trans_typ_binds_etvar in Hbinds; auto.
    apply trans_typ_det with (A₁ᵈ:=T) in Htrans; eauto; subst; auto.
    + eapply trans_typ_wf_ss; eauto.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans. 
    pick fresh X0. inst_cofinites_with X0.
    assert (Y `in` ftvar_in_typ (A1ᵈ ᵗ^ₜ X0)). {
      rewrite ftvar_in_typ_open_typ_wrt_typ_lower  with (A2:=` X0) in Hfv.
      eapply H0 with (Y:=Y) in Hfv; eauto.
    }
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H4.
    apply union_iff in H4. inversion H4; simpl; eauto.
    apply singleton_iff in H5. subst. solve_notin_eq Y. 
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
Qed.

Lemma trans_typ_tvar_stvar_in_etvar_binds_in_atyp : forall θ X T Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ~ T ∈ᵈ θ ->
  X `in` ftvar_in_typ Aᵃ ->
  (forall Y, Y `in` ftvar_in_typ T -> Y `in` ftvar_in_typ Aᵈ). 
Proof.
  intros * Htrans Hbinds Hfv. 
  apply trans_typ_lc_atyp in Htrans as Hlc.
  eapply trans_typ_tvar_stvar_in_etvar_binds_in_atyp'; eauto.
Qed.

Lemma trans_wl_a_wf_typ_d_wf_typ' : forall Γ Ω θ Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ Aᵃ ->
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ Aᵈ.
Proof with eauto. 
  intros * Hlc. 
  generalize dependent Aᵈ.
  generalize dependent Γ.
  generalize dependent Ω.
  generalize dependent θ.
  induction Hlc; intros.
  - dependent destruction H0...
  - dependent destruction H0...
  - dependent destruction H0...
  - dependent destruction H0...
    + eapply trans_wl_ss_binds_tvar_a_wl in H1...
      eapply trans_wl_a_wl_binds_tvar_d_wl in H1...
    + eapply trans_wl_ss_binds_stvar_a_wl in H1...
      eapply trans_wl_a_wl_binds_stvar_d_wl in H1...
    + eapply trans_wl_wf_bind_typ...
  - dependent destruction H0...
    dependent destruction H1...
  - dependent destruction H2.
    dependent destruction H4.
    inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X...
    + eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=dbind_tvar_empty)... 
    + rewrite_env (dwl_to_denv (dworklist_cons_var Ω X dbind_tvar_empty)).
      eapply H0 with (Γ:=(aworklist_cons_var Γ X abind_tvar_empty))...
      econstructor...
  - dependent destruction H0...
    dependent destruction H1...
  - dependent destruction H0...
    dependent destruction H1...
Qed.

Lemma trans_wl_ss_wf_typ_d_wf_typ : forall Γ Ω θ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  d_wf_typ (ss_to_denv θ) Aᵈ ->
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ Aᵈ.
Proof with eauto. 
  intros. generalize dependent Γ; generalize dependent Ω; dependent induction H0; intros...
  - constructor. eapply trans_wl_a_wl_binds_tvar_d_wl; eauto. eapply trans_wl_ss_binds_tvar_a_wl; eauto.
    apply binds_ss_to_denv_binds_ss...
  - apply d_wf_typ__stvar. eapply trans_wl_a_wl_binds_stvar_d_wl; eauto. eapply trans_wl_ss_binds_stvar_a_wl; eauto.
    apply binds_ss_to_denv_binds_ss...
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X...
    + replace (X ~ □ ++ dwl_to_denv Ω) with (dwl_to_denv (dworklist_cons_var Ω X dbind_tvar_empty))...
      eapply H1 with (Γ:=aworklist_cons_var Γ X abind_tvar_empty) (θ:=(X, dbind_tvar_empty)::θ); eauto.
Qed.

Lemma trans_wl_a_wf_typ_d_wf_typ : forall Γ Ω θ Aᵃ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ Aᵃ ->
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ Aᵈ.
Proof with eauto. 
  intros. apply trans_typ_lc_atyp in H0 as Hlc.
  eapply trans_wl_a_wf_typ_d_wf_typ'; eauto.
Qed.

Lemma trans_wl_d_wf_typ_a_wf_typ' : forall Γ Ω θ Aᵃ Aᵈ,
  lc_typ Aᵈ ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ Aᵈ ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ Aᵃ.
Proof with eauto.
  intros * Hlc. 
  generalize dependent Aᵃ.
  generalize dependent Γ.
  generalize dependent Ω.
  generalize dependent θ.
  induction Hlc; intros.
  - dependent destruction H0...
    apply a_wf_typ__etvar...
    eapply trans_wl_ss_binds_etvar_a_wl...
  - dependent destruction H0...
    solve_binds_nonmono_contradiction.
  - dependent destruction H0...
    solve_binds_nonmono_contradiction.
  - dependent destruction H0...
    + eapply trans_wl_ss_binds_tvar_a_wl in H1...
    + eapply trans_wl_ss_binds_stvar_a_wl in H1...
    + eapply trans_wl_ss_binds_etvar_a_wl in H1...
  - dependent destruction H0...
    eapply trans_wl_ss_binds_etvar_a_wl in H1...
    dependent destruction H1...
  - dependent destruction H2.
    solve_binds_nonmono_contradiction.
    dependent destruction H4.
    inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X...
    + rewrite_env (awl_to_aenv (aworklist_cons_var Γ X abind_tvar_empty)).
      eapply H0 with (Ω:=(dworklist_cons_var Ω X dbind_tvar_empty))...
      econstructor...
  - dependent destruction H0...
    apply a_wf_typ__etvar...
    eapply trans_wl_ss_binds_etvar_a_wl...
    dependent destruction H1...
  - dependent destruction H0...
    apply a_wf_typ__etvar...  eapply trans_wl_ss_binds_etvar_a_wl...
    dependent destruction H1...
Qed.

Lemma trans_wl_d_wf_typ_a_wf_typ : forall Γ Ω θ Aᵃ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ Aᵈ -> 
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ Aᵃ.
Proof with eauto. 
  intros. apply trans_typ_lc_atyp in H0 as Hlc.
  eapply trans_wl_d_wf_typ_a_wf_typ' with (Aᵈ:=Aᵈ); eauto.
Qed.

Lemma trans_wl_d_wf_typ_ss_wf_typ : forall Γ Ω θ Aᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  ⌊ Ω ⌋ᵈ ᵗ⊢ᵈ Aᵈ ->
  ⌈ θ ⌉ᵈ ᵗ⊢ᵈ Aᵈ.
Proof with eauto. 
  intros. generalize dependent Γ; generalize dependent θ; dependent induction H0; intros...
  - eapply trans_wl_d_wl_binds_tvar_ss in H0; eauto.
  - eapply trans_wl_d_wl_binds_stvar_ss in H0; eauto.
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X...
    rewrite_env (ss_to_denv ((X, dbind_tvar_empty)::θ)).
    eapply H1 with (Γ:=aworklist_cons_var Γ X abind_tvar_empty) (Ω:=dworklist_cons_var Ω X dbind_tvar_empty); eauto.
Qed.

Lemma trans_wl_d_wl_dom_upper : forall θ Γ Ω,  
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  dom (⌊ Ω ⌋ᵈ) [<=] dom (⌊ Γ ⌋ᵃ).
Proof with auto.
  intros. dependent induction H; simpl...
  - fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
Qed.

Lemma trans_wl_ss_dom_upper : forall θ Γ Ω,  
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  dom θ [<=] dom (⌊ Γ ⌋ᵃ).
Proof with auto.
  intros. dependent induction H; simpl...
  - fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
Qed.

Lemma trans_typ_weaken : forall θ1 θ2 θ3 Aᵃ Aᵈ,
  θ3 ++ θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros. generalize dependent θ2.
  dependent induction H; intros...
  - inst_cofinites_for trans_typ__all; intros.
    inst_cofinites_with X...
    rewrite_env (((X, □) :: θ3) ++ θ2 ++ θ1).
    eapply H1; simpl...
Qed.

Lemma trans_typ_weaken_cons : forall θ X b Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  wf_ss ((X, b) :: θ) ->
  (X, b) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof.
  intros. rewrite_env (nil ++ (X ~ b) ++ θ). apply trans_typ_weaken; auto.
Qed.

Lemma trans_typ_strengthen_etvar : forall θ1 θ2 X T Aᵃ Aᵈ,
  (θ2 ++ (X, dbind_typ T) :: θ1) ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ∉ ftvar_in_typ Aᵃ ->
  θ2 ++ θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto using wf_ss_strengthen_etvar.
  intros.
  dependent induction H; intros; simpl in *...
  - econstructor. 
    eapply wf_ss_strengthen_etvar; eauto.
    simpl in H1.
    apply binds_remove_mid in H0...
  - apply trans_typ__stvar.
    eapply wf_ss_strengthen_etvar; eauto.
    simpl in H1.
    apply binds_remove_mid in H0...
  - econstructor.
    eapply wf_ss_strengthen_etvar; eauto.
    simpl in H1.
    apply binds_remove_mid in H0...
  - eapply trans_typ__all with (L:=L `union` singleton X); eauto.
    intros. inst_cofinites_with X0.
    rewrite_env (((X0, □) :: θ2) ++ θ1).
    eapply H1 with (X:=X) (T:=T); eauto.
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
Qed.

Lemma trans_wl_a_wl_binds_var_binds_d_wl_and_trans : forall θ Γ Ω x Aᵃ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  x ~ Aᵃ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  exists Aᵈ, x ~ Aᵈ ∈ᵈ ⌊ Ω ⌋ᵈ /\ θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros. induction H...
  - inversion H0.
  - simpl in *. destruct_binds; eauto.
    apply IHtrans_worklist in H3. destruct H3 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto. apply trans_typ_weaken_cons...
  - simpl in *. destruct_binds; eauto.
    apply IHtrans_worklist in H3. destruct H3 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto. apply trans_typ_weaken_cons...
  - simpl in *. destruct_binds; eauto.
    apply IHtrans_worklist in H3. destruct H3 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto.
  - simpl in *. destruct_binds; eauto.
    apply IHtrans_worklist in H4. destruct H4 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto. apply trans_typ_weaken_cons...
Qed.

Lemma trans_wl_a_wl_binds_var_binds_d_wl : forall θ Γ Ω x Aᵃ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  x ~ Aᵃ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  exists Aᵈ, x ~ Aᵈ ∈ᵈ ⌊ Ω ⌋ᵈ.
Proof with eauto.
  intros. eapply trans_wl_a_wl_binds_var_binds_d_wl_and_trans in H0; eauto.
  destruct H0 as [Aᵈ [Hbinds _]]. eauto.  
Qed.

Lemma trans_wl_a_wf_exp_d_wf_exp' : forall Γ Ω θ eᵃ eᵈ,
  lc_exp eᵃ ->
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ eᵃ ->
  d_wf_exp (dwl_to_denv Ω) eᵈ.
Proof with auto.
  intros * Hlc Htranswl Htranse Hwfe.
  generalize dependent Ω. 
  generalize dependent Γ.
  generalize dependent θ. 
  generalize dependent eᵈ.
  dependent induction Hlc; intros; dependent destruction Htranse...
  - dependent destruction Hwfe.
    eapply trans_wl_a_wl_binds_var_binds_d_wl with (Ω:=Ω) in H0; eauto.
    destruct H0 as [Aᵈ Hbinds]. econstructor; eauto. 
  - dependent destruction Hwfe. 
    inst_cofinites_for d_wf_exp__abs T:=typ_unit...
    intros. inst_cofinites_with x.
    rewrite_env (dwl_to_denv (dworklist_cons_var Ω x (dbind_typ typ_unit))).
    eapply H0; eauto. simpl.
    rewrite_env (nil ++ (x, abind_var_typ typ_unit) :: ⌊ Γ ⌋ᵃ). 
    eapply a_wf_exp_var_binds_another with (A1:=T); eauto.
  - dependent destruction Hwfe. constructor; eauto.
  - dependent destruction Hwfe. inst_cofinites_for d_wf_exp__tabs;
    intros; inst_cofinites_with X...
    + eapply trans_typ_dtvar_atyp_s_in_dtyp with (b:=dbind_tvar_empty); eauto.
    + rewrite_env (⌊ X ~ᵈ □ ;ᵈ Ω ⌋ᵈ). 
      eapply H0 with (Γ:=X ~ᵃ □ ;ᵃ Γ); eauto.
      constructor; eauto. econstructor...
  - dependent destruction Hwfe. constructor; eauto.
    eapply trans_wl_a_wf_typ_d_wf_typ; eauto.
  - dependent destruction Hwfe. constructor; eauto.
    eapply trans_wl_a_wf_typ_d_wf_typ; eauto.
Qed.

Lemma trans_wl_a_wf_exp_d_wf_exp : forall Γ Ω θ eᵃ eᵈ,
  nil ⊩ Γ ⇝ Ω ⫣ θ ->
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  a_wf_exp (awl_to_aenv Γ) eᵃ ->
  d_wf_exp (dwl_to_denv Ω) eᵈ.
Proof.
  intros. apply trans_exp_lc_aexp in H0 as Hlc.
  eapply trans_wl_a_wf_exp_d_wf_exp'; eauto.
Qed.

Lemma trans_wl_a_wf_conts_d_wf_conts : forall Γ Ω θ csᵃ csᵈ,  
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ -> 
  ⌊ Γ ⌋ᵃ ᶜˢ⊢ᵃ csᵃ -> 
  d_wf_conts (dwl_to_denv Ω) csᵈ
with trans_wl_a_wf_contd_d_wf_contd : forall Γ Ω θ cdᵃ cdᵈ,  
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ -> 
  ⌊ Γ ⌋ᵃ ᶜᵈ⊢ᵃ cdᵃ -> 
  d_wf_contd (dwl_to_denv Ω) cdᵈ.
Proof with eauto using trans_wl_a_wf_typ_d_wf_typ, trans_wl_a_wf_exp_d_wf_exp.
  - clear trans_wl_a_wf_conts_d_wf_conts. intros * Htranswl Htransc Hwfc. 
    dependent induction Htransc; dependent destruction Hwfc...
  - clear trans_wl_a_wf_contd_d_wf_contd. intros * Htranswl Htransc Hwfc. 
    dependent induction Htransc; dependent destruction Hwfc...
Qed.

Lemma trans_wl_a_wf_work_d_wf_work : forall Γ Ω θ wᵃ wᵈ,  
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  θ ʷ⊩ wᵃ ⇝ wᵈ -> 
  ⌊ Γ ⌋ᵃ ʷ⊢ᵃ wᵃ -> 
  d_wf_work (dwl_to_denv Ω) wᵈ.
Proof.
  intros * Hwfwl Htransw Hwfw. 
  dependent destruction Htransw; dependent destruction Hwfw; 
    eauto 7 using trans_wl_a_wf_typ_d_wf_typ, 
      trans_wl_a_wf_exp_d_wf_exp, 
      trans_wl_a_wf_conts_d_wf_conts, 
      trans_wl_a_wf_contd_d_wf_contd.
Qed.

Lemma trans_wl_a_wf_twl_d_wf_twl : forall θ Γ Ω,  
  ⊢ᵃʷₜ Γ -> 
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  ⊢ᵈʷₜ Ω.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H...
  - econstructor...
    eapply trans_wl_a_wf_work_d_wf_work; eauto.
    intros. destruct H4 as [A1 [B1]]. 
    dependent destruction H4.
    dependent destruction H3... 
  - econstructor...
    rewrite trans_wl_d_wl_dom_upper...
  - econstructor... 
    rewrite trans_wl_d_wl_dom_upper...
    eapply trans_wl_a_wf_typ_d_wf_typ with (Aᵃ:=A1ᵃ)...
Qed.

Lemma trans_wl_a_wf_wl_d_wf_wl : forall θ Γ Ω,  
  ⊢ᵃʷₛ Γ -> 
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  ⊢ᵈʷₛ Ω.
Proof with eauto using trans_wl_a_wf_twl_d_wf_twl.
  intros. dependent induction H0; dependent destruction H...
  - dependent destruction H3...
    apply d_wf_wl__conswork_sub; eauto; 
    eapply trans_wl_a_wf_typ_d_wf_typ; eauto.
  - econstructor...
    dependent destruction H... constructor...
    rewrite trans_wl_d_wl_dom_upper...
  - dependent destruction H.
  - apply d_wf_wl__consstvar...
    rewrite trans_wl_d_wl_dom_upper...
  - dependent destruction H...
Qed.

Lemma a_wf_twl_d_wf_tenv : forall θ Γ Ω,  
  ⊢ᵃʷₜ Γ -> 
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  ⊢ᵈₜ ⌊ Ω ⌋ᵈ.
Proof with eauto.
  intros.
  apply d_wf_twl_wf_tenv.
  eapply trans_wl_a_wf_twl_d_wf_twl; eauto.
Qed.

Lemma a_wf_wl_d_wf_env : forall θ Γ Ω,  
  ⊢ᵃʷₛ Γ -> 
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  ⊢ᵈ ⌊ Ω ⌋ᵈ.
Proof with eauto.
  intros.
  apply d_wf_wl_wf_env.
  eapply trans_wl_a_wf_wl_d_wf_wl; eauto.
Qed.

Lemma a_wl_uniq_d_wl_uniq : forall θ Γ Ω,  
  uniq (⌊ Γ ⌋ᵃ) -> 
  nil ⊩ Γ ⇝ Ω ⫣ θ -> 
  uniq (⌊ Ω ⌋ᵈ).
Proof with eauto.
  intros. dependent induction H0; simpl in *; dependent destruction H; eauto.
  - apply IHtrans_worklist... rewrite <- x in *... 
  - apply IHtrans_worklist... rewrite <- x in *...
  - constructor; auto. erewrite trans_wl_d_wl_dom_upper; eauto. 
  - constructor; auto. erewrite trans_wl_d_wl_dom_upper; eauto. 
  - constructor; auto. erewrite trans_wl_d_wl_dom_upper; eauto. 
Qed.

Lemma a_wf_work_apply_conts : forall Γ cs A w,
  Γ ᶜˢ⊢ᵃ cs -> 
  Γ ᵗ⊢ᵃ A -> 
  apply_conts cs A w ->
  Γ ʷ⊢ᵃ w.
Proof with eauto.
  intros. induction H1; try solve [destruct_a_wf_wl; constructor; eauto].
Qed.

Lemma a_wf_work_apply_contd : forall Γ cd A B w,
  a_wf_contd Γ cd ->
  a_wf_typ Γ A ->
  a_wf_typ Γ B ->
  apply_contd cd A B w ->
  a_wf_work Γ w.
Proof with eauto.
  intros. induction H2; try solve [destruct_a_wf_wl; constructor; eauto].
Qed.

Lemma trans_typ_strengthen_dtvar : forall θ1 θ2 X b Aᵃ Aᵈ,
  (θ2 ++ (X, b) :: θ1) ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ∉ ftvar_in_typ Aᵃ ->
  wf_ss (θ2 ++ θ1) ->
  θ2 ++ θ1 ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  dependent induction H; intros; simpl in *...
  - econstructor...
    simpl in H1.
    apply binds_remove_mid in H0...
  - apply trans_typ__stvar...
    simpl in H1.
    apply binds_remove_mid in H0...
  - econstructor...
    simpl in H1.
    apply binds_remove_mid in H0...
  - inst_cofinites_for trans_typ__all;
    intros; inst_cofinites_with X0...
    rewrite_env (((X0, □) :: θ2) ++ θ1).
    eapply H1 with (X:=X) (b:=b); simpl; eauto...
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
Qed.

Lemma trans_typ_strengthen_cons : forall θ X b Aᵃ Aᵈ,
  (X, b) :: θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  X ∉ ftvar_in_typ Aᵃ ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof.
  intros.
  rewrite_env (nil ++ θ).
  eapply trans_typ_strengthen_dtvar; eauto.
  apply trans_typ_wf_ss in H. dependent destruction H; auto.
Qed.

Lemma trans_exp_strengthen_etvar : forall θ1 θ2 X T eᵃ eᵈ,
  (θ2 ++ (X, dbind_typ T) :: θ1) ᵉ⊩ eᵃ ⇝ eᵈ ->
  X ∉ ftvar_in_exp eᵃ ->
  θ2 ++ θ1 ᵉ⊩ eᵃ ⇝ eᵈ.
Proof with eauto using wf_ss_strengthen_etvar, trans_typ_strengthen_etvar.
  intros. dependent induction H; simpl in *...
  - inst_cofinites_for trans_exp__abs. intros.
    inst_cofinites_with x...
    eapply H0... rewrite ftvar_in_exp_open_exp_wrt_exp_upper...
  - inst_cofinites_for trans_exp__tabs; subst; intros; inst_cofinites_with X0.
    + rewrite_env (((X0, □) :: θ2) ++ θ1).
      eapply H0 with (X:=X) (T:=T); eauto.
      rewrite ftvar_in_exp_open_exp_wrt_typ_upper...
    + rewrite_env (((X0, □) :: θ2) ++ θ1).
      eapply trans_typ_strengthen_dtvar; eauto.
      rewrite ftvar_in_typ_open_typ_wrt_typ_upper...
      apply trans_typ_wf_ss in H1...
Qed.

Lemma trans_conts_strengthen_etvar : forall θ1 θ2 X T csᵃ csᵈ,
  (θ2 ++ (X, dbind_typ T) :: θ1) ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  X ∉ ftvar_in_conts csᵃ ->
  θ2 ++ θ1 ᶜˢ⊩ csᵃ ⇝ csᵈ
with trans_contd_strengthen_etvar : forall θ1 θ2 X T cdᵃ cdᵈ,
  (θ2 ++ (X, dbind_typ T) :: θ1) ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  X ∉ ftvar_in_contd cdᵃ ->
  θ2 ++ θ1 ᶜᵈ⊩ cdᵃ ⇝ cdᵈ.
Proof with eauto using wf_ss_strengthen_etvar, trans_typ_strengthen_etvar, trans_exp_strengthen_etvar. 
  - intros. clear trans_conts_strengthen_etvar. 
      dependent induction H; simpl in *...
  - intros. clear trans_contd_strengthen_etvar. 
      dependent induction H; simpl in *...
Qed.

Lemma trans_work_strengthen_etvar : forall θ1 θ2 X T wᵃ wᵈ,
  (θ2 ++ (X, dbind_typ T) :: θ1) ʷ⊩ wᵃ ⇝ wᵈ ->
  X ∉ ftvar_in_work wᵃ ->
  θ2 ++ θ1 ʷ⊩ wᵃ ⇝ wᵈ.
Proof.
  intros. dependent destruction H; simpl in *; eauto 7 
    using wf_ss_strengthen_etvar, trans_typ_strengthen_etvar, trans_exp_strengthen_etvar,
          trans_conts_strengthen_etvar, trans_contd_strengthen_etvar.
Qed.

Lemma trans_wl_strengthen_etvar : forall Γ Ω X T θ1 θ2 θ'1 θ'2,
  X ∉ ftvar_in_aworklist' Γ ->
  θ2 ++ (X, dbind_typ T) :: θ1 ⊩ Γ ⇝ Ω ⫣ (θ'2 ++ (X, dbind_typ T) :: θ'1) ->
  (θ2 ++ θ1) ⊩ Γ ⇝ Ω ⫣ (θ'2 ++ θ'1).
Proof.
  intros. dependent induction H0.
  - apply eq_sym in x. apply ls_split_det in x. dependent destruction x. subst.
    constructor; auto.
    eapply wf_ss_strengthen_etvar; eauto.
    apply wf_ss_notin_remaining in H0. rewrite dom_app in H0. destruct_notin; eauto.
  - simpl in H.
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    eapply IHtrans_worklist in H2; eauto.
    econstructor. auto. 
    eapply trans_work_strengthen_etvar; eauto.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'2.
    + simpl in x. inversion x. 
    + simpl in x. inversion x. subst.  
      eapply IHtrans_worklist in H2; eauto.
      simpl. 
      constructor; auto.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'2.
    + simpl in x. inversion x. 
    + simpl in x. inversion x. subst.  
      eapply IHtrans_worklist in H2; eauto.
      simpl. 
      constructor; auto.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    eapply IHtrans_worklist in H2; eauto.
    constructor; auto.
    eapply trans_typ_strengthen_etvar; eauto.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'2.
    + simpl in x. inversion x. subst. solve_notin_eq X. 
    + simpl in x. inversion x. subst.
      eapply IHtrans_worklist in H3; eauto.
      simpl. constructor; auto.
      rewrite ss_to_denv_app in *; simpl in *; auto.
Qed.

Lemma trans_typ_refl: forall θ A,
  ss_to_denv θ ᵗ⊢ᵈ A ->
  wf_ss θ ->
  θ ᵗ⊩ A ⇝ A.
Proof with eauto.
  intros. dependent induction H...
  - econstructor...
    apply in_ss_denv_in_ss...
  - eapply trans_typ__stvar...
    apply in_ss_denv_in_ss...
  - inst_cofinites_for trans_typ__all...
Qed.

Lemma trans_exp_weaken : forall θ1 θ2 θ3 eᵃ eᵈ,
  θ3 ++ θ1 ᵉ⊩ eᵃ ⇝ eᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ᵉ⊩ eᵃ ⇝ eᵈ.
Proof with auto using trans_typ_weaken.
  intros. generalize dependent θ2. dependent induction H...
  - intros. inst_cofinites_for trans_exp__abs. intros. inst_cofinites_with x.
    eapply H0...
  - intros. inst_cofinites_for trans_exp__tabs; intros; inst_cofinites_with X.
    + rewrite_env (((X, □) :: θ3) ++ θ2 ++ θ1).
      eapply H0... econstructor...
    + rewrite_env (((X, □) :: θ3) ++ θ2 ++ θ1).
      eapply trans_typ_weaken... econstructor...
Qed. 

Lemma trans_exp_weaken_cons : forall θ X b eᵃ eᵈ,
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  wf_ss ((X, b) :: θ) ->
  (X, b) :: θ ᵉ⊩ eᵃ ⇝ eᵈ.
Proof.
  intros. rewrite_env (nil ++ (X ~ b) ++ θ). apply trans_exp_weaken; auto.
Qed. 

Lemma trans_conts_weaken : forall θ1 θ2 θ3 csᵃ csᵈ,
  θ3 ++ θ1 ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ᶜˢ⊩ csᵃ ⇝ csᵈ
with trans_contd_weaken : forall θ1 θ2 θ3 cdᵃ cdᵈ,
  θ3 ++ θ1 ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ᶜᵈ⊩ cdᵃ ⇝ cdᵈ.
Proof with auto using trans_typ_weaken, trans_exp_weaken.
  - intros. clear trans_conts_weaken. dependent induction H...
  - intros. clear trans_contd_weaken. dependent induction H...
Qed.
     

Lemma trans_conts_weaken_cons : forall θ X b csᵃ csᵈ,
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  wf_ss ((X, b) :: θ) ->
  (X, b) :: θ ᶜˢ⊩ csᵃ ⇝ csᵈ
with trans_contd_weaken_cons : forall θ X b cdᵃ cdᵈ,
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  wf_ss ((X, b) :: θ) ->
  (X, b) :: θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ.
Proof.
  - intros. rewrite_env (nil ++ (X ~ b) ++ θ). apply trans_conts_weaken; auto.
  - intros. rewrite_env (nil ++ (X ~ b) ++ θ). apply trans_contd_weaken; auto.
Qed.

Lemma trans_work_weaken : forall θ1 θ2 θ3 wᵃ wᵈ,
  θ3 ++ θ1 ʷ⊩ wᵃ ⇝ wᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ʷ⊩ wᵃ ⇝ wᵈ.
Proof with auto using trans_typ_weaken, trans_exp_weaken, trans_conts_weaken, trans_contd_weaken.
  intros. dependent destruction H...
Qed.

#[local] Hint Immediate 
  trans_typ_weaken_cons trans_exp_weaken_cons 
  trans_conts_weaken_cons trans_contd_weaken_cons : core.

Lemma trans_wl_weaken_etvar : forall Γ Ω X T θ1 θ2 θ',
  X ∉ ftvar_in_aworklist' Γ `union` dom θ' `union` dom θ1 `union` dom θ2 ->
  (θ2 ++ θ1) ⊩ Γ ⇝ Ω ⫣ (θ' ++ θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) T ->
  θ2 ++ (X, dbind_typ T) :: θ1 ⊩ Γ ⇝ Ω ⫣ (θ' ++ θ2 ++ (X, dbind_typ T) :: θ1).
Proof with eauto.
  intros. dependent induction H0...
  - rewrite_env (nil ++ θ2 ++ θ1) in x. apply ls_app_eq_inv in x. 
    subst.
    constructor... simpl. eapply wf_ss_weaken_etvar...
  - simpl in *. constructor...
    rewrite_env ((θ' ++ θ2) ++ (X ~ dbind_typ T) ++ θ1).
    apply trans_work_weaken.
    rewrite_env (θ' ++ θ2 ++ θ1). auto.
    rewrite_env ((θ' ++ θ2) ++ (X ,dbind_typ T) :: θ1).
    apply wf_ss_weaken_etvar...
    rewrite_env (θ' ++ θ2 ++ θ1). eauto.
  - apply trans_wl_split_ss in H0. 
    destruct H0 as [θ'']. subst.
    rewrite_env (((X0, □) :: θ'') ++ θ2 ++ θ1) in x.
    apply ls_app_eq_inv in x. subst.
    simpl in *. 
    constructor...
  - apply trans_wl_split_ss in H0. 
    destruct H0 as [θ'']. subst. 
    rewrite_env (((X0, ■) :: θ'') ++ θ2 ++ θ1) in x.
    apply ls_app_eq_inv in x. subst.
    simpl in *. 
    constructor...
  - simpl in *. constructor...
    rewrite_env ((θ' ++ θ2) ++ (X ~ dbind_typ T) ++ θ1).
    apply trans_typ_weaken...
    + rewrite_env (θ' ++ θ2 ++ θ1). auto.
    + apply wf_ss_weaken_etvar; eauto.
      rewrite_env (θ' ++ θ2 ++ θ1). eauto.
  - apply trans_wl_split_ss in H0.  
    destruct H0 as [θ'']. subst. 
    rewrite_env (((X0, dbind_typ T0) :: θ'') ++ θ2 ++ θ1) in x.
    apply ls_app_eq_inv in x. subst.
    simpl in *.
    constructor...
    rewrite_env ((θ'' ++ θ2) ++ (X, dbind_typ T) :: θ1).
    rewrite <- wf_ss_etvar_same_denv.
    rewrite_env (θ'' ++ θ2 ++ θ1). auto.
Qed.

(* Lemma trans_wl_weaken_etvar_cons : forall Γ Ω X T θ θ',
  X ∉ ftvar_in_aworklist' Γ `union` dom θ->
  θ ⊩ Γ ⇝ Ω ⫣ (θ' ++ θ) ->
  d_mono_typ (ss_to_denv θ) T ->
  (X, dbind_typ T) :: θ ⊩ Γ ⇝ Ω ⫣ (θ' ++ (X, dbind_typ T) :: θ).
Proof.
  intros. rewrite_env (nil ++ (X, dbind_typ T) :: θ).
  eapply trans_wl_weaken_etvar; eauto.
Qed. *)

Lemma ftvar_in_trans_dtyp_upper : forall θ Aᵃ Aᵈ,
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  ftvar_in_typ Aᵈ [<=] dom θ.
Proof.
  intros. induction H; simpl; try fsetdec.
  - apply binds_In in H0. fsetdec.
  - apply binds_In in H0. fsetdec.
  - rewrite wf_ss_ftvar_in_typ_upper; eauto. fsetdec. 
  - inst_cofinites_by (L `union` dom θ `union` ftvar_in_typ A1ᵈ) using_name X.
    assert (ftvar_in_typ A1ᵈ [<=] ftvar_in_typ (A1ᵈ ᵗ^ₜ X)). {
      eapply ftvar_in_typ_open_typ_wrt_typ_lower.
    }
    simpl in *. fsetdec.
Qed.
  
Lemma d_mono_typ_reorder_ss : forall θ θ' T,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_typ T -> binds X b θ -> binds X b θ') ->
  d_mono_typ (ss_to_denv θ) T ->
  d_mono_typ (ss_to_denv θ') T.
Proof.
  intros. apply d_mono_typ_lc in H2 as Hlc. induction Hlc; try dependent destruction H2.
  - constructor.
  - subst. 
    apply binds_ss_to_denv_binds_ss in H2.
    apply H1 in H2; simpl; auto.
    constructor. 
    apply binds_tvar_ss_binds_ss_to_denv; eauto.
  - simpl in *. constructor; eauto.
  - simpl in *. constructor; eauto.
  - simpl in *. constructor; eauto.
Qed.

Lemma trans_typ_reorder_ss : forall θ θ' Aᵃ Aᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_typ Aᵃ -> binds X b θ -> binds X b θ') ->
  θ ᵗ⊩ Aᵃ ⇝ Aᵈ ->
  θ' ᵗ⊩ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros. apply trans_typ_lc_atyp in H2 as Hlc.
  generalize dependent θ'. generalize dependent θ. generalize dependent Aᵈ.
  induction Hlc; intros...
  - dependent destruction H2...
  - dependent destruction H2...
  - dependent destruction H2...
  - dependent destruction H2...
    + apply trans_typ__tvar... 
      apply H3... simpl...
    + apply trans_typ__stvar...
      apply H3... simpl... 
    + apply trans_typ__etvar... 
      apply H3... simpl...
  - dependent destruction H2...
    simpl in H1. econstructor...
  - dependent destruction H2.
    inst_cofinites_for trans_typ__all; intros;
    inst_cofinites_with X...
    eapply H0 with (θ':=(X, dbind_tvar_empty) :: θ') in H3; auto...
    + intros. destruct (X0 == X).
      * subst. destruct_binds... 
        -- apply binds_dom_contradiction in H10... contradiction.
      * rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H7. 
        apply union_iff in H7. inversion H7.
        -- simpl in H9. apply singleton_iff in H9. subst. contradiction. 
        -- destruct_binds... 
  - dependent destruction H2...
    simpl in H1. econstructor...
  - dependent destruction H2...
    simpl in H1. econstructor...
Qed.

Lemma trans_exp_reorder_ss' : forall θ θ' eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_exp eᵃ -> binds X b θ -> binds X b θ') ->
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  θ' ᵉ⊩ eᵃ ⇝ eᵈ.
Proof with eauto.
  intros * Hlc. 
  generalize dependent θ'. generalize dependent θ. generalize dependent eᵈ.
  induction Hlc; intros; try solve [dependent destruction H2; eauto].
  - dependent destruction H4...
    inst_cofinites_for trans_exp__abs. intros. 
    inst_cofinites_with x.
    eapply H0 with (θ:=θ)... intros.
    apply H3...
    rewrite ftvar_in_exp_open_exp_wrt_exp_upper in H6. simpl in *. fsetdec.
  - simpl in *. dependent destruction H2...
    constructor...
  - dependent destruction H4.
    inst_cofinites_for trans_exp__tabs; intros; inst_cofinites_with X.
    + assert ((X, □) :: θ ᵉ⊩ exp_anno eᵃ Aᵃ ᵉ^^ₜ ` X ⇝ exp_anno eᵈ Aᵈ ᵉ^^ₜ ` X).
      constructor; auto.
      eapply H0 with (θ':=(X, □) :: θ') in H7 ; eauto. dependent destruction H7; eauto.
      intros. auto. destruct_binds...
      apply binds_cons. apply H3...
      apply union_iff in H8. inversion H8.
      * rewrite ftvar_in_exp_open_exp_wrt_typ_rec_upper in H9...
        apply union_iff in H9. inversion H9. apply singleton_iff in H10. subst.
        apply binds_dom_contradiction in H11... contradiction. auto.  
      * rewrite ftvar_in_typ_open_typ_wrt_typ_rec_upper in H9...
        apply union_iff in H9. inversion H9. apply singleton_iff in H10. subst.
        apply binds_dom_contradiction in H11... contradiction. auto.
    + eapply trans_typ_reorder_ss with (θ:=(X, □) :: θ); eauto.
      intros. destruct_binds...
      apply binds_cons. apply H3...
      rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H7.
      apply union_iff in H7. inversion H7. apply singleton_iff in H8. subst.
      apply binds_dom_contradiction in H10... contradiction. auto.
  - simpl in *. dependent destruction H3...
    constructor... eapply trans_typ_reorder_ss with (θ:=θ)...
  - simpl in *. dependent destruction H3...
    constructor... eapply trans_typ_reorder_ss with (θ:=θ)...
Qed.

Lemma trans_exp_reorder_ss : forall θ θ' eᵃ eᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_exp eᵃ -> binds X b θ -> binds X b θ') ->
  θ ᵉ⊩ eᵃ ⇝ eᵈ ->
  θ' ᵉ⊩ eᵃ ⇝ eᵈ.
Proof with eauto.
  intros. apply trans_exp_lc_aexp in H2 as Hlc. 
  eapply trans_exp_reorder_ss' with (θ:=θ); eauto.
Qed.

Lemma trans_conts_reorder_ss : forall θ θ' csᵃ csᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_conts csᵃ -> binds X b θ -> binds X b θ') ->
  θ ᶜˢ⊩ csᵃ ⇝ csᵈ ->
  θ' ᶜˢ⊩ csᵃ ⇝ csᵈ
with trans_contd_reorder : forall θ θ' cdᵃ cdᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_contd cdᵃ -> binds X b θ -> binds X b θ') ->
  θ ᶜᵈ⊩ cdᵃ ⇝ cdᵈ ->
  θ' ᶜᵈ⊩ cdᵃ ⇝ cdᵈ.
Proof with eauto.
  intros.
  generalize dependent θ'. generalize dependent θ. generalize dependent csᵈ.
  induction csᵃ; simpl in *; intros; dependent destruction H2; constructor; 
    try eapply trans_typ_reorder_ss with (θ:=θ); eauto; 
    try eapply trans_exp_reorder_ss with (θ:=θ); eauto; 
    try eapply IHcᵃ with (θ:=θ)...
  intros.
  generalize dependent θ'. generalize dependent θ. generalize dependent cdᵈ.
  induction cdᵃ; simpl in *; intros; dependent destruction H2; constructor; 
    try eapply trans_typ_reorder_ss with (θ:=θ); eauto; 
    try eapply trans_exp_reorder_ss with (θ:=θ); eauto; 
    try eapply IHdᵃ with (θ:=θ)...
Qed.

Lemma trans_work_reorder_ss : forall θ θ' wᵃ wᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_work wᵃ -> binds X b θ -> binds X b θ') ->
  θ ʷ⊩ wᵃ ⇝ wᵈ ->
  θ' ʷ⊩ wᵃ ⇝ wᵈ.
Proof with eauto.
  intros. destruct wᵃ; simpl in *; dependent destruction H2; constructor;
    try eapply trans_typ_reorder_ss with (θ:=θ); eauto; 
    try eapply trans_exp_reorder_ss with (θ:=θ); eauto; 
    try eapply trans_conts_reorder_ss with (θ:=θ); eauto;
    try eapply trans_contd_reorder with (θ:=θ); eauto.
    intros. apply H1; auto.
    intros. apply H1; eauto.
Qed.
