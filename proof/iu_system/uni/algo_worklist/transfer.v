Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.notations.
Require Import ln_utils.


Inductive ss_bind := 
  | ss_bind__tvar_empty
  | ss_bind__stvar_empty
  | ss_bind__typ (T : typ).

Definition subst_set := list (atom * ss_bind).

Fixpoint ss_to_denv (θ : list (atom * ss_bind)) : denv := 
  match θ with 
  | nil => nil
  | (X , ss_bind__tvar_empty) :: θ' => (X ~ dbind_tvar_empty) ++ ss_to_denv θ'
  | (X , ss_bind__stvar_empty) :: θ' => (X ~ dbind_stvar_empty) ++ ss_to_denv θ'
  | (X , ss_bind__typ T) :: θ' => ss_to_denv θ'
  end.

Inductive wf_ss : subst_set -> Prop :=
  | wfss_nil : wf_ss nil
  | wfss_tvar : forall θ X,
      wf_ss θ -> 
      X `notin` dom θ ->
      wf_ss ((X , ss_bind__tvar_empty) :: θ)
  | wf_ss_stvar : forall θ X,
    wf_ss θ ->
    X `notin` dom θ ->
    wf_ss ((X, ss_bind__stvar_empty) :: θ)
  | wf_ss_ev : forall θ X T, 
    wf_ss θ  -> 
    X `notin` dom θ  ->
    d_mono_typ (ss_to_denv θ) T -> 
    wf_ss ((X , ss_bind__typ T) :: θ)
.

Lemma wf_uniq : forall Θ,
    wf_ss Θ -> uniq Θ.
Proof.
  induction 1; eauto.
Qed.


(* Lemma wf_mono : forall θ X T, 
  wf_ss θ -> binds X (sse_etvar T) θ -> dmono_typ T.
Proof.
  intros. induction H.
  - inversion H0.
  - inversion H0.
    inversion H2.
    auto.
  - inversion H0.
    + inversion H2.
    + auto.
  - inversion H0; auto.
    dependent destruction H4. auto.
Qed. *)

Inductive inst_typ : subst_set -> typ -> typ -> Prop := 
  | inst_typ__tvar : forall θ X, 
      wf_ss θ -> 
      binds X (ss_bind__tvar_empty) θ ->
      inst_typ θ (typ_var_f X) (typ_var_f X)
  | inst_typ__stvar : forall θ X, 
      wf_ss θ -> 
      binds X (ss_bind__stvar_empty) θ ->
      inst_typ θ (typ_var_f X) (typ_var_f X)
  | inst_typ__etvar : forall θ X A1,
      wf_ss θ ->
      binds X (ss_bind__typ A1) θ ->
      inst_typ θ (typ_var_f X) A1
  | inst_typ_unit : forall θ,
      wf_ss θ ->
      inst_typ θ typ_unit typ_unit
  | inst_typ__bot : forall θ,
      wf_ss θ ->
      inst_typ θ typ_bot typ_bot
  | inst_typ__top : forall θ,
      wf_ss θ ->
      inst_typ θ typ_top typ_top
  | instyp_arrow : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ,
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_typ θ A2ᵃ A2ᵈ ->
      inst_typ θ (typ_arrow A1ᵃ A2ᵃ) (typ_arrow A1ᵈ A2ᵈ)
  | instyp_all : forall θ L A1ᵃ A1ᵈ,
      (forall X, X `notin` L -> 
        inst_typ ((X, ss_bind__tvar_empty) :: θ) (open_typ_wrt_typ A1ᵃ (typ_var_f X)) (open_typ_wrt_typ A1ᵈ (typ_var_f X))
      ) ->
      inst_typ θ (typ_all A1ᵃ) (typ_all A1ᵈ)
  | instyp_intersection : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ,
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_typ θ A2ᵃ A2ᵈ ->
      inst_typ θ (typ_intersection A1ᵃ A2ᵃ) (typ_intersection A1ᵈ A2ᵈ)
  | instyp_union : forall θ A1ᵃ A2ᵃ A1ᵈ A2ᵈ,
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_typ θ A2ᵃ A2ᵈ ->
      inst_typ θ (typ_union A1ᵃ A2ᵃ) (typ_union A1ᵈ A2ᵈ)
  . 

Inductive inst_exp : subst_set -> exp -> exp -> Prop :=
  | inste_unit : forall θ,
      inst_exp θ exp_unit exp_unit
  | inste_var : forall θ x,
      inst_exp θ (exp_var_f x) (exp_var_f x)
  | inste_abs : forall L θ eᵃ eᵈ,
      (forall x, x `notin` L -> 
        inst_exp θ (open_exp_wrt_exp eᵃ (exp_var_f x))
                   (open_exp_wrt_exp eᵈ (exp_var_f x))
        ) ->
      inst_exp θ (exp_abs eᵃ) (exp_abs eᵈ)
  | inste_app : forall θ e1ᵃ e2ᵃ e1ᵈ e2ᵈ,
      inst_exp θ e1ᵃ e1ᵈ ->
      inst_exp θ e2ᵃ e2ᵈ ->
      inst_exp θ (exp_app e1ᵃ e2ᵃ) (exp_app e1ᵈ e2ᵈ)
  | inste_tabs : forall L θ bᵃ bᵈ,
      (forall X, X \notin L -> 
        inst_body ((X, ss_bind__tvar_empty) :: θ) 
                  (open_body_wrt_typ bᵃ (typ_var_f X))
                  (open_body_wrt_typ bᵈ (typ_var_f X))
      ) ->
      inst_exp θ (exp_tabs bᵃ) (exp_tabs bᵈ)
  | inste_tapp : forall θ eᵃ eᵈ A1ᵃ A1ᵈ,
      inst_exp θ eᵃ eᵈ ->
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_exp θ (exp_tapp eᵃ A1ᵃ) (exp_tapp eᵈ A1ᵈ)
  | inste_anno : forall θ eᵃ eᵈ A1ᵃ A1ᵈ, 
      inst_exp θ eᵃ eᵈ ->
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_exp θ (exp_anno eᵃ A1ᵃ) (exp_anno eᵈ A1ᵈ) 
with inst_body : subst_set -> body -> body -> Prop :=
  | inst_bodyanno : forall θ eᵃ eᵈ A1ᵃ A1ᵈ,
      inst_exp θ eᵃ eᵈ ->
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_body θ (body_anno eᵃ A1ᵃ) (body_anno eᵈ A1ᵈ)
.

Inductive inst_cont : subst_set -> cont -> cont -> Prop :=
  | inst_cont__infabs : forall θ cᵃ cᵈ,
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_infabs cᵃ) (cont_infabs cᵈ)
  | inst_cont__infabs_union : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    inst_typ θ A1ᵃ A1ᵈ ->
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_infabsunion A1ᵃ cᵃ) (cont_infabsunion A1ᵈ cᵈ)
  | inst_cont__infapp : forall θ eᵃ eᵈ cᵃ cᵈ,
    inst_exp θ eᵃ eᵈ ->
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_infapp eᵃ cᵃ) (cont_infapp eᵈ cᵈ)
  | inst_cont__inftapp : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    inst_typ θ A1ᵃ A1ᵈ ->
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_inftapp A1ᵃ cᵃ) (cont_inftapp A1ᵈ cᵈ)
  | inst_cont__inftappunion : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
    inst_typ θ A1ᵃ A1ᵈ ->
    inst_typ θ A2ᵃ A2ᵈ ->
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_inftappunion A1ᵃ A2ᵃ cᵃ) (cont_inftappunion A1ᵈ A2ᵈ cᵈ)
  | inst_cont__unioninftapp : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    inst_typ θ A1ᵃ A1ᵈ ->
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_unioninftapp A1ᵃ cᵃ) (cont_unioninftapp A1ᵈ cᵈ)
  | inst_cont__unioninfabs : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    inst_typ θ A1ᵃ A1ᵈ ->
    inst_cont θ cᵃ cᵈ ->
    inst_cont θ (cont_unioninfabs A1ᵃ cᵃ) (cont_unioninfabs A1ᵈ cᵈ)    
  | inst_cont__sub : forall θ A1ᵃ A1ᵈ,
    inst_typ θ A1ᵃ A1ᵈ ->
    inst_cont θ (cont_sub A1ᵃ) (cont_sub A1ᵈ)
.


Inductive inst_work : subst_set -> work -> work -> Prop :=
  | inst_work__inf : forall Θ eᵃ eᵈ cᵃ cᵈ,
      inst_exp Θ eᵃ eᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_infer eᵃ cᵃ) (work_infer eᵈ cᵈ)
  | inst_work__chk : forall Θ eᵃ eᵈ A1ᵃ A1ᵈ,
      inst_exp Θ eᵃ eᵈ ->
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_work Θ (work_check eᵃ A1ᵃ) (work_check eᵈ A1ᵈ)
  | inst_work__infabs : forall Θ A1ᵃ A1ᵈ  cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_infabs A1ᵃ cᵃ ) (work_infabs A1ᵈ cᵈ)
  | inst_work__infabsunion : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_typ Θ A2ᵃ A2ᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_infabsunion A1ᵃ A2ᵃ cᵃ) (work_infabsunion A1ᵈ A2ᵈ cᵈ)
  | inst_work__infapp : forall Θ A1ᵃ A1ᵈ eᵃ eᵈ cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_exp Θ eᵃ eᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_infapp A1ᵃ eᵃ cᵃ) (work_infapp A1ᵈ eᵈ cᵈ)
  | inst_work__inftapp : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_typ Θ A2ᵃ A2ᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_inftapp A1ᵃ A2ᵃ cᵃ) (work_inftapp A1ᵈ A2ᵈ cᵈ)
  | inst_work__sub : forall θ A1ᵃ A1ᵈ B1ᵃ B1ᵈ,
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_typ θ B1ᵃ B1ᵈ ->
      inst_work θ (work_sub A1ᵃ B1ᵃ) (work_sub A1ᵈ B1ᵈ)
  | inst_work__inftappunion : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ B1ᵃ B1ᵈ cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_typ Θ A2ᵃ A2ᵈ ->
      inst_typ Θ B1ᵃ B1ᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_inftappunion A1ᵃ A2ᵃ B1ᵃ cᵃ) (work_inftappunion A1ᵈ A2ᵈ B1ᵈ cᵈ)
  | inst_work__unioninftapp : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_typ Θ A2ᵃ A2ᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_unioninftapp A1ᵃ A2ᵃ cᵃ) (work_unioninftapp A1ᵈ A2ᵈ cᵈ)
  | inst_work__unioninfabs : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      inst_typ Θ A1ᵃ A1ᵈ ->
      inst_typ Θ A2ᵃ A2ᵈ ->
      inst_cont Θ cᵃ cᵈ ->
      inst_work Θ (work_unioninfabs A1ᵃ A2ᵃ cᵃ) (work_unioninfabs A1ᵈ A2ᵈ cᵈ)
  | inst_work__applycont : forall θ cᵃ cᵈ A1ᵃ A1ᵈ,
      inst_cont θ cᵃ cᵈ ->
      inst_typ θ A1ᵃ A1ᵈ ->
      inst_work θ (work_apply cᵃ A1ᵃ) (work_apply cᵈ A1ᵈ)
.

Reserved Notation "θ ⫦ Ω ⇝ Γ ⫣ θ'"
  (at level 65, Ω at next level, Γ at next level, no associativity).
Inductive inst_worklist : subst_set -> aworklist -> dworklist -> subst_set -> Prop := 
  | inst_wl__empty : forall θ, 
      wf_ss θ -> 
      θ ⫦ aworklist_empty ⇝ dworklist_empty ⫣ θ
  | inst_wl__conswork : forall θ θ' Γ Ω  wᵃ wᵈ, 
      wf_ss θ -> 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      inst_work θ' wᵃ wᵈ ->
      θ ⫦ aworklist_conswork Γ wᵃ ⇝ dworklist_conswork Ω wᵈ ⫣ θ'
  | inst_wl__cons_tvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      θ ⫦ aworklist_constvar Γ X abind_tvar_empty ⇝ dworklist_constvar Ω X dbind_tvar_empty ⫣  (X, ss_bind__tvar_empty) :: θ'
  | inst_wl__cons_stvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      θ ⫦ aworklist_constvar Γ X abind_stvar_empty ⇝ dworklist_constvar Ω X dbind_stvar_empty ⫣  (X, ss_bind__stvar_empty) :: θ'
  | inst_wl__cons_var : forall θ θ' Γ Ω A1ᵃ A1ᵈ x, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      inst_typ θ' A1ᵃ A1ᵈ ->
      θ ⫦ aworklist_consvar Γ x (abind_typ A1ᵃ) ⇝ dworklist_consvar Ω x (dbind_typ A1ᵈ) ⫣ θ'
  | inst_wl_ev : forall θ θ' Γ Ω A1ᵃ A1ᵈ B1ᵃ B1ᵈ T1 X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' -> 
      inst_typ θ' A1ᵃ A1ᵈ ->
      inst_typ θ' B1ᵃ B1ᵈ ->
      (* TODO: check A1 < T1, T1 < B1  *)
      θ ⫦ aworklist_consvar Γ X (abind_bound A1ᵃ B1ᵃ) ⇝ dworklist_conswork Ω (work_sub A1ᵈ B1ᵈ) ⫣  (X, ss_bind__typ T1) :: θ'
where "θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ'" := (inst_worklist θ Γᵃ Γᵈ θ').


Reserved Notation "θ ⫦ Ω ⇝' Γ ⫣ θ'"
  (at level 65, Ω at next level, Γ at next level, no associativity).
Inductive inst_worklist' : subst_set -> aworklist -> dworklist -> subst_set -> Prop := 
  | inst_wl'__empty : forall θ, 
      wf_ss θ -> 
      θ ⫦ aworklist_empty ⇝' dworklist_empty ⫣ θ
  | inst_wl'__conswork : forall θ θ' Γ Ω  wᵃ wᵈ, 
      wf_ss θ -> 
      θ ⫦ Γ ⇝' Ω ⫣ θ' ->
      inst_work θ' wᵃ wᵈ ->
      θ ⫦ aworklist_conswork Γ wᵃ ⇝' dworklist_conswork Ω wᵈ ⫣ θ'
  | inst_wl'__cons_tvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝' Ω ⫣ θ' ->
      θ ⫦ aworklist_constvar Γ X abind_tvar_empty ⇝' dworklist_constvar Ω X dbind_tvar_empty ⫣  (X, ss_bind__tvar_empty) :: θ'
  | inst_wl'__cons_stvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝' Ω ⫣ θ' ->
      θ ⫦ aworklist_constvar Γ X abind_stvar_empty ⇝' dworklist_constvar Ω X dbind_stvar_empty ⫣  (X, ss_bind__stvar_empty) :: θ'
  | inst_wl'__cons_var : forall θ θ' Γ Ω A1ᵃ A1ᵈ x, 
      θ ⫦ Γ ⇝' Ω ⫣ θ' ->
      inst_typ θ' A1ᵃ A1ᵈ ->
      θ ⫦ aworklist_consvar Γ x (abind_typ A1ᵃ) ⇝' dworklist_consvar Ω x (dbind_typ A1ᵈ) ⫣ θ'
  | inst_wl'_ev : forall θ θ' Γ Ω Aᵃ Aᵈ Bᵃ Bᵈ T X, 
      θ ⫦ Γ ⇝' Ω ⫣ θ' -> 
      inst_typ θ' Aᵃ Aᵈ ->
      inst_typ θ' Bᵃ Bᵈ ->
      dwl_to_denv Ω ⊢ Aᵈ <: T ->
      dwl_to_denv Ω ⊢ T <: Bᵈ ->
      (* TODO: check A1 < T1, T1 < B1  *)
      θ ⫦ aworklist_consvar Γ X (abind_bound Aᵃ Bᵃ) ⇝' Ω ⫣  (X, ss_bind__typ T) :: θ'
where "θ ⫦ Γᵃ ⇝' Γᵈ ⫣ θ'" := (inst_worklist' θ Γᵃ Γᵈ θ').


(* Hint Constructors inst_typ : transfer.
Hint Constructors inst_worklist : transfer.

Lemma fv_ss_ld_ctx_dom: forall θ x,
  x `notin` fv_ss θ -> x `notin` ld_ctx_dom (ss_to_ctx θ).
Proof.
  induction θ; simpl; intros; auto.
  - destruct a; destruct s.
    + simpl in *. auto.
    + auto.
Qed.





Lemma notin_wf_t_notin_ss: forall t θ x,
  ss_to_ctx θ ⊢ t -> x `notin` fv_ss θ -> x `notin` fv_ld_type t.
Proof.
  induction t; intros.
  - auto.
  - simpl. dependent destruction H.
    inst_cofinites_by (L `union` singleton x).
    eapply ld_wf_type_fv with (x:=x) in H.
    rewrite fv_ld_type_open_ld_type_wrt_ld_type_lower.
    eauto. simpl. auto.
    apply notin_add; auto.
    apply fv_ss_ld_ctx_dom. auto.
  - simpl. dependent destruction H; apply notin_union; eauto.
  - simpl. dependent destruction H; apply notin_union; eauto.
  - simpl. dependent destruction H; apply notin_union; eauto.
  - auto.
  - dependent destruction H; auto.
    clear H.
    induction θ; auto.
    + inversion H0.
    + destruct a. destruct s; simpl in *.
      inversion H0; subst; auto.
      auto.
Qed.

Lemma notin_ss_notin_inst : forall θ x ex t,
    wf_ss θ ->
    ex : t ∈ θ -> 
    x `notin` fv_ss θ ->
    x `notin` fv_ld_type t.
Proof.
  intro θ.
  induction θ; intros.
  - inversion H0.
  - inversion H0. destruct a; destruct s.
    + inversion H2.
    + inversion H2. subst. inversion H. subst. 
      simpl in H1. eapply notin_wf_t_notin_ss; eauto.
    + eapply IHθ; eauto. inversion H; auto.
      destruct a; destruct s; simpl in *. auto. auto.
Qed.

Lemma inst_t_lc : forall θ Aᵃ Aᵈ, 
  θ ⫦ Aᵃ ⇝ Aᵈ -> 
  lc_la_type Aᵃ /\ lc_ld_type Aᵈ.
Proof.
  intros.
  induction H; try (split; destruct_conjs; auto; fail).
  - split. auto. 
    induction θ.
    + inversion H0.
    + destruct a. inversion H0.
      * inversion H1. subst. inversion H.
        subst. now apply ld_mono_is_ld_lc.
      * inversion H. apply IHθ; auto. auto.
  - split; inst_cofinites_by L.
    + apply lc_la_t_forall_exists with (x1:=x). intuition.
    + apply lc_ld_t_forall_exists with (x1:=x). intuition.
Qed.


Ltac inversion_eq :=
  repeat
    match goal with 
        | H : ?a = ?b |-  _ => dependent destruction H
      end.

Lemma inst_A_det : forall θ Aᵃ A₁ᵈ,
  uniq θ -> 
  θ ⫦ Aᵃ ⇝ A₁ᵈ -> 
  forall A₂ᵈ, θ ⫦ Aᵃ ⇝ A₂ᵈ -> 
    A₁ᵈ = A₂ᵈ.
Proof.
  induction 2; (intros e₂ᵈ H2; dependent destruction H2; auto). 
  - specialize (binds_unique _ _ _ _ _ H1 H3).
    intros. specialize (H4 H). inversion_eq. auto.
  - specialize (IHinst_type1 H _ H2_).
    specialize (IHinst_type2 H _ H2_0).
    subst. auto.
  - inst_cofinites_by (L `union` L0 `union` (fv_ld_type A) `union` (fv_ld_type A0)).  
    assert (A = A0).
    + eapply open_ld_type_wrt_ld_type_inj with (x1:=x); auto.
    + subst. auto. 
Qed.


Lemma not_in_dom_not_in_fv_ss: forall x θ,
  x `notin` dom θ -> 
  x `notin` fv_ss θ.
Proof.
  induction θ; auto.
  destruct a. destruct s; simpl; 
  intros; apply notin_union; auto.
Qed.


Lemma inst_e_rename : forall θ Aᵃ Aᵈ x x'
  , θ ⫦ Aᵃ ⇝ Aᵈ 
  -> x `notin` dom θ
  -> θ ⫦ [`ᵃ x' /ᵃ x] Aᵃ ⇝ [`ᵈ x' /ᵗ x] Aᵈ.
Proof with auto with transfer.
  intros. induction H; simpl; auto...
  - unfold eq_dec. destruct (EqDec_eq_of_X x0 x); auto...
  - rewrite subst_ld_type_fresh_eq. auto...
    eapply notin_ss_notin_inst; eauto.
    now apply not_in_dom_not_in_fv_ss. 
  - eapply inst_t_forall with (L := L `union` singleton x). intros.
    rewrite_la_subst_open_var. rewrite_ld_subst_open_var. auto.
Qed.


Lemma inst_e_rev_subst' : forall tᵃ tᵈ x θ Aᵃ,
  lc_la_type Aᵃ -> 
  x `notin` (fx_la_type tᵃ `union` fv_ss θ) -> 
  θ ⫦ tᵃ ⇝ tᵈ -> 
  forall A'ᵈ, θ ⫦ [tᵃ /ᵃ x] Aᵃ ⇝ A'ᵈ
    -> exists Aᵈ, [tᵈ /ᵗ x] Aᵈ = A'ᵈ /\ θ ⫦ Aᵃ ⇝ Aᵈ.
Proof with auto with transfer.
  intros * Hlc Hfv Hinstt.
  induction Hlc; intros * HinstA; simpl in *.
  - inversion HinstA. exists ld_t_int. simpl. split; auto...
  - specialize (inst_t_lc _ _ _ Hinstt). intros.
    dependent destruction HinstA.
    inst_cofinites_by (L `union` singleton x `union` fv_ld_type tᵈ `union`  fv_ld_type A `union` dom θ `union` fx_la_type t). 
    replace (`ᵃ x0) with ([tᵃ /ᵃ x] (`ᵃ x0)) in H1 by (apply subst_la_type_fresh_eq; auto).
    rewrite <- subst_la_type_open_la_type_wrt_la_type in H1.
    specialize (H0 _ _ H1).
    destruct H0 as [A'ᵈ HinstA'ᵈ].
    exists (ld_t_forall (close_ld_type_wrt_ld_type x0 A'ᵈ)). simpl.
    rewrite subst_ld_type_close_ld_type_wrt_ld_type. 
    + split.
      * f_equal. destruct_conjs. apply ld_type_open_r_close_l; auto. 
      * eapply inst_t_forall with (L:=L); intros.
        rewrite (subst_la_type_intro x0) by auto.
        rewrite (subst_ld_type_intro x0) by (apply close_dtyp_notin).
        apply inst_e_rename; auto.
        rewrite open_ld_type_wrt_ld_type_close_ld_type_wrt_ld_type. intuition.
    + intuition. 
    + auto.
    + auto.
    + intuition.
  - dependent destruction HinstA.
    specialize (IHHlc1 _ HinstA1). destruct IHHlc1 as [t₁ᵈ HinstA1inv].
    specialize (IHHlc2 _ HinstA2). destruct IHHlc2 as [t₂ᵈ HinstA2inv].
    exists (ld_t_arrow t₁ᵈ t₂ᵈ). destruct_conjs. split; simpl; subst; auto...
  - exists (ld_t_var_f x5).
    destruct (x5 == x).  
    + subst. simpl. destruct (x == x).
      * split.
        -- assert (uniq θ) as Huniq by (apply wf_uniq; eapply inst_t_wf_ss; eauto).
           specialize (inst_A_det _ _ _ Huniq Hinstt). intros.
           specialize (H _ HinstA). auto.
        -- constructor. eapply inst_t_wf_ss. eauto.
      * contradiction.
    + simpl. unfold eq_dec. destruct (EqDec_eq_of_X x5 x).
      * contradiction.
      * inversion HinstA; split; auto... 
  - simpl in *. exists A'ᵈ. split.
    + rewrite subst_ld_type_fresh_eq. auto.
      inversion HinstA.
      eapply notin_ss_notin_inst; eauto.
    + auto.
Qed.

Lemma inst_wf : forall θ tᵃ tᵈ,
  θ ⫦ tᵃ ⇝ tᵈ -> wf_ss θ.
Proof.
  intros. induction H; auto.
  - inst_cofinites_by L. auto.
Qed.

Lemma inst_e_rev_subst : forall A'ᵈ θ tᵃ tᵈ x Aᵃ,
  lc_la_type Aᵃ ->
  x `notin` (fx_la_type tᵃ `union` fv_ss θ) -> 
  θ ⫦ tᵃ ⇝ tᵈ → θ ⫦ [tᵃ /ᵃ x] Aᵃ ⇝ A'ᵈ ->
  exists Aᵈ, [tᵈ /ᵗ x] Aᵈ = A'ᵈ ∧ θ ⫦ Aᵃ ⇝ Aᵈ.
Proof.
  intros.  
  specialize (inst_e_rev_subst' _ _ _ _  _ H H0 H1 A'ᵈ).
  intros.
  specialize (H3 H2).
  auto.
Qed.


Lemma inst_subst : forall θ x tᵈ Aᵃ Aᵈ, 
  lc_la_type Aᵃ ->
  x `notin` (fx_la_type Aᵃ)->
  (θ; x : tᵈ) ⫦ Aᵃ ⇝ Aᵈ -> 
  θ ⫦ [ld_type_to_la_type tᵈ /^ᵃ x] Aᵃ ⇝ Aᵈ.
Proof.
  intros * Hlc Hfv Hinstopen.
  generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros.
  - inversion Hinstopen. econstructor.
    inversion H. auto.
  - dependent destruction Hinstopen.
    eapply inst_t_forall with (L:=singleton x `union` fx_la_type t `union` fex_la_type t `union` L). intros.
    + intros.
      rewrite la_type_ex_subst_open_comm.
      * eapply H0.
        apply fx_la_type_open_la_type_notin; auto.
        auto.
      * inst_cofinites_with x0.
        apply inst_wf in H1.
        inversion H1.
        apply ld_type_to_la_type_keeps_lc. apply ld_mono_is_ld_lc. auto.
      * auto.
  - dependent destruction Hinstopen.
    econstructor; auto.
  - destruct (x5 == x).
    + subst.
      apply notin_singleton_1 in Hfv. 
      contradiction.
    + dependent destruction Hinstopen.
      constructor. inversion H. auto. 
  - dependent destruction Hinstopen. 
    destruct (ex5 == x). 
    + subst.
      apply binds_unique with (a:=sse_ev tᵈ) in H0. inversion H0. subst. inversion H.
      * apply inst_ld_type_to_la_type; auto. 
        apply ld_mono_is_ld_lc. auto.
      * constructor; auto.
      * apply wf_uniq. auto.
    + inversion H0. 
      * dependent destruction H1.
        contradiction.
      * econstructor; auto.      
        dependent destruction H. auto.
Qed. *)


(* Lemma transfer_reorder: forall Γᵃ Γ'ᵈ θ' x t m Γ'ᵃ,
  reorder Γᵃ x t m la_wl_nil Γ'ᵃ ->
  inst_worklist nil Γ'ᵃ Γ'ᵈ θ' ->
  exists Γᵈ θ, inst_worklist nil Γᵃ Γᵈ θ.
Proof.
  intros. 
  generalize dependent θ'.
  generalize dependent Γ'ᵈ.
  induction H; intros.
  - admit.
  - admit.
  - dependent destruction H1.
    specialize (IHreorder Γᵈ θ' H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].  
    exists (ld_wl_cons_tv Γ'ᵈ y), θ''.
    constructor. auto.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ].
    exists Γ'ᵈ.
    econstructor; auto. admit.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ].
    exists Γ'ᵈ.
    econstructor; eauto. admit.
  - dependent destruction H0.
    admit.
Admitted.

Lemma transfer_reorder': forall Γᵃ Γᵈ θ x t m Γ'ᵃ,
  reorder Γᵃ x t m la_wl_nil Γ'ᵃ ->
  inst_worklist nil Γᵃ Γᵈ θ -> 
  exists Γ'ᵈ θ', inst_worklist nil Γ'ᵃ Γ'ᵈ θ'.
Proof.
  intros. 
  generalize dependent θ.
  generalize dependent Γᵈ.
  induction H; intros.
  - exists Γᵈ, θ. admit.
  - admit.
  - dependent destruction H1.
    specialize (IHreorder Γᵈ θ' H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].  
    exists (ld_wl_cons_tv Γ'ᵈ y), θ''.
    econstructor. auto.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].
    exists Γ'ᵈ, (θ''; y : tᵈ).
    econstructor; auto.
    + admit.
    + admit.
  - dependent destruction H1.
    specialize (IHreorder _ _ H1).
    destruct IHreorder as [Γ'ᵈ [θ'']].
    exists Γ'ᵈ, (θ''; y : tᵈ).
    econstructor; eauto.
    + admit.
    + admit.
  - dependent destruction H0.
Admitted. *)


Definition transfer (Γ : aworklist) (Ω : dworklist)  : Prop :=
  exists θ', inst_worklist nil Γ Ω θ'.