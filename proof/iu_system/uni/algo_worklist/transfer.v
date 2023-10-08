Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import ln_utils.



Definition subst_set := denv.

Fixpoint ss_to_denv (θ : subst_set) : denv := 
  match θ with 
  | nil => nil
  | (X , dbind_tvar_empty) :: θ' => (X ~ dbind_tvar_empty) ++ ss_to_denv θ'
  | (X , dbind_stvar_empty) :: θ' => (X ~ dbind_stvar_empty) ++ ss_to_denv θ'
  | (X , dbind_typ T) :: θ' => ss_to_denv θ'
  end.

Inductive wf_ss : subst_set -> Prop :=
  | wfss__nil : wf_ss nil
  | wfss__tvar : forall θ X,
      wf_ss θ -> 
      X `notin` dom θ ->
      wf_ss ((X , dbind_tvar_empty) :: θ)
  | wf_ss__stvar : forall θ X,
    wf_ss θ ->
    X `notin` dom θ ->
    wf_ss ((X, dbind_stvar_empty) :: θ)
  | wf_ss__etvar : forall θ X T, 
    wf_ss θ  -> 
    X `notin` dom θ  ->
    d_mono_typ (ss_to_denv θ) T -> 
    wf_ss ((X , dbind_typ T) :: θ)
.

Lemma wf_uniq : forall Θ,
    wf_ss Θ -> uniq Θ.
Proof.
  induction 1; eauto.
Qed.


Inductive trans_typ : subst_set -> typ -> typ -> Prop := 
  | trans_typ__tvar : forall θ X, 
      wf_ss θ -> 
      binds X (dbind_tvar_empty) θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__stvar : forall θ X, 
      wf_ss θ -> 
      binds X (dbind_stvar_empty) θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__etvar : forall θ X A1,
      wf_ss θ ->
      binds X (dbind_typ A1) θ ->
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
      (forall X, X `notin` L -> 
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
      (forall x, x `notin` L -> 
        trans_exp θ (open_exp_wrt_exp eᵃ (exp_var_f x))
                   (open_exp_wrt_exp eᵈ (exp_var_f x))
        ) ->
      trans_exp θ (exp_abs eᵃ) (exp_abs eᵈ)
  | trans_exp__app : forall θ e1ᵃ e2ᵃ e1ᵈ e2ᵈ,
      trans_exp θ e1ᵃ e1ᵈ ->
      trans_exp θ e2ᵃ e2ᵈ ->
      trans_exp θ (exp_app e1ᵃ e2ᵃ) (exp_app e1ᵈ e2ᵈ)
  | trans_exp__tabs : forall L θ bᵃ bᵈ,
      (forall X, X \notin L -> 
        inst_body ((X, dbind_tvar_empty) :: θ) 
                  (open_body_wrt_typ bᵃ (typ_var_f X))
                  (open_body_wrt_typ bᵈ (typ_var_f X))
      ) ->
      trans_exp θ (exp_tabs bᵃ) (exp_tabs bᵈ)
  | trans_exp__tapp : forall θ eᵃ eᵈ A1ᵃ A1ᵈ,
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_exp θ (exp_tapp eᵃ A1ᵃ) (exp_tapp eᵈ A1ᵈ)
  | trans_exp__anno : forall θ eᵃ eᵈ A1ᵃ A1ᵈ, 
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_exp θ (exp_anno eᵃ A1ᵃ) (exp_anno eᵈ A1ᵈ) 
with inst_body : subst_set -> body -> body -> Prop :=
  | inst_body__anno : forall θ eᵃ eᵈ A1ᵃ A1ᵈ,
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      inst_body θ (body_anno eᵃ A1ᵃ) (body_anno eᵈ A1ᵈ)
.

Inductive trans_cont : subst_set -> cont -> cont -> Prop :=
  | trans_cont__infabs : forall θ cᵃ cᵈ,
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_infabs cᵃ) (cont_infabs cᵈ)
  | trans_cont__infabs_union : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_infabsunion A1ᵃ cᵃ) (cont_infabsunion A1ᵈ cᵈ)
  | trans_cont__infapp : forall θ eᵃ eᵈ cᵃ cᵈ,
    trans_exp θ eᵃ eᵈ ->
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_infapp eᵃ cᵃ) (cont_infapp eᵈ cᵈ)
  | trans_cont__inftapp : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_inftapp A1ᵃ cᵃ) (cont_inftapp A1ᵈ cᵈ)
  | trans_cont__inftappunion : forall θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_typ θ A2ᵃ A2ᵈ ->
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_inftappunion A1ᵃ A2ᵃ cᵃ) (cont_inftappunion A1ᵈ A2ᵈ cᵈ)
  | trans_cont__unioninftapp : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_unioninftapp A1ᵃ cᵃ) (cont_unioninftapp A1ᵈ cᵈ)
  | trans_cont__unioninfabs : forall θ A1ᵃ A1ᵈ cᵃ cᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_cont θ cᵃ cᵈ ->
    trans_cont θ (cont_unioninfabs A1ᵃ cᵃ) (cont_unioninfabs A1ᵈ cᵈ)    
  | trans_cont__sub : forall θ A1ᵃ A1ᵈ,
    trans_typ θ A1ᵃ A1ᵈ ->
    trans_cont θ (cont_sub A1ᵃ) (cont_sub A1ᵈ)
.


Inductive trans_work : subst_set -> work -> work -> Prop :=
  | trans_work__inf : forall Θ eᵃ eᵈ cᵃ cᵈ,
      trans_exp Θ eᵃ eᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_infer eᵃ cᵃ) (work_infer eᵈ cᵈ)
  | trans_work__chk : forall Θ eᵃ eᵈ A1ᵃ A1ᵈ,
      trans_exp Θ eᵃ eᵈ ->
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_work Θ (work_check eᵃ A1ᵃ) (work_check eᵈ A1ᵈ)
  | trans_work__infabs : forall Θ A1ᵃ A1ᵈ  cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_infabs A1ᵃ cᵃ ) (work_infabs A1ᵈ cᵈ)
  | trans_work__infabsunion : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_typ Θ A2ᵃ A2ᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_infabsunion A1ᵃ A2ᵃ cᵃ) (work_infabsunion A1ᵈ A2ᵈ cᵈ)
  | trans_work__infapp : forall Θ A1ᵃ A1ᵈ eᵃ eᵈ cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_exp Θ eᵃ eᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_infapp A1ᵃ eᵃ cᵃ) (work_infapp A1ᵈ eᵈ cᵈ)
  | trans_work__inftapp : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_typ Θ A2ᵃ A2ᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_inftapp A1ᵃ A2ᵃ cᵃ) (work_inftapp A1ᵈ A2ᵈ cᵈ)
  | trans_work__sub : forall θ A1ᵃ A1ᵈ B1ᵃ B1ᵈ,
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_typ θ B1ᵃ B1ᵈ ->
      trans_work θ (work_sub A1ᵃ B1ᵃ) (work_sub A1ᵈ B1ᵈ)
  | trans_work__inftappunion : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ B1ᵃ B1ᵈ cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_typ Θ A2ᵃ A2ᵈ ->
      trans_typ Θ B1ᵃ B1ᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_inftappunion A1ᵃ A2ᵃ B1ᵃ cᵃ) (work_inftappunion A1ᵈ A2ᵈ B1ᵈ cᵈ)
  | trans_work__unioninftapp : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_typ Θ A2ᵃ A2ᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_unioninftapp A1ᵃ A2ᵃ cᵃ) (work_unioninftapp A1ᵈ A2ᵈ cᵈ)
  | trans_work__unioninfabs : forall Θ A1ᵃ A1ᵈ A2ᵃ A2ᵈ cᵃ cᵈ,
      trans_typ Θ A1ᵃ A1ᵈ ->
      trans_typ Θ A2ᵃ A2ᵈ ->
      trans_cont Θ cᵃ cᵈ ->
      trans_work Θ (work_unioninfabs A1ᵃ A2ᵃ cᵃ) (work_unioninfabs A1ᵈ A2ᵈ cᵈ)
  | trans_work__applycont : forall θ cᵃ cᵈ A1ᵃ A1ᵈ,
      trans_cont θ cᵃ cᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_work θ (work_apply cᵃ A1ᵃ) (work_apply cᵈ A1ᵈ)
.


Reserved Notation "θ ⫦ Ω ⇝ Γ ⫣ θ'"
  (at level 65, Ω at next level, Γ at next level, no associativity).
Inductive trans_worklist : subst_set -> aworklist -> dworklist -> subst_set -> Prop := 
  | inst_wl__empty : forall θ, 
      wf_ss θ -> 
      θ ⫦ aworklist_empty ⇝ dworklist_empty ⫣ θ
  | inst_wl__conswork : forall θ θ' Γ Ω  wᵃ wᵈ, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      trans_work θ' wᵃ wᵈ ->
      θ ⫦ aworklist_conswork Γ wᵃ ⇝ dworklist_conswork Ω wᵈ ⫣ θ'
  | inst_wl__cons_tvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      θ ⫦ aworklist_constvar Γ X abind_tvar_empty ⇝ dworklist_constvar Ω X dbind_tvar_empty ⫣  (X, dbind_tvar_empty) :: θ'
  | inst_wl__cons_stvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      θ ⫦ aworklist_constvar Γ X abind_stvar_empty ⇝ dworklist_constvar Ω X dbind_stvar_empty ⫣  (X, dbind_stvar_empty) :: θ'
  | inst_wl__cons_var : forall θ θ' Γ Ω A1ᵃ A1ᵈ x, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      trans_typ θ' A1ᵃ A1ᵈ ->
      θ ⫦ aworklist_consvar Γ x (abind_typ A1ᵃ) ⇝ dworklist_consvar Ω x (dbind_typ A1ᵈ) ⫣ θ'
  | inst_wl_ev : forall θ θ' Γ Ω Aᵃ Aᵈ Bᵃ Bᵈ T X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' -> 
      trans_typ θ' Aᵃ Aᵈ ->
      trans_typ θ' Bᵃ Bᵈ ->
      d_mono_typ (ss_to_denv θ' ) T ->
      dwl_to_denv Ω ⊢ Aᵈ <: T ->
      dwl_to_denv Ω ⊢ T <: Bᵈ ->
      θ ⫦ aworklist_constvar Γ X (abind_bound Aᵃ Bᵃ) ⇝ Ω ⫣  (X, dbind_typ T) :: θ'
where "θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ'" := (trans_worklist θ Γᵃ Γᵈ θ').

Hint Constructors trans_typ : Hdb_transfer.


Lemma trans_work_not_in_ss : forall θ Γ Ω X,
  nil ⫦ Γ ⇝ Ω ⫣ θ -> X ∉ dom (awl_to_aenv Γ) -> X ∉ dom θ.
Proof with auto.
  intros. dependent induction H; simpl in *...
Qed.


Lemma wf_ss_uniq : forall θ,
  wf_ss θ -> uniq θ.
Proof.
  intros. induction H; auto.
Qed.

Hint Resolve wf_ss_uniq : Hdb_transfer.

Lemma wf_ss_etvar_tvar_false : forall θ X A,
  wf_ss θ -> X ~ A ∈ θ -> X ~ ▫ ∈ θ -> False.
Proof.
  intros. apply wf_ss_uniq in H.
  specialize (binds_unique _ _ _ _ _ H0 H1 H).
  intros. inversion H2.
Qed.

Lemma wf_ss_etvar_stvar_false : forall θ X A,
  wf_ss θ -> X ~ A ∈ θ -> X ~ ▪ ∈ θ -> False.
Proof.
  intros. apply wf_ss_uniq in H.
  specialize (binds_unique _ _ _ _ _ H0 H1 H).
  intros. inversion H2.
Qed.


Lemma a_wf_wl_wf_ss : forall θ Γ Ω,  
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> wf_ss θ.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H...
  - econstructor... eapply trans_work_not_in_ss...
  - econstructor... eapply trans_work_not_in_ss...
  - econstructor... eapply trans_work_not_in_ss... 
Qed.


Hint Resolve a_wf_wl_wf_ss : Hdb_transfer.

Notation "θ ⫦ᵗ Aᵃ ⇝ Aᵈ" := (trans_typ θ Aᵃ Aᵈ)
  (at level 65, Aᵃ at next level, no associativity).



Lemma trans_typ_wf_ss : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss θ.
Proof with auto with Hdb_transfer.
  intros. induction H...
  - inst_cofinites_by L.
    dependent destruction H0...
Qed.


Lemma trans_typ_det : forall θ Aᵃ A₁ᵈ A₂ᵈ,
  uniq θ -> 
  θ ⫦ᵗ Aᵃ ⇝ A₁ᵈ -> 
  θ ⫦ᵗ Aᵃ ⇝ A₂ᵈ -> 
  A₁ᵈ = A₂ᵈ.
Proof with eauto with Hdb_transfer.
  intros. generalize dependent A₂ᵈ.
  induction H0; (intros A₂ᵈ H2; dependent destruction H2; auto).
  - exfalso. eapply wf_ss_etvar_tvar_false... 
  - exfalso. eapply wf_ss_etvar_stvar_false... 
  - exfalso. eapply wf_ss_etvar_tvar_false...
  - exfalso. eapply wf_ss_etvar_stvar_false... 
  - specialize (binds_unique _ _ _ _ _ H1 H3 H). intros.
    dependent destruction H4... 
  - specialize (IHtrans_typ1 H _ H2_).
    specialize (IHtrans_typ2 H _ H2_0).
    subst...
  - inst_cofinites_by (L `union` L0 `union` (ftvar_in_typ A1ᵈ) `union` (ftvar_in_typ A1ᵈ0) `union`  dom θ) using_name X.  
    apply f_equal.
    + eapply open_typ_wrt_typ_inj with (X1:=X); auto.
  - specialize (IHtrans_typ1 H _ H2_).
    specialize (IHtrans_typ2 H _ H2_0).
    subst...
  - specialize (IHtrans_typ1 H _ H2_).
    specialize (IHtrans_typ2 H _ H2_0).
    subst...
Qed.


Hint Constructors trans_typ : Hdb_transfer.
Hint Constructors trans_cont : Hdb_transfer.
Hint Constructors trans_work : Hdb_transfer.
Hint Constructors trans_worklist : Hdb_transfer.
Hint Constructors wf_ss : Hdb_transfer.


Hint Resolve a_wf_wl_wf_ss : Hdb_a_wl_red_soundness.


Lemma etvar_in_awl_in_ss : forall θ θ' Γ Ω X A B,
   ⊢ᵃ Γ -> θ ⫦ Γ ⇝ Ω ⫣ θ' -> binds X (abind_bound A B) (awl_to_aenv Γ) ->
   exists Tᵈ, binds X Tᵈ θ'.
Proof with eauto with Hdb_transfer.
  intros. 
  generalize dependent Ω. generalize dependent θ. generalize dependent θ'.
    induction H; intros.
  - inversion H1.
  - simpl in H1. inversion H1.
    inversion H4. dependent destruction H3.
    eapply IHa_wf_wl...
  - simpl in H1. inversion H1. inversion H3.
    dependent destruction H2.
    apply IHa_wf_wl in H2... destruct H2 as [Tᵈ].
    exists Tᵈ. apply binds_cons...
  - simpl in H1. inversion H1. inversion H3.
    dependent destruction H2.
    apply IHa_wf_wl in H2... destruct H2 as [Tᵈ].
    exists Tᵈ. apply binds_cons...
  - simpl in H1. inversion H1. 
    + dependent destruction H5.
      dependent destruction H4.
      exists (dbind_typ T)...
    + dependent destruction H4.
      apply IHa_wf_wl in H4... destruct H4 as [Tᵈ].
      exists Tᵈ. apply binds_cons...
  - simpl in H1. dependent destruction H2.
    apply IHa_wf_wl in H2...
Qed.
    


Lemma a_wf_typ_trans_typ : forall θ Γ Ω Aᵃ,
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> exists Aᵈ,
    trans_typ θ Aᵃ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros. dependent induction H...
  - exists (` X). econstructor... admit.
  - exists (` X). eapply trans_typ__stvar... admit. 
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted. 


Lemma a_wf_wl_d_wf_wl : forall θ Γ Ω,  
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> ⊢ᵈʷ Ω.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H...
  - admit.
  - econstructor... admit.
  - econstructor... admit.
  - econstructor... admit. 
    admit.
Admitted.


(* Lemma inst_subst : forall θ θ' X T Aᵃ Aᵈ, 
  lc_typ Aᵃ ->
  θ' ++ (X, dbind_typ T) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> 
  (* X cannot appear in θ', so we don't need to do any subst for it *)
  θ' ++ θ ⫦ᵗ {T /ᵗ X} Aᵃ ⇝ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros * Hlc Hinst.
  generalize dependent θ'. generalize dependent Aᵈ.
  dependent induction Hlc; simpl in *; intros; try solve 
    [dependent destruction Hinst; eauto with Hdb_transfer; dependent destruction H; eauto with Hdb_transfer].
  - dependent destruction Hinst.
    admit.
  - dependent destruction Hinst.
    admit.
  - dependent destruction Hinst.
    admit.
  - destruct (X0 == X); subst.
    + dependent destruction Hinst. 
      * admit.
      * admit.
      * admit.
    + dependent destruction Hinst.
      * econstructor. admit. admit.
      * eapply trans_typ__stvar. admit. admit.
      * econstructor.
        admit.
        admit.
  - dependent destruction Hinst.
    eapply trans_typ__all with (L:=L `union` singleton X). intros.
    inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    rewrite_env (((X0, dbind_tvar_empty) :: θ') ++ θ).
    eapply H0...
Admitted.
 *)

Lemma wf_subst_set_strength_etvar_same_denv: forall θ θ' X T,
  ss_to_denv (θ' ++ θ) = ss_to_denv (θ' ++ (X, dbind_typ T) :: θ).
Proof.
  intros. induction θ'.
  - auto.
  - destruct a. destruct d; auto; simpl; now rewrite IHθ'.
Qed.


Lemma wf_subst_set_strength_etvar: forall θ θ' T X,
  wf_ss (θ' ++ θ) ->
  d_mono_typ (ss_to_denv θ) T ->
  X `notin` dom (θ' ++ θ) ->
  wf_ss (θ' ++ (X, dbind_typ T) :: θ).
Proof with auto with Hdb_transfer.
  intros. induction θ'.
  - simpl in *. constructor...
  - destruct a. destruct d; simpl in *.
    + dependent destruction H. econstructor...
    + dependent destruction H. econstructor...
    + dependent destruction H. econstructor...
      rewrite <- wf_subst_set_strength_etvar_same_denv...
Qed.



Hint Resolve wf_subst_set_strength_etvar : Hdb_transfer.


Lemma trans_typ_rename : forall θ1 θ2 Aᵃ Aᵈ X X', 
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  map (subst_tvar_in_dbind (` X') X) θ2  ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵗ {` X' /ᵗ X} Aᵃ ⇝ {` X' /ᵗ X} Aᵈ.
Proof with auto with Hdb_transfer.
  intros. dependent induction H; simpl; auto...
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + econstructor... admit.
    + econstructor... admit. admit.
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + econstructor... admit.
    + admit.
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + admit.
    + admit.
  - econstructor... admit.
  - econstructor... admit.
  - econstructor... admit.
  - eapply trans_typ__all with (L := L `union` singleton X).
    intros. inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    rewrite typ_subst_open_comm...
    rewrite_env (map (subst_tvar_in_dbind ` X' X) ((X0, ▫) :: θ2) ++ (X', ▫) :: θ1).
    eapply H0...
Admitted.

Corollary trans_typ_rename_cons : forall θ Aᵃ Aᵈ X X', 
  (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  (X', dbind_tvar_empty) :: θ ⫦ᵗ {` X' /ᵗ X} Aᵃ ⇝ {` X' /ᵗ X} Aᵈ.
Proof.
  intros. 
  rewrite_env (map (subst_tvar_in_dbind (` X') X) nil  ++ (X', dbind_tvar_empty) :: θ).
  eapply trans_typ_rename. auto.
Qed.


Lemma in_ss_denv_in_ss : forall X b θ,
  binds X b (ss_to_denv θ) ->
  binds X b θ.
Proof with auto with Hdb_transfer.
  intros. induction θ...
  - destruct a. destruct d...
    + inversion H... 
      dependent destruction H0...
    + inversion H... 
      dependent destruction H0...
Qed.


Lemma wf_ss_etvar_tvar : forall θ1 θ2 T X,
  wf_ss (θ2 ++ (X, dbind_typ T) :: θ1) ->
  wf_ss (θ2 ++ (X, ▫) :: θ1).
Proof with auto with Hdb_transfer.
  intros. induction θ2; simpl in *.
  - dependent destruction H...
  - destruct a. destruct d.
    dependent destruction H...
    dependent destruction H...
    dependent destruction H...
    econstructor...
    rewrite <- wf_subst_set_strength_etvar_same_denv in H1.
  
    admit.
Admitted.

Hint Resolve wf_ss_etvar_tvar : Hdb_transfer.


Lemma trans_typ_weaken : forall θ1 θ2 θ3 Aᵃ Aᵈ,
  θ3 ++ θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros. generalize dependent θ2.
  dependent induction H; intros...
  - inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X.
    rewrite_env (((X, ▫) :: θ3) ++ θ2 ++ θ1).
    eapply H0; simpl...
Qed.


Lemma trans_typ_refl: forall θ A,
  ss_to_denv θ ⊢ A ->
  wf_ss θ ->
  θ ⫦ᵗ A ⇝ A.
Proof with eauto with Hdb_transfer.
  intros. dependent induction H...
  - econstructor... admit.
  - eapply trans_typ__stvar... admit.
  - econstructor. admit.
Admitted.


Lemma wf_ss_typ_no_etvar: forall θ X A T,
  wf_ss θ ->
  ss_to_denv θ ⊢ A ->
  binds X (dbind_typ T) θ ->
  X \notin ftvar_in_typ A.
Proof with eauto with Hdb_transfer.
  intros. dependent induction H0...
  + destruct (X == X0)...
    subst. apply in_ss_denv_in_ss in H0.
    exfalso. eapply wf_ss_etvar_tvar_false...
  + destruct (X == X0)...
    subst. apply in_ss_denv_in_ss in H0.
    exfalso. eapply wf_ss_etvar_stvar_false...
  + inst_cofinites_by (L `union` dom θ `union` singleton X) using_name X.
    simpl.
    rewrite ftvar_in_typ_open_typ_wrt_typ_lower.
    eapply H1 with (θ:=(X0 ~ dbind_tvar_empty ++ θ))...
    econstructor...
Qed.

Corollary etvar_bind_no_etvar: forall θ X Y A B,
  wf_ss θ ->
  binds X (dbind_typ A) θ ->
  binds Y (dbind_typ B) θ ->
  X \notin ftvar_in_typ B.
Proof with eauto with Hdb_transfer.
  intros; eapply wf_ss_typ_no_etvar...
Admitted.


Hint Resolve trans_typ_wf_ss : Hdb_transfer.



Lemma trans_typ_etvar_tvar_subst : forall θ1 θ2 T X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X `notin` dom (θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) T ->
  θ2 ++ (X, dbind_typ T) :: θ1 ⫦ᵗ Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {T /ᵗ X} Aᵈ = A'ᵈ /\ θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto with Hdb_transfer.
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
        econstructor... admit.
      * exists ` X... intuition... admit.
      * exists A1. split.
        -- rewrite subst_tvar_in_typ_fresh_eq...
           eapply etvar_bind_no_etvar...
        -- econstructor...
           admit.
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
    + eapply trans_typ__all with (L:=L); intros.
      intuition.
      erewrite subst_tvar_in_typ_intro by auto.
      erewrite (subst_tvar_in_typ_intro X0 (close_typ_wrt_typ X0 Aᵈ)) by apply close_typ_notin.
      apply trans_typ_rename_cons...
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
Admitted.


Lemma trans_typ_etvar_tvar_subst_cons : forall θ1 T X Aᵃ A'ᵈ,
  lc_typ Aᵃ -> 
  X `notin` dom θ1 ->
  d_mono_typ (ss_to_denv θ1) T ->
  (X, dbind_typ T) :: θ1 ⫦ᵗ Aᵃ ⇝ A'ᵈ -> 
  exists Aᵈ, {T /ᵗ X} Aᵈ = A'ᵈ /\ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with auto with Hdb_transfer. 
  intros. 
  rewrite_env (nil ++ (X, ▫) :: θ1).  
  apply trans_typ_etvar_tvar_subst...
Qed.


(* Hint Constructors trans_typ : transfer.
Hint Constructors trans_worklist : transfer.

Lemma fv_ss_ld_ctx_dom: forall θ x,
  x `notin` fv_ss θ -> x `notin` ld_ctx_dom (ss_to_ctx θ).
Proof.
  induction θ; simpl; intros; auto.
  - destruct a; destruct s.
    + simpl in *. auto.
    + auto.
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

Ltac inversion_eq :=
  repeat
    match goal with 
        | H : ?a = ?b |-  _ => dependent destruction H
      end.


(* Lemma transfer_reorder: forall Γᵃ Γ'ᵈ θ' x t m Γ'ᵃ,
  reorder Γᵃ x t m la_wl_nil Γ'ᵃ ->
  trans_worklist nil Γ'ᵃ Γ'ᵈ θ' ->
  exists Γᵈ θ, trans_worklist nil Γᵃ Γᵈ θ.
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
  trans_worklist nil Γᵃ Γᵈ θ -> 
  exists Γ'ᵈ θ', trans_worklist nil Γ'ᵃ Γ'ᵈ θ'.
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
Admitted. 
*)*)

Definition transfer (Γ : aworklist) (Ω : dworklist)  : Prop :=
  exists θ', trans_worklist nil Γ Ω θ'.
