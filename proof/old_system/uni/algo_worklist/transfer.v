Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
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


Inductive ss_wf_typ : subst_set -> typ -> Prop :=
  | ss_wf_typ__unit : forall (θ:subst_set),
    ss_wf_typ θ typ_unit
  | ss_wf_typ__bot : forall (θ:subst_set),
    ss_wf_typ θ typ_bot
  | ss_wf_typ__top : forall (θ:subst_set),
    ss_wf_typ θ typ_top
  | ss_wf_typ__tvar : forall (θ:subst_set) (X:typvar),
    binds ( X )  ( dbind_tvar_empty ) ( θ )  ->
    ss_wf_typ θ (typ_var_f X)
  | ss_wf_typ__stvar : forall (θ:subst_set) (X:typvar),
    binds ( X )  ( dbind_stvar_empty ) ( θ )  ->
    ss_wf_typ θ (typ_var_f X)
  | ss_wf_typ__etvar : forall (θ:subst_set) (X:typvar) (T:typ),
    binds ( X )  ( dbind_typ T ) ( θ )  ->
    ss_wf_typ θ (typ_var_f X)
  | ss_wf_typ__arrow : forall (θ:subst_set) (A1 A2:typ),
    ss_wf_typ θ A1 ->
    ss_wf_typ θ A2 ->
    ss_wf_typ θ (typ_arrow A1 A2)
  | ss_wf_typ__all : forall (L:vars) (θ:subst_set) (A:typ),
    ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
    ( forall X , X \notin  L  -> ss_wf_typ  ( X ~ dbind_tvar_empty  ++  θ )   ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
    ss_wf_typ θ (typ_all A)
  | ss_wf_typ__union : forall (θ:subst_set) (A1 A2:typ),
    ss_wf_typ θ A1 ->
    ss_wf_typ θ A2 ->
    ss_wf_typ θ (typ_union A1 A2)
  | ss_wf_typ__intersection : forall (θ:subst_set) (A1 A2:typ),
    ss_wf_typ θ A1 ->
    ss_wf_typ θ A2 ->
    ss_wf_typ θ (typ_intersection A1 A2).


Inductive trans_typ : subst_set -> typ -> typ -> Prop := 
  | trans_typ__tvar : forall θ X, 
      wf_ss θ -> 
      X ~ □ ∈ θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__stvar : forall θ X, 
      wf_ss θ -> 
      X ~ ■ ∈ θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__etvar : forall θ X A1,
      wf_ss θ ->
      X ~ A1 ∈ θ ->
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
        trans_body ((X, dbind_tvar_empty) :: θ) 
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
with trans_body : subst_set -> body -> body -> Prop :=
  | trans_body__anno : forall θ eᵃ eᵈ A1ᵃ A1ᵈ,
      trans_exp θ eᵃ eᵈ ->
      trans_typ θ A1ᵃ A1ᵈ ->
      trans_body θ (body_anno eᵃ A1ᵃ) (body_anno eᵈ A1ᵈ)
.

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
    trans_contd θ (contd_unioninfabs Aᵃ Bᵃ cdᵃ) (contd_unioninfabs Aᵈ Bᵈ cdᵈ)    
.


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

Notation "θ ⫦ᵗ Aᵃ ⇝ Aᵈ" := (trans_typ θ Aᵃ Aᵈ)
  (at level 65, Aᵃ at next level, no associativity).

Notation "θ ⫦ᵉ eᵃ ⇝ eᵈ" := (trans_exp θ eᵃ eᵈ)
  (at level 65, eᵃ at next level, no associativity).

Notation "θ ⫦ᵇ bᵃ ⇝ bᵈ" := (trans_body θ bᵃ bᵈ)
  (at level 65, bᵃ at next level, no associativity).

Notation "θ ⫦ᶜˢ csᵃ ⇝ csᵈ" := (trans_conts θ csᵃ csᵈ)
  (at level 65, csᵃ at next level, no associativity).

Notation "θ ⫦ᶜᵈ cdᵃ ⇝ cdᵈ" := (trans_contd θ cdᵃ cdᵈ)
  (at level 65, cdᵃ at next level, no associativity).

Notation "θ ⫦ʷ wᵃ ⇝ wᵈ" := (trans_work θ wᵃ wᵈ)
  (at level 65, wᵃ at next level, no associativity).


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
      X `notin` dom θ' -> 
      θ ⫦ aworklist_constvar Γ X abind_tvar_empty ⇝ dworklist_constvar Ω X dbind_tvar_empty ⫣  (X, dbind_tvar_empty) :: θ'
  | inst_wl__cons_stvar : forall θ θ' Γ Ω X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      X `notin` dom θ' -> 
      θ ⫦ aworklist_constvar Γ X abind_stvar_empty ⇝ dworklist_constvar Ω X dbind_stvar_empty ⫣  (X, dbind_stvar_empty) :: θ'
  | inst_wl__cons_var : forall θ θ' Γ Ω A1ᵃ A1ᵈ x, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' ->
      trans_typ θ' A1ᵃ A1ᵈ ->
      θ ⫦ aworklist_consvar Γ x (abind_var_typ A1ᵃ) ⇝ dworklist_consvar Ω x (dbind_typ A1ᵈ) ⫣ θ'
  | inst_wl_ev : forall θ θ' Γ Ω T X, 
      θ ⫦ Γ ⇝ Ω ⫣ θ' -> 
      X `notin` dom θ' -> 
      d_mono_typ (ss_to_denv θ' ) T ->
      θ ⫦ aworklist_constvar Γ X abind_etvar_empty ⇝ Ω ⫣  (X, dbind_typ T) :: θ'
where "θ ⫦ Γᵃ ⇝ Γᵈ ⫣ θ'" := (trans_worklist θ Γᵃ Γᵈ θ').


#[export] Hint Constructors trans_typ trans_exp trans_conts trans_contd trans_work trans_worklist wf_ss : core.


Lemma wf_ss_uniq : forall θ,
  wf_ss θ -> uniq θ.
Proof.
  intros. induction H; auto.
Qed.


Lemma wf_ss_etvar_tvar_false : forall θ X A,
  wf_ss θ -> X ~ A ∈ θ -> X ~ □ ∈ θ -> False.
Proof.
  intros. apply wf_ss_uniq in H.
  specialize (binds_unique _ _ _ _ _ H0 H1 H).
  intros. inversion H2.
Qed.

Lemma wf_ss_etvar_stvar_false : forall θ X A,
  wf_ss θ -> X ~ A ∈ θ -> X ~ ■ ∈ θ -> False.
Proof.
  intros. apply wf_ss_uniq in H.
  specialize (binds_unique _ _ _ _ _ H0 H1 H).
  intros. inversion H2.
Qed.

Lemma wf_ss_tvar_stvar_false : forall θ X,
  wf_ss θ -> X ~ □ ∈ θ -> X ~ ■ ∈ θ -> False.
Proof.
  intros. apply wf_ss_uniq in H.
  specialize (binds_unique _ _ _ _ _ H0 H1 H).
  intros. inversion H2.
Qed.

#[local] Hint Resolve wf_ss_uniq : core.

Lemma trans_typ_neq_all : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> neq_all Aᵃ -> neq_all Aᵈ.
Proof.
  intros. dependent destruction H0; dependent destruction H; auto.
  + admit.
  + constructor... admit. admit.
Admitted.


Lemma trans_typ_neq_all_rev : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> neq_all Aᵈ -> neq_all Aᵃ.
Proof.
  intros. dependent destruction H0; dependent destruction H; auto.
  + admit.
  + constructor... admit. admit.
Admitted.


Lemma trans_typ_neq_union : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> neq_union Aᵃ -> neq_union Aᵈ.
Proof.
  intros. dependent destruction H0; dependent destruction H; auto.
  + admit.
  + constructor... admit. admit.
Admitted.


Lemma trans_typ_neq_union_rev : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> neq_union Aᵈ -> neq_union Aᵃ.
Proof.
  intros. dependent destruction H0; dependent destruction H; auto.
  + admit.
  + constructor... admit.
Admitted.

Lemma trans_typ_neq_intersection : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> neq_intersection Aᵃ -> neq_intersection Aᵈ.
Proof.
  intros. dependent destruction H0; dependent destruction H; auto.
  + admit.
  + constructor... admit. admit.
Admitted.


Lemma trans_typ_neq_intersection_rev : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ -> neq_intersection Aᵈ -> neq_intersection Aᵃ.
Proof.
  intros. dependent destruction H0; dependent destruction H; auto.
  + admit.
  + constructor... admit.
Admitted.


Lemma trans_wl_not_in_ss : forall θ Γ Ω X,
  nil ⫦ Γ ⇝ Ω ⫣ θ -> X ∉ dom (awl_to_aenv Γ) -> X ∉ dom θ.
Proof with auto.
  intros. dependent induction H; simpl in *...
Qed.


Lemma trans_wl_wf_ss : forall θ θ' Γ Ω,  
  θ ⫦ Γ ⇝ Ω ⫣ θ' -> wf_ss θ'.
Proof with eauto.
  intros. dependent induction H; auto.
Qed.


Hint Resolve trans_wl_wf_ss : Hdb_transfer.


Lemma trans_typ_wf_ss : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss θ.
Proof with auto.
  intros. induction H...
  - inst_cofinites_by L.
    dependent destruction H0...
Qed.


(* does not hold because of inFV condition is not enforced in trans_typ *)
Lemma trans_typ_wf_dtyp : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  (ss_to_denv θ) ⊢ Aᵈ.
Proof with auto.
Abort.


Lemma trans_typ_lc_atyp : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  lc_typ Aᵃ.
Proof with auto.
  intros. induction H...
Qed.

Lemma wf_ss_binds_typ_lc : forall θ X T,
  wf_ss θ ->
  binds X (dbind_typ T) θ ->
  lc_typ T.
Proof with auto.
  intros. induction H.
  - inversion H0.
  - inversion H0; subst...
    inversion H2.
  - inversion H0; subst...
    inversion H2.
  - inversion H0; subst...
     dependent destruction H3.
     eapply d_mono_typ_lc; eauto.
Qed.

Lemma trans_typ_lc_dtyp : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  lc_typ Aᵈ.
Proof with auto.
  intros. induction H...
  eapply wf_ss_binds_typ_lc; eauto.
Qed.


Lemma trans_exp_lc_aexp : forall θ eᵃ eᵈ,
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  lc_exp eᵃ
with trans_body_lc_abody : forall θ bᵃ bᵈ,  
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  lc_body bᵃ.
Proof.
  - intros. induction H; auto. 
    + inst_cofinites_by L using_name X.   
      apply lc_exp_tabs_exists with (X1:=X).
      eapply trans_body_lc_abody; eauto.
    + constructor; auto.
      eapply trans_typ_lc_atyp; eauto.
    + constructor; auto.
      eapply trans_typ_lc_atyp; eauto.
  - intros. destruct bᵃ.
    + dependent destruction H. constructor; auto.
      eapply trans_exp_lc_aexp; eauto.
      eapply trans_typ_lc_atyp; eauto.
Qed.

Lemma trans_typ_det : forall θ Aᵃ A₁ᵈ A₂ᵈ,
  uniq θ -> 
  θ ⫦ᵗ Aᵃ ⇝ A₁ᵈ -> 
  θ ⫦ᵗ Aᵃ ⇝ A₂ᵈ -> 
  A₁ᵈ = A₂ᵈ.
Proof with eauto.
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

Ltac unify_trans_typ :=
  match goal with
  | H_1 : trans_typ ?θ ?Aᵃ ?A1ᵈ, H_2 : trans_typ ?θ ?Aᵃ ?A2ᵈ |- _ => eapply trans_typ_det with (A₁ᵈ:=A1ᵈ) in H_2; 
      eauto with Hdb_transfer; subst
  end.

Lemma trans_exp_det : forall θ eᵃ e₁ᵈ e₂ᵈ,
  uniq θ -> 
  θ ⫦ᵉ eᵃ ⇝ e₁ᵈ -> 
  θ ⫦ᵉ eᵃ ⇝ e₂ᵈ -> 
  e₁ᵈ = e₂ᵈ
with trans_body_det : forall θ bᵃ b₁ᵈ b₂ᵈ,
  uniq θ -> 
  θ ⫦ᵇ bᵃ ⇝ b₁ᵈ -> 
  θ ⫦ᵇ bᵃ ⇝ b₂ᵈ -> 
  b₁ᵈ = b₂ᵈ.
Proof with eauto.
  - intros. generalize dependent e₂ᵈ.
    induction H0; (intros e₂ᵈ H2; dependent destruction H2; auto).
    + inst_cofinites_by (L `union` L0 `union` (fvar_in_exp eᵈ) `union` (fvar_in_exp eᵈ0) `union`  dom θ) using_name x.
      apply f_equal.
      eapply open_exp_wrt_exp_inj with (x1:=x); auto.  
    + specialize (IHtrans_exp1 H _ H2_).
      specialize (IHtrans_exp2 H _ H2_0).
      subst...
    + inst_cofinites_by (L `union` L0 `union` (ftvar_in_body bᵈ) `union` (ftvar_in_body bᵈ0) `union`  dom θ) using_name X.
      apply f_equal.
      eapply open_body_wrt_typ_inj with (X1:=X); auto.
      eapply trans_body_det with (θ:=(X, □) :: θ)...
    + specialize (IHtrans_exp H _ H2).
      eapply trans_typ_det with (A₂ᵈ:=A1ᵈ0) in H1; auto.
      subst...
    + specialize (IHtrans_exp H _ H2).
      eapply trans_typ_det with (A₂ᵈ:=A1ᵈ0) in H1; auto.
      subst...
  - intros. generalize dependent b₂ᵈ.
    induction H0; intros.
    dependent destruction H2.
    apply trans_exp_det with (e₂ᵈ:=eᵈ0) in H0; auto.
    eapply trans_typ_det with (A₂ᵈ:=A1ᵈ0) in H1; auto.
    subst. auto.
Qed.


Ltac unify_trans_exp :=
  match goal with
  | H_1 : trans_exp ?θ ?eᵃ ?e1ᵈ, H_2 : trans_exp ?θ ?eᵃ ?e2ᵈ |- _ => eapply trans_exp_det in H_1; 
      eauto; subst
  end.

Lemma trans_conts_det : forall θ csᵃ cs₁ᵈ cs₂ᵈ,
  uniq θ -> 
  θ ⫦ᶜˢ csᵃ ⇝ cs₁ᵈ -> 
  θ ⫦ᶜˢ csᵃ ⇝ cs₂ᵈ -> 
  cs₁ᵈ = cs₂ᵈ
with trans_contd_det : forall θ cdᵃ cd₁ᵈ cd₂ᵈ,
  uniq θ -> 
  θ ⫦ᶜᵈ cdᵃ ⇝ cd₁ᵈ -> 
  θ ⫦ᶜᵈ cdᵃ ⇝ cd₂ᵈ -> 
  cd₁ᵈ = cd₂ᵈ.
Proof with eauto.
  - intros. generalize dependent cs₂ᵈ.
    induction H0; (intros cs₂ᵈ Htrans2; dependent destruction Htrans2).
    + apply trans_contd_det with (cd₂ᵈ:= cdᵈ0) in H0; auto; subst; auto.
    + apply trans_typ_det with (A₂ᵈ:=Aᵈ0) in H0; auto; subst.
      pose proof (IHtrans_conts H _ Htrans2) as IHtrans_conts; subst; auto.
    + apply trans_typ_det with (A₂ᵈ:=A1ᵈ0) in H0; auto; subst.
      apply trans_typ_det with (A₂ᵈ:=A2ᵈ0) in H1; auto; subst.
      pose proof (IHtrans_conts H _ Htrans2) as IHtrans_conts; subst; auto.
    + apply trans_typ_det with (A₂ᵈ:=Aᵈ0) in H0; auto; subst.
      pose proof (IHtrans_conts H _ Htrans2) as IHtrans_conts; subst; auto.
    + apply trans_typ_det with (A₂ᵈ:=Aᵈ0) in H0; auto; subst. auto.
  - intros. generalize dependent cd₂ᵈ.
    induction H0; (intros cd₂ᵈ Htrans2; dependent destruction Htrans2).
    + apply trans_exp_det with (e₂ᵈ:=eᵈ0) in H0; auto; subst.
      apply trans_conts_det with (cs₂ᵈ:= csᵈ0) in H1; subst; auto.
    + apply trans_typ_det with (A₂ᵈ:=Aᵈ0) in H0; auto; subst.
      pose proof (IHtrans_contd H _ Htrans2) as IHtrans_contd; subst; auto.
    + apply trans_typ_det with (A₂ᵈ:=Aᵈ0) in H0; auto; subst.
      apply trans_typ_det with (A₂ᵈ:=Bᵈ0) in H1; auto; subst.
      pose proof (IHtrans_contd H _ Htrans2) as IHtrans_contd; subst; auto.
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
  θ ⫦ Γ ⇝ Ω ⫣ θ' ->
  exists θ'', θ' = θ'' ++ θ.
Proof.  
  intros. induction H; eauto.
  - exists nil; auto.
  - destruct IHtrans_worklist as [θ''].
    exists ((X, □) :: θ''). rewrite H1. auto.
  - destruct IHtrans_worklist as [θ''].
    exists ((X, ■) :: θ''). rewrite H1. auto.
  - destruct IHtrans_worklist as [θ''].
    exists ((X, dbind_typ T):: θ''). rewrite H2. auto.
Qed.

Lemma trans_wl_split : forall Γ1 Γ2 Ω θ θ',
  θ ⫦ (Γ2 ⧺ Γ1) ⇝ Ω ⫣ θ' ->
  exists Ω1 Ω2 θ''
    , Ω = dwl_app Ω2 Ω1 
    ∧ θ  ⫦ Γ1 ⇝ Ω1 ⫣ θ''
    ∧ θ'' ⫦ Γ2 ⇝ Ω2 ⫣ θ'.
Proof.
  induction Γ2; simpl; intros.
  - exists Ω. exists dworklist_empty. exists θ'.
    simpl; repeat split; auto.
    econstructor. eapply trans_wl_wf_ss; eauto.
  - inversion H; subst.
    pose proof (IHΓ2 _ _ _ H6) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
    exists Ω1, (x ~ᵈ A1ᵈ;ᵈ Ω2)%dworklist, Θ0. repeat split; eauto.
    rewrite E. auto.
  - destruct ab; inversion H; subst.
    + pose proof (IHΓ2 _ _ _ H3) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, (X ~ᵈ □ ;ᵈ Ω2)%dworklist, Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2 _ _ _ H3) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, (X ~ᵈ ■ ;ᵈ Ω2)%dworklist, Θ0.
      subst. repeat split; eauto.
    + pose proof (IHΓ2 _ _ _ H2) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
      exists Ω1, Ω2, Θ0.
      subst. repeat split; eauto. 
  - inversion H; subst.
    pose proof (IHΓ2 _ _ _ H3) as (Ω1 & Ω2 & Θ0 & E & Inst1 & Inst2).
    exists Ω1, (wᵈ ⫤ Ω2)%dworklist, Θ0.
    subst. repeat split; eauto.
Qed.



Hint Resolve trans_wl_wf_ss : Hdb_a_wl_red_soundness.

Lemma trans_wl_app : forall Γ1 Γ2 Ω1 Ω2 θ1 θ2 θ3,
  θ1 ⫦ Γ1 ⇝ Ω1 ⫣ θ2 ->
  θ2 ⫦ Γ2 ⇝ Ω2 ⫣ θ3 -> 
  θ1 ⫦ Γ2 ⧺ Γ1 ⇝ Ω2 ⧺ Ω1 ⫣ θ3.
Proof.
  intros.
  induction H0; simpl; try solve [eauto].
Qed.


Lemma trans_wl_a_wl_binds_etvar_ss : forall Γ X Ω θ θ',
  θ ⫦ Γ ⇝ Ω ⫣ θ' ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  exists T, X ~ T ∈ θ'.
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
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_tvar_empty (awl_to_aenv Γ) ->
  X ~ □ ∈ θ.
Proof with eauto.
  intros. dependent induction H...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H2. inversion H3; subst...
    eauto...
Qed.

Lemma trans_wl_a_wl_binds_tvar_d_wl : forall Γ X Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_tvar_empty (awl_to_aenv Γ) ->
  binds X dbind_tvar_empty (dwl_to_denv Ω).
Proof with eauto.
  intros. dependent induction H; simpl in *...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H2. inversion H3; subst...
    eauto...
Qed.

Lemma trans_wl_ss_binds_etvar_a_wl : forall θ Γ Ω X T,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  X ~ T ∈ θ ->
  binds X abind_etvar_empty (awl_to_aenv Γ).
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
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_stvar_empty (awl_to_aenv Γ) ->
  X ~ ■ ∈ θ.
Proof with eauto.
  intros. dependent induction H...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H2. inversion H3; subst...
    eauto...
Qed.

Lemma trans_wl_a_wl_binds_stvar_d_wl : forall Γ X Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_stvar_empty (awl_to_aenv Γ) ->
  binds X dbind_stvar_empty (dwl_to_denv Ω).
Proof with eauto.
  intros. dependent induction H; simpl in *...
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H2. dependent destruction H3...
    eauto...
Qed.

Lemma trans_wl_d_wl_binds_tvar_ss : forall Γ X Ω θ θ',
  θ ⫦ Γ ⇝ Ω ⫣ θ' ->
  binds X dbind_tvar_empty (dwl_to_denv Ω) ->
  binds X dbind_tvar_empty (ss_to_denv θ').
Proof with eauto.
  intros. dependent induction H; simpl in *...
  - inversion H0.
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H1. dependent destruction H2...
    eauto...
Qed.


Lemma trans_wl_d_wl_binds_stvar_ss : forall Γ X Ω θ θ',
  θ ⫦ Γ ⇝ Ω ⫣ θ' ->
  binds X dbind_stvar_empty (dwl_to_denv Ω) ->
  binds X dbind_stvar_empty (ss_to_denv θ').
Proof with eauto.
  intros. dependent induction H; simpl in *...
  - inversion H0.
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H1. dependent destruction H2...
    eauto...
  - inversion H1. dependent destruction H2...
    eauto...
Qed.


Lemma trans_wl_a_wl_binds_etvar_d_wl : forall Γ X Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  exists T, binds X (dbind_typ T) (dwl_to_denv Ω).
Proof with eauto.
Admitted.

Lemma trans_wl_d_wl_mono_ss : forall θ θ' Γ Ω T,
  θ ⫦ Γ ⇝ Ω ⫣ θ' ->
  d_mono_typ (dwl_to_denv Ω) T -> 
  d_mono_typ (ss_to_denv θ') T.
Proof.
  intros. dependent induction H0; eauto.
  - constructor. eapply trans_wl_d_wl_binds_tvar_ss; eauto.
Qed.

Lemma wf_ss_rename_tvar : forall θ1 θ2 X X',
  wf_ss (θ2 ++ (X, □) :: θ1) ->
  X' ∉ dom (θ2 ++ θ1) ->
  wf_ss (map (subst_tvar_in_dbind ` X' X) θ2 ++ (X', □) :: θ1).
Proof with eauto.
  intros. induction θ2; simpl in *...
  - inversion H; subst...
  - dependent destruction a.
    inversion H; subst...
    econstructor...
    + replace (ss_to_denv (map (subst_tvar_in_dbind ` X' X) θ2 ++ (X', □) :: θ1))
      with ((map (subst_tvar_in_dbind ` X' X) (ss_to_denv θ2) ++ (X', □) :: (ss_to_denv θ1)))
      by admit.
      simpl. apply d_mono_typ_rename_tvar.
      admit.
Admitted.


Lemma trans_typ_s_in : forall θ X Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds X dbind_tvar_empty θ ->
  s_in X Aᵃ ->
  s_in X Aᵈ.
Proof.
  intros. induction H; try dependent destruction H1.
  - constructor.
  - exfalso. eapply wf_ss_tvar_stvar_false; eauto.
  - exfalso. eapply wf_ss_etvar_tvar_false; eauto.
  - econstructor; eauto.
    eapply trans_typ_lc_dtyp; eauto.
  - eapply s_in__arrow2; auto. 
    eapply trans_typ_lc_dtyp; eauto.
  - eapply s_in__all with (L:=L `union` L0).
    intros. inst_cofinites_with Y.
    apply H2... apply binds_cons; auto.
    auto.
  - econstructor; auto.
  - econstructor; auto.
Qed.

Lemma trans_typ_rename_tvar : forall θ1 θ2 Aᵃ Aᵈ X X', 
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  X' `notin` dom (θ2 ++ θ1) ->
  map (subst_tvar_in_dbind (` X') X) θ2  ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵗ {` X' /ᵗ X} Aᵃ ⇝ {` X' /ᵗ X} Aᵈ.
Proof with auto.
  intros. dependent induction H; simpl; auto...
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + econstructor...
      eapply wf_ss_rename_tvar; eauto.
    + econstructor...
      eapply wf_ss_rename_tvar; eauto.
      admit.
  - destruct_eq_atom. 
    + econstructor... 
      eapply wf_ss_rename_tvar; eauto.
    + econstructor... 
      eapply wf_ss_rename_tvar; eauto.
      admit.
  - destruct_eq_atom. 
    + admit. (* OK, false *)
    + econstructor... 
      eapply wf_ss_rename_tvar; eauto. admit. 
  - econstructor...
    eapply wf_ss_rename_tvar; eauto.  
  - econstructor...
    eapply wf_ss_rename_tvar; eauto.
  - econstructor... 
    eapply wf_ss_rename_tvar; eauto.
  - eapply trans_typ__all with (L := L `union` singleton X).
    intros. inst_cofinites_with X0.
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
    rewrite_env (map (subst_tvar_in_dbind ` X' X) ((X0, □) :: θ2) ++ (X', □) :: θ1).
    eapply H0...
Admitted.


Corollary trans_typ_rename_tvar_cons : forall θ Aᵃ Aᵈ X X', 
  (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  X' `notin` dom θ ->
  (X', dbind_tvar_empty) :: θ ⫦ᵗ {` X' /ᵗ X} Aᵃ ⇝ {` X' /ᵗ X} Aᵈ.
Proof.
  intros. 
  rewrite_env (map (subst_tvar_in_dbind (` X') X) nil  ++ (X', dbind_tvar_empty) :: θ).
  eapply trans_typ_rename_tvar; auto.
Qed.



Lemma trans_typ_tvar_stvar_same : forall θ1 θ2 X Aᵃ Aᵈ b b',
  b = dbind_tvar_empty \/ b = dbind_stvar_empty ->
  b' = dbind_tvar_empty \/ b' = dbind_stvar_empty ->
  θ2 ++ (X, b) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ2 ++ (X, b') :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with auto.
  intros. dependent induction H1; auto...
  - admit.
  - admit.
  - admit.
  - constructor.
    admit.
  - constructor.
    admit.
  - constructor.
    admit.
  - destruct H; destruct H0; subst; econstructor; eauto.
  - eapply trans_typ__all with (L:=L).
    intros. inst_cofinites_with X0.
    rewrite_env (((X0, □) :: θ2) ++ (X, b') :: θ1).
    destruct b; destruct b'; eauto...
  - destruct H; destruct H0; subst; econstructor; eauto.
  - destruct H; destruct H0; subst; econstructor; eauto.
Admitted.

Corollary trans_typ_tvar_stvar_cons : forall θ X Aᵃ Aᵈ,
  (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  (X, dbind_stvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof.
  intros. rewrite_env (nil ++ (X, dbind_stvar_empty) :: θ).
  eapply trans_typ_tvar_stvar_same with (b:=dbind_tvar_empty); eauto.
Qed.


Corollary trans_typ_stvar_tvar_cons : forall θ X Aᵃ Aᵈ,
  (X, dbind_stvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof.
  intros. rewrite_env (nil ++ (X, dbind_tvar_empty) :: θ).
  eapply trans_typ_tvar_stvar_same with (b:=dbind_stvar_empty); eauto.
Qed.


#[local] Hint Resolve trans_wl_wf_ss : core.

Lemma trans_typ_total : forall θ Γ Ω Aᵃ,
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->  
  ⊢ᵃʷ Γ -> 
  nil ⫦ Γ ⇝ Ω ⫣ θ -> 
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
  - apply IHa_wf_typ1 in H2 as Htrans_typ1...
    apply IHa_wf_typ2 in H2 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_arrow A1ᵈ A2ᵈ). econstructor...  
  - inst_cofinites_by (L `union` dom (awl_to_aenv Γ)  `union` ftvar_in_typ A `union` dom θ) using_name X.
    assert (⊢ᵃʷ aworklist_constvar Γ X abind_tvar_empty)... 
    eapply H1 with (Ω:=dworklist_constvar Ω X dbind_tvar_empty) (θ:=(X, dbind_tvar_empty)::θ) in H4...
    destruct H4 as [Axᵈ].
    exists (typ_all (close_typ_wrt_typ X Axᵈ)).
    eapply trans_typ__all with (L:=L `union` dom θ). intros.
    erewrite subst_tvar_in_typ_intro by auto.
    erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X Axᵈ)) by apply close_typ_wrt_typ_notin.
    apply trans_typ_rename_tvar_cons...
    rewrite open_typ_wrt_typ_close_typ_wrt_typ...
  - apply IHa_wf_typ1 in H2 as Htrans_typ1...
    apply IHa_wf_typ2 in H2 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_union A1ᵈ A2ᵈ). econstructor...  
  - apply IHa_wf_typ1 in H2 as Htrans_typ1...
    apply IHa_wf_typ2 in H2 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_intersection A1ᵈ A2ᵈ). econstructor...  
Qed.


Lemma trans_exp_rename_var : forall θ eᵃ eᵈ x x', 
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ ⫦ᵉ {(exp_var_f x') /ᵉₑ x} eᵃ ⇝ {(exp_var_f x') /ᵉₑ x} eᵈ
with trans_body_rename_var : forall θ bᵃ bᵈ x x', 
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ ⫦ᵇ {(exp_var_f x') /ᵇₑ x} bᵃ ⇝ {(exp_var_f x') /ᵇₑ x} bᵈ.
Proof with auto.
  - intros. dependent induction H; simpl; auto...
    + unfold eq_dec. destruct (EqDec_eq_of_X x0 x); subst.
      * econstructor... 
      * econstructor... 
    + eapply trans_exp__abs with (L:=L `union` singleton x). intros.
      inst_cofinites_with x0.
      erewrite subst_var_in_exp_open_exp_wrt_exp in H0...
      erewrite subst_var_in_exp_open_exp_wrt_exp in H0...
      simpl in H0...
      unfold eq_dec in H0. destruct (EqDec_eq_of_X x0 x).
      * subst. apply notin_union_2 in H1. apply notin_singleton_1 in H1. contradiction.
      * auto.
    + eapply trans_exp__tabs with (L:=L). intros.
      inst_cofinites_with X.
      erewrite <- subst_var_in_body_open_body_wrt_typ...
      erewrite <- subst_var_in_body_open_body_wrt_typ...
  - intros. dependent induction H; simpl; auto...
    + econstructor; auto.
Qed.


Lemma trans_exp_rename_tvar : forall θ1 θ2 eᵃ eᵈ X X', 
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵉ eᵃ ⇝ eᵈ ->
  X' `notin` dom (θ2 ++ θ1) ->
  map (subst_tvar_in_dbind (` X') X) θ2  ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵉ 
      subst_tvar_in_exp `X' X eᵃ ⇝ subst_tvar_in_exp `X' X eᵈ
with trans_body_rename_tvar :  forall θ1 θ2 bᵃ bᵈ X X', 
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵇ bᵃ ⇝ bᵈ ->
  X' `notin` dom (θ2 ++ θ1) ->
  map (subst_tvar_in_dbind (` X') X) θ2  ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵇ 
      subst_tvar_in_body `X' X bᵃ ⇝ subst_tvar_in_body `X' X bᵈ.
Proof with auto.
  - intros. dependent induction H; simpl in *...
    + constructor...
      eapply wf_ss_rename_tvar; eauto.
    + constructor.
      eapply wf_ss_rename_tvar; eauto.
    + inst_cofinites_for trans_exp__abs.
      intros. inst_cofinites_with x.
      eapply H0 in H1; eauto.
      rewrite subst_tvar_in_exp_open_exp_wrt_exp in H1...
      rewrite subst_tvar_in_exp_open_exp_wrt_exp in H1...
    + inst_cofinites_for trans_exp__tabs.
      intros. inst_cofinites_with X0.
      rewrite_env (((X0, □) :: θ2) ++ (X, □) :: θ1 ) in H.
      apply trans_body_rename_tvar with (X':=X') in H...
      rewrite subst_tvar_in_body_open_body_wrt_typ in H...
      rewrite subst_tvar_in_body_open_body_wrt_typ in H...
      simpl in H. destruct_eq_atom.
      auto.
    + constructor...
      apply trans_typ_rename_tvar...
    + constructor...
      apply trans_typ_rename_tvar...
  - intros. destruct bᵃ. dependent destruction H.
    simpl. constructor...
    apply trans_typ_rename_tvar...
Qed.


Lemma trans_exp_rename_tvar_cons : forall θ eᵃ eᵈ X X', 
  (X, dbind_tvar_empty) :: θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  X' `notin` dom θ ->
  (X', dbind_tvar_empty) :: θ ⫦ᵉ subst_tvar_in_exp `X' X eᵃ ⇝ subst_tvar_in_exp `X' X eᵈ
with trans_body_rename_tvar_cons :  forall θ bᵃ bᵈ X X', 
  (X, dbind_tvar_empty) :: θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  X' `notin` dom θ ->
  (X', dbind_tvar_empty) :: θ ⫦ᵇ subst_tvar_in_body `X' X bᵃ ⇝ subst_tvar_in_body `X' X bᵈ.
Proof.
  intros. rewrite_env (map (subst_tvar_in_dbind (` X') X) nil ++ (X', □) :: θ). 
    apply trans_exp_rename_tvar; auto.
  intros. rewrite_env (map (subst_tvar_in_dbind (` X') X) nil ++ (X', □) :: θ). 
    apply trans_body_rename_tvar; auto.
Qed.


Lemma trans_exp_total : forall θ Γ Ω eᵃ,
  a_wf_exp (awl_to_aenv Γ) eᵃ ->  
  ⊢ᵃʷ Γ -> 
  nil ⫦ Γ ⇝ Ω ⫣ θ -> 
  exists eᵈ, trans_exp θ eᵃ eᵈ
with trans_body_total : forall θ Γ Ω bᵃ,
  a_wf_body (awl_to_aenv Γ) bᵃ ->  
  ⊢ᵃʷ Γ -> 
  nil ⫦ Γ ⇝ Ω ⫣ θ -> 
  exists bᵈ, trans_body θ bᵃ bᵈ.
Proof with eauto.
  - intros. 
    generalize dependent Ω. 
    generalize dependent θ. 
    dependent induction H; intros.
    + exists exp_unit...
    + exists (exp_var_f x)... 
    + inst_cofinites_by (L `union` (fvar_in_exp e) `union` dom (awl_to_aenv Γ)).
      assert (⊢ᵃʷ aworklist_consvar Γ x (abind_var_typ T)) by auto.
      eapply trans_typ_total in H...
      destruct H as [Tᵈ].
      eapply H1 with (θ:=θ) in H4...
      destruct H4 as [eᵈ].
      exists (exp_abs (close_exp_wrt_exp x eᵈ)). 
      eapply trans_exp__abs with (L:=L `union` fvar_in_exp e `union` fvar_in_exp eᵈ). intros.
      erewrite (subst_var_in_exp_intro x)...
      erewrite (subst_var_in_exp_intro x ((close_exp_wrt_exp x eᵈ) )) by apply close_exp_wrt_exp_notin.
      apply trans_exp_rename_var...
      rewrite open_exp_wrt_exp_close_exp_wrt_exp...
    + apply IHa_wf_exp1 in H2 as Htrans_e1; auto.
      apply IHa_wf_exp2 in H2 as Htrans_e2; auto.
      destruct Htrans_e1 as [e1ᵈ].
      destruct Htrans_e2 as [e2ᵈ].  
      exists (exp_app e1ᵈ e2ᵈ)...
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_body body5 `union` dom θ) using_name X.
      assert (⊢ᵃʷ aworklist_constvar Γ X abind_tvar_empty) by auto.
      eapply trans_body_total with (Ω:=dworklist_constvar Ω X dbind_tvar_empty) (θ:=(X, dbind_tvar_empty)::θ) in H2...
      destruct H2 as [bᵈ].
      exists (exp_tabs (close_body_wrt_typ X bᵈ)).
      eapply trans_exp__tabs with (L:=L `union` dom θ). intros.
      erewrite (subst_tvar_in_body_intro X)...
      erewrite (subst_tvar_in_body_intro X (close_body_wrt_typ X bᵈ)) by apply close_body_wrt_typ_notin_rec.
      rewrite open_body_wrt_typ_close_body_wrt_typ.
      apply trans_body_rename_tvar_cons with (X':=X0) in H2; auto.
    + apply IHa_wf_exp in H2 as Htrans_e; auto.
      eapply trans_typ_total with (θ:=θ) (Ω:=Ω) in H as Htrans_A; auto.  
      destruct Htrans_e as [eᵈ].
      destruct Htrans_A as [Aᵈ].
      exists (exp_tapp eᵈ Aᵈ)...
    + apply IHa_wf_exp in H2 as Htrans_e; auto.
      eapply trans_typ_total with (θ:=θ) (Ω:=Ω) in H as Htrans_A; auto.  
      destruct Htrans_e as [eᵈ].
      destruct Htrans_A as [Aᵈ].
      exists (exp_anno eᵈ Aᵈ)...
  - intros. 
    generalize dependent Ω. 
    generalize dependent θ. 
    dependent induction H; intros.
    + eapply trans_exp_total in H0...
      eapply trans_typ_total in H...
      destruct H0 as [eᵈ].
      destruct H as [Aᵈ].
      exists (body_anno eᵈ Aᵈ)...
      econstructor...
Qed.


Fixpoint denv_no_var (Ψ : denv) :=
  match Ψ with 
  | nil => nil
  | (X , dbind_stvar_empty) :: Ψ' =>  X ~ dbind_stvar_empty ++ denv_no_var Ψ'
  | (X , dbind_tvar_empty) :: Ψ' =>  X ~ dbind_tvar_empty ++ denv_no_var Ψ'
  | (X , dbind_typ _) :: Ψ' =>  denv_no_var Ψ'
  end.

Fixpoint ss_no_etvar (Ψ : denv) :=
  match Ψ with 
  | nil => nil
  | (X , dbind_stvar_empty) :: Ψ' =>  X ~ dbind_stvar_empty ++ ss_no_etvar Ψ'
  | (X , dbind_tvar_empty) :: Ψ' =>  X ~ dbind_tvar_empty ++ ss_no_etvar Ψ'
  | (X , dbind_typ _) :: Ψ' =>  ss_no_etvar Ψ'
  end.
  

Lemma trans_wl_strengthen_etvar : forall Γ Ω X T θ θ',
  X `notin` ftvar_in_aworklist' Γ ->
  (X, dbind_typ T) :: θ ⫦ Γ ⇝ Ω ⫣ (θ' ++ (X, dbind_typ T) :: θ) ->
  θ ⫦ Γ ⇝ Ω ⫣ (θ' ++ θ).
Proof.
  intros. dependent induction H0.
  - dependent destruction H0. 
    assert (θ'=nil) by admit. subst.
    constructor; auto.
  - simpl in H.
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    eapply IHtrans_worklist in H2; eauto.
    econstructor. auto. admit.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'.
    + simpl in x. inversion x. 
    + simpl in x. inversion x. subst.  
      eapply IHtrans_worklist in H2; eauto.
      simpl. 
      constructor; auto.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'.
    + simpl in x. inversion x. 
    + simpl in x. inversion x. subst.  
      eapply IHtrans_worklist in H2; eauto.
      simpl. 
      constructor; auto.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    eapply IHtrans_worklist in H2; eauto.
    constructor; auto.
    admit.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'.
    + simpl in x. inversion x. subst. solve_notin_eq X. 
    + simpl in x. inversion x. subst.
      eapply IHtrans_worklist in H3; eauto.
      simpl. constructor; auto.
      admit.
Admitted.


Lemma trans_wl_weaken_etvar : forall Γ Ω X T θ1 θ2 θ',
  X `notin` ftvar_in_aworklist' Γ `union` dom θ1 `union` dom θ2 ->
  (θ2 ++ θ1) ⫦ Γ ⇝ Ω ⫣ (θ' ++ θ2 ++ θ1) ->
  d_mono_typ (ss_to_denv θ1) T ->
  θ2 ++ (X, dbind_typ T) :: θ1 ⫦ Γ ⇝ Ω ⫣ (θ' ++ θ2 ++ (X, dbind_typ T) :: θ1).
Proof.
Admitted.


Lemma trans_wl_weaken_etvar_cons : forall Γ Ω X T θ θ',
  X `notin` ftvar_in_aworklist' Γ `union` dom θ->
  θ ⫦ Γ ⇝ Ω ⫣ (θ' ++ θ) ->
  d_mono_typ (ss_to_denv θ) T ->
  (X, dbind_typ T) :: θ ⫦ Γ ⇝ Ω ⫣ (θ' ++ (X, dbind_typ T) :: θ).
Proof.
  intros. rewrite_env (nil ++ (X, dbind_typ T) :: θ).
  eapply trans_wl_weaken_etvar; eauto.
Qed.


Lemma trans_wl_strengthen_etvar_gen : forall Γ Ω X T θ1 θ2 θ'1 θ'2,
  X `notin` ftvar_in_aworklist' Γ ->
  θ2 ++ (X, dbind_typ T) :: θ1 ⫦ Γ ⇝ Ω ⫣ (θ'2 ++ (X, dbind_typ T) :: θ'1) ->
  (θ2 ++ θ1) ⫦ Γ ⇝ Ω ⫣ (θ'2 ++ θ'1).
Proof.
  intros. dependent induction H0.
  - assert (θ2=θ'2) by admit. 
    assert (θ1=θ'1) by admit.
    subst.
    constructor; auto. admit. 
  - simpl in H.
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    eapply IHtrans_worklist in H2; eauto.
    econstructor. auto. admit.
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
    admit.
  - simpl in H. 
    assert (X ∉ (ftvar_in_aworklist' Γ)) by auto.
    destruct θ'2.
    + simpl in x. inversion x. subst. solve_notin_eq X. 
    + simpl in x. inversion x. subst.
      eapply IHtrans_worklist in H3; eauto.
      simpl. constructor; auto.
      admit.
Admitted.


(* not used now *)
Lemma tran_wl_dwl_ss_same_tvar_stvar : forall Γ Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  ss_no_etvar θ = denv_no_var (dwl_to_denv Ω).
Proof with auto. 
  intros. dependent induction H...
  - simpl... rewrite IHtrans_worklist...
  - simpl... rewrite IHtrans_worklist...
Qed.


Lemma trans_wl_wf_bind_typ : forall Γ Ω θ X T,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X (dbind_typ T) θ ->
  dwl_to_denv Ω ⊢ T.
Proof.
  intros. dependent induction H...
  - inversion H0.
  - simpl. auto.
  - inversion H1...
    dependent destruction H2.
    simpl. apply d_wf_typ_weaken_cons. auto.
  - inversion H1...
    dependent destruction H2.
    simpl. apply d_wf_typ_weaken_cons. auto.
  - simpl. apply d_wf_typ_weaken_cons. auto.
  - simpl. inversion H2.
    dependent destruction H3.
    admit.
    (* eapply d_sub_dwft; eauto. *)
    auto.
Admitted.



Lemma trans_typ_binds_etvar : forall θ X T,
  wf_ss θ ->
  binds X (dbind_typ T) θ ->
  θ ⫦ᵗ ` X ⇝ T.
Proof.
  intros.
  constructor; auto.
Qed.


Lemma trans_typ_tvar_stvar_in_atyp_in_dtyp' : forall θ X Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds X dbind_tvar_empty θ \/ binds X dbind_stvar_empty θ ->
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
    assert (X `in` ftvar_in_typ (A1ᵈ ^ᵗ X0)). {
      eapply H0; eauto.
      rewrite ftvar_in_typ_open_typ_wrt_typ_lower  with (A2:=` X0) in Hfv.
      auto. inversion Hbinds; auto.
    }
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H2.
    apply union_iff in H2. inversion H2; simpl; eauto.
    + apply singleton_iff in H3. subst. solve_notin_eq X. 
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
Qed.


Lemma trans_typ_tvar_stvar_in_atyp_in_dtyp : forall θ X Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds X dbind_tvar_empty θ \/ binds X dbind_stvar_empty θ ->
  X `in` ftvar_in_typ Aᵃ -> 
  X `in` ftvar_in_typ Aᵈ.
Proof.
  intros * Htrans Hbinds Hfv. 
  apply trans_typ_lc_atyp in Htrans as Hlc.
  eapply trans_typ_tvar_stvar_in_atyp_in_dtyp'; eauto.
Qed.

Lemma trans_typ_tvar_stvar_in_etvar_binds_in_atyp' : forall θ X T Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds X (dbind_typ T) θ ->
  X `in` ftvar_in_typ Aᵃ ->
  (forall Y, Y `in` ftvar_in_typ T -> Y `in` ftvar_in_typ Aᵈ). 
Proof.
  intros * Hlc Htrans Hbinds Hfv. generalize dependent θ. generalize dependent Aᵈ.
  induction Hlc; simpl in *; intros; try fsetdec.
  - apply singleton_iff in Hfv.
    subst. apply trans_typ_binds_etvar in Hbinds; auto.
    apply trans_typ_det with (A₁ᵈ:=T) in Htrans; eauto; subst; auto.
    + apply wf_ss_uniq. eapply trans_typ_wf_ss; eauto.
    + eapply trans_typ_wf_ss; eauto.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans. 
    pick fresh X0. inst_cofinites_with X0.
    assert (Y `in` ftvar_in_typ (A1ᵈ ^ᵗ X0)). {
      rewrite ftvar_in_typ_open_typ_wrt_typ_lower  with (A2:=` X0) in Hfv.
      eapply H0 with (Y:=Y) in Hfv; eauto.
    }
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H3.
    apply union_iff in H3. inversion H3; simpl; eauto.
    apply singleton_iff in H4. subst. solve_notin_eq Y. 
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
  - dependent destruction Htrans. 
    apply union_iff in Hfv. inversion Hfv; simpl; eauto.
Qed.


Lemma trans_typ_tvar_stvar_in_etvar_binds_in_atyp : forall θ X T Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  binds X (dbind_typ T) θ ->
  X `in` ftvar_in_typ Aᵃ ->
  (forall Y, Y `in` ftvar_in_typ T -> Y `in` ftvar_in_typ Aᵈ). 
Proof.
  intros * Htrans Hbinds Hfv. 
  apply trans_typ_lc_atyp in Htrans as Hlc.
  eapply trans_typ_tvar_stvar_in_etvar_binds_in_atyp'; eauto.
Qed.


Lemma trans_wl_a_wf_typ_d_wf_typ' : forall Γ Ω θ Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->
  d_wf_typ (dwl_to_denv Ω) Aᵈ.
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
    + admit.
    + admit.
    + eapply trans_wl_wf_bind_typ...
  - dependent destruction H0...
    dependent destruction H1...
  - dependent destruction H2.
    dependent destruction H3.
    inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X...
    + eapply trans_typ_s_in... 
    + rewrite_env (dwl_to_denv (dworklist_constvar Ω X dbind_tvar_empty)).
      eapply H0 with (Γ:=(aworklist_constvar Γ X abind_tvar_empty))...
      econstructor...
  - dependent destruction H0...
    dependent destruction H1...
  - dependent destruction H0...
    dependent destruction H1...
Admitted.

Lemma trans_wl_a_wf_typ_d_wf_typ : forall Γ Ω θ Aᵃ Aᵈ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->
  d_wf_typ (dwl_to_denv Ω) Aᵈ.
Proof with eauto. 
  intros. apply trans_typ_lc_atyp in H0 as Hlc.
  eapply trans_wl_a_wf_typ_d_wf_typ'; eauto.
Qed.

Lemma trans_wl_d_wf_typ_ss_wf_typ : forall Γ Ω θ Aᵈ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  d_wf_typ (dwl_to_denv Ω) Aᵈ ->
  d_wf_typ (ss_to_denv θ) Aᵈ.
Proof with eauto. 
  intros. generalize dependent Γ; generalize dependent θ; dependent induction H0; intros...
  - eapply trans_wl_d_wl_binds_tvar_ss in H0; eauto.
  - eapply trans_wl_d_wl_binds_stvar_ss in H0; eauto.
  - inst_cofinites_for d_wf_typ__all; intros; inst_cofinites_with X...
    rewrite_env (ss_to_denv ((X, dbind_tvar_empty)::θ)).
    eapply H1 with (Γ:=aworklist_constvar Γ X abind_tvar_empty) (Ω:=dworklist_constvar Ω X dbind_tvar_empty); eauto.
Qed.


Lemma trans_wl_dom_upper_bound : forall θ Γ Ω,  
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  dom (dwl_to_denv Ω) [<=] dom (awl_to_aenv Γ).
Proof with auto.
  intros. dependent induction H; simpl...
  - fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
Qed.


Lemma a_wf_wl_d_wf_wl : forall θ Γ Ω,  
  ⊢ᵃʷ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> ⊢ᵈʷ Ω.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H...
  - econstructor...
    admit.
  - econstructor...
    rewrite trans_wl_dom_upper_bound...
  - econstructor... 
    rewrite trans_wl_dom_upper_bound...
  - econstructor... 
    rewrite trans_wl_dom_upper_bound... 
    eapply trans_wl_a_wf_typ_d_wf_typ with (Aᵃ:=A1ᵃ)...
Admitted.


Lemma a_wf_wl_d_wf_env : forall θ Γ Ω,  
  ⊢ᵃʷ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> ⊢ dwl_to_denv Ω.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H; simpl...
  - econstructor...
    rewrite trans_wl_dom_upper_bound...
  - econstructor...
    rewrite trans_wl_dom_upper_bound...
  - econstructor... 
    eapply trans_wl_a_wf_typ_d_wf_typ with (Aᵃ:=A1ᵃ)...
    rewrite trans_wl_dom_upper_bound...
Qed.



Lemma wf_ss_binds_monotyp : forall θ X T,
  wf_ss θ -> binds X (dbind_typ T) θ -> d_mono_typ (ss_to_denv θ) T.
Proof.
  intros. induction H; auto.
  - inversion H0.
  - inversion H0.
    + inversion H2.
    + simpl. rewrite_env ((X0 ~ □) ++ ss_to_denv θ).
      apply d_mono_typ_weaken_head. apply IHwf_ss; auto.
  - inversion H0.
    + inversion H2.
    + simpl. rewrite_env ((X0 ~ ■) ++ ss_to_denv θ).
      apply d_mono_typ_weaken_head. apply IHwf_ss; auto.
  - inversion H0.
    + dependent destruction H3. simpl. auto. 
    + simpl. apply IHwf_ss; auto.
Qed.

(* dependent destruction all non-atomic ⊢ᵃʷ relation *)


Lemma a_wf_work_apply_conts : forall Γ cs A w,
  a_wf_conts Γ cs ->
  a_wf_typ Γ A ->
  apply_conts cs A w ->
  a_wf_work Γ w.
Proof with eauto.
  intros. induction H1; try solve [destruct_a_wf_wl; constructor; eauto with Hdb_transfer].
Qed.



Lemma a_wf_work_apply_contd : forall Γ cd A B w,
  a_wf_contd Γ cd ->
  a_wf_typ Γ A ->
  a_wf_typ Γ B ->
  apply_contd cd A B w ->
  a_wf_work Γ w.
Proof with eauto.
  intros. induction H2; try solve [destruct_a_wf_wl; constructor; eauto with Hdb_transfer].
Qed.



Lemma wf_ss_etvar_same_denv: forall θ θ' X T,
  ss_to_denv (θ' ++ θ) = ss_to_denv (θ' ++ (X, dbind_typ T) :: θ).
Proof.
  intros. induction θ'.
  - auto.
  - destruct a. destruct d; auto; simpl; now rewrite IHθ'.
Qed.


Lemma wf_ss_weaken_tvar: forall θ1 θ2 X,
  wf_ss (θ2 ++ θ1) ->
  X `notin` dom (θ2 ++ θ1) ->
  wf_ss (θ2 ++ (X, dbind_tvar_empty) :: θ1).
Proof with auto.
  intros. induction θ2; simpl in *...
  - destruct a; destruct d; simpl in *...
    + dependent destruction H... 
    + dependent destruction H...
    + dependent destruction H... econstructor...
      admit.
Admitted.

Lemma wf_ss_weaken_stvar: forall θ1 θ2 X,
  wf_ss (θ2 ++ θ1) ->
  X `notin` dom (θ2 ++ θ1) ->
  wf_ss (θ2 ++ (X, dbind_stvar_empty) :: θ1).
Proof with auto.
  intros. induction θ2; simpl in *...
  - destruct a; destruct d; simpl in *...
    + dependent destruction H... 
    + dependent destruction H...
    + dependent destruction H... econstructor...
      admit.
Admitted.

Lemma wf_ss_weaken_etvar: forall θ θ' T X,
  wf_ss (θ' ++ θ) ->
  d_mono_typ (ss_to_denv θ) T ->
  X `notin` dom (θ' ++ θ) ->
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


Hint Resolve wf_ss_weaken_etvar : Hdb_transfer.


Lemma in_ss_denv_in_ss : forall X b θ,
  binds X b (ss_to_denv θ) ->
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
    admit.
Admitted.

Hint Resolve wf_ss_etvar_tvar : Hdb_transfer.


Lemma trans_typ_weaken : forall θ1 θ2 θ3 Aᵃ Aᵈ,
  θ3 ++ θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss (θ3 ++ θ2 ++ θ1) ->
  (θ3 ++ θ2 ++ θ1) ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros. generalize dependent θ2.
  dependent induction H; intros...
  - inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X.
    rewrite_env (((X, □) :: θ3) ++ θ2 ++ θ1).
    eapply H0; simpl...
Qed.

Lemma trans_typ_strengthen_etvar : forall θ1 θ2 X T Aᵃ Aᵈ,
  (θ2 ++ (X, dbind_typ T) :: θ1) ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  X \notin ftvar_in_typ Aᵃ ->
  θ2 ++ θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  dependent induction H; intros...
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
  - econstructor.
    eapply wf_ss_strengthen_etvar; eauto.
  - econstructor.
    eapply wf_ss_strengthen_etvar; eauto.
  - econstructor.
    eapply wf_ss_strengthen_etvar; eauto.
  - simpl in H1. econstructor.
    eapply IHtrans_typ1; eauto. 
    eapply IHtrans_typ2; eauto. 
  - eapply trans_typ__all with (L:=L `union` singleton X); eauto.
    intros. inst_cofinites_with X0.
    rewrite_env (((X0, □) :: θ2) ++ θ1).
    eapply H0 with (X:=X) (T:=T); eauto.
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
  - simpl in H1. econstructor.
    eapply IHtrans_typ1; eauto. 
    eapply IHtrans_typ2; eauto. 
  - simpl in H1. econstructor.
    eapply IHtrans_typ1; eauto. 
    eapply IHtrans_typ2; eauto. 
Qed.


Lemma trans_typ_strengthen : forall θ1 θ2 X b Aᵃ Aᵈ,
  (θ2 ++ (X, b) :: θ1) ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  X \notin ftvar_in_typ Aᵃ ->
  wf_ss (θ2 ++ θ1) ->
  θ2 ++ θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros.
  dependent induction H; intros...
  - econstructor...
    simpl in H1.
    apply binds_remove_mid in H0...
  - apply trans_typ__stvar...
    simpl in H1.
    apply binds_remove_mid in H0...
  - econstructor...
    simpl in H1.
    apply binds_remove_mid in H0...
  - simpl in H1. econstructor.
    eapply IHtrans_typ1; eauto. 
    eapply IHtrans_typ2; eauto. 
  - inst_cofinites_for trans_typ__all.
    intros. inst_cofinites_with X0.
    rewrite_env (((X0, □) :: θ2) ++ θ1).
    eapply H0 with (X:=X) (b:=b); simpl; eauto...
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
  - simpl in H1. econstructor.
    eapply IHtrans_typ1; eauto. 
    eapply IHtrans_typ2; eauto. 
  - simpl in H1. econstructor.
    eapply IHtrans_typ1; eauto. 
    eapply IHtrans_typ2; eauto.
Qed.


Lemma trans_typ_refl: forall θ A,
  ss_to_denv θ ⊢ A ->
  wf_ss θ ->
  θ ⫦ᵗ A ⇝ A.
Proof with eauto.
  intros. dependent induction H...
  - econstructor...
    apply in_ss_denv_in_ss...
  - eapply trans_typ__stvar...
    apply in_ss_denv_in_ss...
  - inst_cofinites_for trans_typ__all...
Qed.

Lemma wf_ss_typ_no_etvar: forall θ X A T,
  wf_ss θ ->
  ss_to_denv θ ⊢ A ->
  X ~ T ∈ θ ->
  X \notin ftvar_in_typ A.
Proof with eauto.
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

Corollary etvar_bind_no_etvar: forall θ X1 X2 A1 A2,
  wf_ss θ ->
  X1 ~ A1 ∈ θ ->
  X2 ~ A2 ∈ θ ->
  X1 \notin ftvar_in_typ A2.
Proof with eauto.
  intros; eapply wf_ss_typ_no_etvar...
Admitted.



Ltac destruct_binds_eq :=
  repeat
    lazymatch goal with
    | H1 : (?X1, ?b1) = (?X2, ?b2) |- _ =>
      dependent destruction H1
    end.

Ltac destruct_binds :=
  simpl in *;
  repeat
  match goal with
  | H1 : binds ?X ?b (?b' :: ?θ) |- _ =>
    inversion H1;
    clear H1;
    destruct_binds_eq
  end.


Lemma trans_wl_a_wl_binds_var_binds_d_wl_and_trans : forall θ Γ Ω x Aᵃ,
  ⊢ᵃʷ Γ ->
  ⊢ᵈʷ Ω ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds x (abind_var_typ Aᵃ) (awl_to_aenv Γ) ->
  exists Aᵈ, binds x (dbind_typ Aᵈ) (dwl_to_denv Ω) /\ θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto.
  intros. generalize dependent Ω. generalize dependent θ. 
    dependent induction H; intros; auto.
  - inversion H2.
  - dependent destruction H4.
    dependent destruction H3.
    destruct_binds; eauto.
    + eapply IHa_wf_wl in H8; eauto. destruct H8 as [Aᵈ [Hbinds Htrans]].
      exists Aᵈ. split; auto.
  - dependent destruction H3.
    inversion H1.
    destruct_binds.
    eapply IHa_wf_wl in H8; eauto. destruct H8 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto.
    rewrite_env (nil ++ (X ~ dbind_tvar_empty) ++ θ'). 
    apply trans_typ_weaken; simpl...
  - dependent destruction H3.
    inversion H1.
    destruct_binds.
    eapply IHa_wf_wl in H8; eauto. destruct H8 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto.
    rewrite_env (nil ++ (X ~ dbind_stvar_empty) ++ θ'). 
    apply trans_typ_weaken; simpl...
  - dependent destruction H3.
    destruct_binds.
    eapply IHa_wf_wl with (θ:=θ') in H6 ; eauto. destruct H6 as [Aᵈ [Hbinds Htrans]].
    exists Aᵈ. split; auto.
    rewrite_env (nil ++ (X ~ dbind_typ T) ++ θ'). 
    apply trans_typ_weaken; simpl...
  - dependent destruction H3. simpl in *.
    dependent destruction H1.
    eapply IHa_wf_wl; eauto.
Qed.



Hint Resolve trans_typ_wf_ss : Hdb_transfer.


Hint Resolve trans_typ_lc_atyp : Hdb_transfer.
Hint Resolve trans_typ_lc_dtyp : Hdb_transfer.


Lemma ftvar_in_trans_dtyp_upper : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  ftvar_in_typ Aᵈ [<=] dom θ.
Proof.
  intros. induction H; simpl; try fsetdec.
  - apply binds_In in H0. fsetdec.
  - apply binds_In in H0. fsetdec.
  - admit.
  - admit.
Admitted.
  

Lemma trans_typ_reorder : forall θ θ' Aᵃ Aᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_typ Aᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  θ' ⫦ᵗ Aᵃ ⇝ Aᵈ.
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
    inst_cofinites_for trans_typ__all. intros.
    inst_cofinites_with X.
    eapply H0 with (θ':=(X, dbind_tvar_empty) :: θ') in H2; auto...
    + intros. destruct (X0 == X).
      * subst. inversion H7.
        -- dependent destruction H8...
        -- apply binds_dom_contradiction in H8... contradiction.
      * rewrite ftvar_in_typ_open_typ_wrt_typ_upper in H6. 
        apply union_iff in H6. inversion H6.
        -- simpl in H8. apply singleton_iff in H8. subst. contradiction. 
        -- inversion H7. dependent destruction H9...
           ++ apply binds_cons...
  - dependent destruction H2...
    simpl in H1. econstructor...
  - dependent destruction H2...
    simpl in H1. econstructor...
Qed.



Lemma trans_exp_reorder' : forall θ θ' eᵃ eᵈ,
  lc_exp eᵃ ->
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_exp eᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ' ⫦ᵉ eᵃ ⇝ eᵈ
with trans_body_reorder' : forall θ θ' bᵃ bᵈ,
  lc_body bᵃ ->
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_body bᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ' ⫦ᵇ bᵃ ⇝ bᵈ.
Proof with eauto.
  - intros * Hlc. 
    generalize dependent θ'. generalize dependent θ. generalize dependent eᵈ.
    induction Hlc; clear trans_exp_reorder'; intros; try solve [dependent destruction H2; eauto with Hdb_transfer].
    + dependent destruction H4...
      inst_cofinites_for trans_exp__abs. intros. 
      inst_cofinites_with x.
      eapply H0 with (θ:=θ)... intros.
      apply H3...
      rewrite ftvar_in_exp_open_exp_wrt_exp_upper in H6. simpl in *. fsetdec.
    + simpl in *. dependent destruction H2...
      constructor...
    + dependent destruction H3.
      inst_cofinites_for trans_exp__tabs. intros. 
      inst_cofinites_with X.
      eapply trans_body_reorder' with (θ:=(X, dbind_tvar_empty) :: θ)...
      * intros. destruct (X0 == X). 
        -- subst. inversion H6. 
           ++ dependent destruction H7... 
           ++ apply binds_dom_contradiction in H7... contradiction.
        -- apply binds_cons... apply H2.
           rewrite ftvar_in_body_open_body_wrt_typ_upper in H5.
           apply union_iff in H5. inversion H5.
           ++ simpl in H7. apply singleton_iff in H7. subst. contradiction.
           ++ auto.
           ++ inversion H6.
              ** dependent destruction H7... contradiction.
              ** auto. 
    + simpl in *. dependent destruction H3...
      constructor... eapply trans_typ_reorder with (θ:=θ)...
    + simpl in *. dependent destruction H3...
      constructor... eapply trans_typ_reorder with (θ:=θ)...
  - intros.  
    dependent destruction H.
    dependent destruction H4; simpl in *...
    constructor...
    + eapply trans_typ_reorder with (θ:=θ)...
Qed.

Lemma trans_exp_reorder : forall θ θ' eᵃ eᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_exp eᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ' ⫦ᵉ eᵃ ⇝ eᵈ
with trans_body_reorder : forall θ θ' bᵃ bᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_body bᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ' ⫦ᵇ bᵃ ⇝ bᵈ.
Proof with eauto.
  - intros. apply trans_exp_lc_aexp in H2 as Hlc. eapply trans_exp_reorder' with (θ:=θ); eauto.
  - intros. apply trans_body_lc_abody in H2 as Hlc. eapply trans_body_reorder' with (θ:=θ); eauto.
Qed.

(* Lemma trans_exp_reorder : forall θ θ' eᵃ eᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_exp eᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ' ⫦ᵉ eᵃ ⇝ eᵈ
with trans_body_reorder : forall θ θ' bᵃ bᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_body bᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ' ⫦ᵇ bᵃ ⇝ bᵈ.
Proof with eauto.
  - intros. 
    apply trans_exp_lc_aexp in H2 as Hlc.
    generalize dependent θ'. generalize dependent θ. generalize dependent eᵈ.
    induction Hlc; clear trans_exp_reorder; intros; try solve [dependent destruction H2; eauto with Hdb_transfer].
    + dependent destruction H2...
      inst_cofinites_for trans_exp__abs. intros. 
      inst_cofinites_with x.
      eapply H0 with (θ:=θ)... intros.
      apply H4...
      rewrite ftvar_in_exp_open_exp_wrt_exp_upper in H6. simpl in *. fsetdec.
    + simpl in *. dependent destruction H2...
      constructor...
    + dependent destruction H2.
      inst_cofinites_for trans_exp__tabs. intros. 
      inst_cofinites_with X.
      eapply trans_body_reorder with (θ:=(X, dbind_tvar_empty) :: θ)...
      * intros. destruct (X0 == X). 
        -- subst. inversion H6. 
           ++ dependent destruction H7... 
           ++ apply binds_dom_contradiction in H7... contradiction.
        -- apply binds_cons... apply H3.
           rewrite ftvar_in_body_open_body_wrt_typ_upper in H5.
           apply union_iff in H5. inversion H5.
           ++ simpl in H7. apply singleton_iff in H7. subst. contradiction.
           ++ auto.
           ++ inversion H6.
              ** dependent destruction H7... contradiction.
              ** auto. 
    + simpl in *. dependent destruction H2...
      constructor... eapply trans_typ_reorder with (θ:=θ)...
    + simpl in *. dependent destruction H2...
      constructor... eapply trans_typ_reorder with (θ:=θ)...
  - intros.  
    apply trans_body_lc_abody in H2 as Hlc. dependent destruction Hlc; simpl in *.
    dependent destruction H2...
    constructor...
    + eapply trans_typ_reorder with (θ:=θ)...
Qed. *)


Lemma trans_conts_reorder : forall θ θ' csᵃ csᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_conts csᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᶜˢ csᵃ ⇝ csᵈ ->
  θ' ⫦ᶜˢ csᵃ ⇝ csᵈ
with trans_contd_reorder : forall θ θ' cdᵃ cdᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_contd cdᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ᶜᵈ cdᵃ ⇝ cdᵈ ->
  θ' ⫦ᶜᵈ cdᵃ ⇝ cdᵈ.
Proof with eauto.
  intros.
  generalize dependent θ'. generalize dependent θ. generalize dependent csᵈ.
  induction csᵃ; simpl in *; intros; dependent destruction H2; constructor; 
    try eapply trans_typ_reorder with (θ:=θ); eauto with Hdb_transfer; 
    try eapply trans_exp_reorder with (θ:=θ); eauto with Hdb_transfer; 
    try eapply IHcᵃ with (θ:=θ)...
  intros.
  generalize dependent θ'. generalize dependent θ. generalize dependent cdᵈ.
  induction cdᵃ; simpl in *; intros; dependent destruction H2; constructor; 
    try eapply trans_typ_reorder with (θ:=θ); eauto with Hdb_transfer; 
    try eapply trans_exp_reorder with (θ:=θ); eauto with Hdb_transfer; 
    try eapply IHdᵃ with (θ:=θ)...
Qed.


Lemma trans_work_reorder : forall θ θ' wᵃ wᵈ,
  wf_ss θ ->
  wf_ss θ' ->
  (forall X b, X `in` ftvar_in_work wᵃ -> binds X b θ -> binds X b θ') ->
  θ ⫦ʷ wᵃ ⇝ wᵈ ->
  θ' ⫦ʷ wᵃ ⇝ wᵈ.
Proof with eauto.
  intros. destruct wᵃ; simpl in *; dependent destruction H2; constructor;
    try eapply trans_typ_reorder with (θ:=θ); eauto with Hdb_transfer; 
    try eapply trans_exp_reorder with (θ:=θ); eauto with Hdb_transfer; 
    try eapply trans_conts_reorder with (θ:=θ); eauto with Hdb_transfer;
    try eapply trans_contd_reorder with (θ:=θ); eauto.
    intros. apply H1; auto.
    intros. apply H1; eauto.
Qed.


Definition transfer (Γ : aworklist) (Ω : dworklist)  : Prop :=
  exists θ', trans_worklist nil Γ Ω θ'.

    