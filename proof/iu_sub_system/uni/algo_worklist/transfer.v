Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import LibTactics.

Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
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
      X ~ ▫ ∈ θ ->
      trans_typ θ (typ_var_f X) (typ_var_f X)
  | trans_typ__stvar : forall θ X,
      wf_ss θ ->
      X ~ ▪ ∈ θ ->
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

Notation "θ ⫦ᵗ Aᵃ ⇝ Aᵈ" := (trans_typ θ Aᵃ Aᵈ)
  (at level 65, Aᵃ at next level, no associativity).

Notation "θ ⫦ᵉ eᵃ ⇝ eᵈ" := (trans_exp θ eᵃ eᵈ)
  (at level 65, eᵃ at next level, no associativity).

Notation "θ ⫦ᵇ bᵃ ⇝ bᵈ" := (trans_body θ bᵃ bᵈ)
  (at level 65, bᵃ at next level, no associativity).

Notation "θ ⫦ᶜ cᵃ ⇝ cᵈ" := (trans_cont θ cᵃ cᵈ)
  (at level 65, cᵃ at next level, no associativity).

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


Lemma trans_wl_not_in_ss : forall θ Γ Ω X,
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

Lemma wf_ss_tvar_stvar_false : forall θ X,
  wf_ss θ -> X ~ ▫ ∈ θ -> X ~ ▪ ∈ θ -> False.
Proof.
  intros. apply wf_ss_uniq in H.
  specialize (binds_unique _ _ _ _ _ H0 H1 H).
  intros. inversion H2.
Qed.

Corollary wf_ss_etvar_tvar_false_middle : forall θ1 θ2 X A,
    wf_ss (θ2 ++ (X, ▫) :: θ1) -> X ~ A ∈ (θ2 ++ (X, ▫) :: θ1) -> False.
Proof.
  intros. applys wf_ss_etvar_tvar_false H H0.
  applys binds_app_3. applys~ binds_cons_2.
Qed.

Corollary wf_ss_tvar_stvar_false_middle : forall θ1 θ2 X,
    wf_ss (θ2 ++ (X, ▫) :: θ1) -> X ~ ▪ ∈ (θ2 ++ (X, ▫) :: θ1) -> False.
Proof.
  intros. applys wf_ss_tvar_stvar_false H H0.
  applys binds_app_3. applys~ binds_cons_2.
Qed.

Lemma a_wf_wl_wf_ss : forall θ Γ Ω,
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> wf_ss θ.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H...
  - econstructor... eapply trans_wl_not_in_ss...
  - econstructor... eapply trans_wl_not_in_ss...
  - econstructor... eapply trans_wl_not_in_ss...
Qed.


Hint Resolve a_wf_wl_wf_ss : Hdb_transfer.


Lemma trans_typ_wf_ss : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  wf_ss θ.
Proof with auto with Hdb_transfer.
  intros. induction H...
  - inst_cofinites_by L.
    dependent destruction H0...
Qed.


(* does not hold because of inFV condition is not enforced in trans_typ *)
Lemma trans_typ_wf_typ : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  (ss_to_denv θ) ⊢ Aᵈ.
Proof with auto with Hdb_transfer.
Abort.


Lemma trans_typ_lc_atyp : forall θ Aᵃ Aᵈ,
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  lc_typ Aᵃ.
Proof with auto with Hdb_transfer.
  intros. induction H...
Qed.

Lemma wf_ss_binds_typ_lc : forall θ X T,
  wf_ss θ ->
  binds X (dbind_typ T) θ ->
  lc_typ T.
Proof with auto with Hdb_transfer.
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
Proof with auto with Hdb_transfer.
  intros. induction H...
  eapply wf_ss_binds_typ_lc; eauto.
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
Proof with eauto with Hdb_transfer.
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
      eapply trans_body_det with (θ:=(X, ▫) :: θ)...
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


Hint Constructors trans_typ : Hdb_transfer.
Hint Constructors trans_exp : Hdb_transfer.
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


Lemma trans_wl_in_ss_tvar : forall Γ X Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_tvar_empty (awl_to_aenv Γ) ->
  X ~ ▫ ∈ θ.
Proof with eauto with Hdb_transfer.
  intros. dependent induction H...
  - inversion H0. inversion H1; subst...
    eauto...
  - inversion H0. inversion H1; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H5. inversion H6; subst...
    eauto...
Qed.

Lemma trans_wl_in_ss_stvar : forall Γ X Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X abind_stvar_empty (awl_to_aenv Γ) ->
  X ~ ▪ ∈ θ.
Proof with eauto with Hdb_transfer.
  intros. dependent induction H...
  - inversion H0. inversion H1; subst...
    eauto...
  - inversion H0. inversion H1; subst...
    eauto...
  - inversion H1. inversion H2; subst...
    eauto...
  - inversion H5. inversion H6; subst...
    eauto...
Qed.


Lemma trans_wl_in_ss_etvar : forall Γ X Ω θ A B,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X (abind_bound A B) (awl_to_aenv Γ) ->
  exists T, X ~ T ∈ θ.
Proof with eauto with Hdb_transfer.
  intros. dependent induction H.
  - inversion H0.
  - auto...
  - inversion H0. inversion H1; subst...
    apply IHtrans_worklist in H1...
    destruct H1 as [T]. exists T...
  - inversion H0. inversion H1; subst...
    apply IHtrans_worklist in H1...
    destruct H1 as [T]. exists T...
  - inversion H1. inversion H2; subst...
    apply IHtrans_worklist in H2...
  - inversion H5. inversion H6; subst...
    apply IHtrans_worklist in H6...
    destruct H6 as [T']. exists T'...
Qed.


Lemma binds_flag_subst : forall  X flag Y T θ1 θ2 Y' A B T',
  binds X flag (θ2 ++ (Y, T) :: θ1) -> X <> Y -> subst_tvar_in_dbind A B flag = flag ->
  binds X flag (map (subst_tvar_in_dbind A B) θ2 ++ (Y', T') :: θ1).
Proof.
  intros * H HF Heq.
  forwards* [?|?]: binds_app_1 H.
  - forwards: binds_map_2 (subst_tvar_in_dbind A B) H0. rewrite Heq in H1.
    simpl in H1. applys~ binds_app_2.
  - apply binds_cons_iff in H0. iauto.
Qed.

Lemma binds_change_middle : forall  X U Y T (θ1 θ2 : denv) T',
    binds X U (θ2 ++ (Y, T) :: θ1) -> X <> Y ->
    binds X U (θ2 ++ (Y, T') :: θ1).
Proof.
  intros * H HF.
  forwards* [?|?]: binds_app_1 H. forwards* [?|?]: binds_cons_1 H0.
  - intuition auto.
Qed.

Lemma binds_change_middle_2 : forall  X U Y T (θ1 θ2 : denv) T',
    binds X U (θ2 ++ (Y, T) :: θ1) -> U <> T -> U <> T' ->
    binds X U (θ2 ++ (Y, T') :: θ1).
Proof.
  intros * H HF.
  forwards* [?|?]: binds_app_1 H. forwards* [?|?]: binds_cons_1 H0.
  - intuition auto.
Qed.

(*********************************** wf_ss ************************************)

Lemma binds_typ_subst_with_wf_ss_aux : forall  X U Y θ1 θ2 Y',
  wf_ss (θ2 ++ (Y, ▫) :: θ1) ->
  X ~ U ∈ (θ2 ++ (Y, ▫) :: θ1) -> Y ∉ ftvar_in_typ U ->
  X ~ ({` Y' /ᵗ Y} U) ∈ (map (subst_tvar_in_dbind ` Y' Y) θ2 ++ (Y', ▫) :: θ1).
Proof.
  intros. induction θ2; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + rewrite subst_tvar_in_typ_fresh_eq; auto.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      apply IHθ2; auto.
      inversion H; auto.
Qed.

Lemma ss_to_denv_app : forall θ θ',
    ss_to_denv (θ ++ θ') = ss_to_denv θ ++ ss_to_denv θ'.
Proof.
  intros *. induction* θ.
  simpl. destruct a; destruct d; rewrite IHθ.
  all: eauto.
Qed.

Lemma wf_ss_strenthening_head : forall a Ψ,
    wf_ss (a :: Ψ) -> wf_ss Ψ.
Proof with auto.
  intros * H. inverts* H.
Qed.

Corollary wf_ss_weaken_stvar : forall Ψ1 Ψ2 X,
  wf_ss (Ψ2 ++ Ψ1) ->
  X ∉ dom (Ψ2 ++ Ψ1) ->
  wf_ss (Ψ2 ++ X ~ ▪ ++ Ψ1).
Proof with eauto.
  intros * HE HT. induction Ψ2; intros.
  - econstructor...
  - rewrite_env (a :: (Ψ2 ++ X ~ ▪ ++ Ψ1)). destruct a. destruct d.
    1: rewrite_env ((a, ▫) :: (Ψ2 ++ Ψ1)) in HE.
    2: rewrite_env ((a, ▪) :: (Ψ2 ++ Ψ1)) in HE.
    3: rewrite_env ((a, dbind_typ A) :: (Ψ2 ++ Ψ1)) in HE.
    all: forwards HE': wf_ss_strenthening_head HE; inverts HE.
    all: econstructor; try solve_notin.
    rewrite ss_to_denv_app in *. applys* d_mono_typ_weaken H4.
Qed.

Lemma dom_change_middle : forall (θ1 θ2 : denv) X A B,
    dom (θ2 ++ X ~ A ++ θ1) = dom (θ2 ++ X ~ B ++ θ1).
Proof.
  intros. induction* θ2. simpl in *. rewrite* IHθ2.
Qed.

Lemma d_mono_typ_in_ss_to_denv_change_bind : forall Ψ1 Ψ2 Y T A,
    d_mono_typ (ss_to_denv (Ψ2 ++ (Y , T) :: Ψ1)) A  ->
    d_mono_typ (ss_to_denv (Ψ2 ++ (Y , ▫) :: Ψ1)) A.
Proof with try solve_notin; simpl in *; eauto.
  intros * HT.
  inductions HT...
  rewrite ss_to_denv_app in *; simpl in *.
  forwards* [?|?]: binds_app_1 H. destruct* T.
  inverts H0.
  - inverts H1.
  - econstructor. eauto.
Qed.

Lemma wf_ss_bind_to_tvar : forall θ1 θ2 X T,
    wf_ss (θ2 ++ (X, dbind_typ T) :: θ1) ->
    wf_ss (θ2 ++ (X, ▫) :: θ1).
Proof with eauto.
  intros * Hw. induction θ2; intros.
  - inverts* Hw. econstructor...
  - rewrite_env (a :: (θ2 ++ X ~ ▫ ++ θ1)). destruct a. destruct d.
    1: rewrite_env ((a, ▫) :: (θ2 ++ (X, dbind_typ T) :: θ1)) in Hw.
    2: rewrite_env ((a, ▪) :: (θ2 ++ (X, dbind_typ T) :: θ1)) in Hw.
    3: rewrite_env ((a, dbind_typ A) :: (θ2 ++ (X, dbind_typ T) :: θ1)) in Hw.
    all: forwards~: IHθ2; inverts~ Hw.
    all: replace (dom (θ2 ++ (X, dbind_typ T) :: θ1)) with (dom (θ2 ++ X ~ ▫ ++ θ1));
      try applys dom_change_middle.
    all: econstructor; try solve_notin.
    + applys* d_mono_typ_in_ss_to_denv_change_bind.
Qed.

Lemma ss_to_denv_map_subst_tvar_comm: forall A X Ψ,
    ss_to_denv (map (subst_tvar_in_dbind A X) Ψ) =
      map (subst_tvar_in_dbind A X) (ss_to_denv Ψ).
Proof.
  intros. induction* Ψ.
  destruct a. destruct* d.
  all: simpl; rewrite* IHΨ.
Qed.

Lemma d_mono_typ_in_ss_to_denv_rename_tvar : forall Ψ1 Ψ2 X Y A,
  d_mono_typ (ss_to_denv (Ψ2 ++ X ~ ▫ ++ Ψ1)) A  ->
  d_mono_typ (ss_to_denv (map (subst_tvar_in_dbind ` Y X ) Ψ2 ++ Y ~ ▫ ++ Ψ1)) ({ ` Y /ᵗ X } A).
Proof with try solve_notin; simpl in *; eauto.
  intros * HT.
  case_eq (X==Y); intros.
  1: { subst. rewrite* subst_same_tvar_map_id. rewrite subst_same_tvar_typ_id... }
  clear H.
  inductions HT... case_if; econstructor; rewrite ss_to_denv_app in *; simpl in *.
  - subst*.
  - rewrite ss_to_denv_map_subst_tvar_comm. applys* binds_flag_subst H.
Qed.

Lemma wf_ss_rename : forall θ1 θ2 X Y,
  wf_ss (θ2 ++ (X, ▫) :: θ1) ->
  Y ∉ dom (θ2 ++ θ1) ->
  wf_ss (map (subst_tvar_in_dbind ` Y X) θ2 ++ (Y, ▫) :: θ1).
Proof with try solve_notin; simpl; eauto.
  intros * HE HT.
  case_eq (Y == X); intros.
  1: { subst. rewrite* subst_same_tvar_map_id. } clear H.
  rewrite_env ((θ2 ++ X ~ ▫) ++ θ1) in HE.
  forwards HE': wf_ss_weaken_stvar Y HE. { solve_notin. }
  induction θ2; intros; simpl.
  - inverts~ HE. econstructor...
  - destruct a. destruct d...
    + rewrite_env (((a, ▫) :: (θ2 ++ X ~ ▫) ++ θ1)) in HE. inverts~ HE.
      rewrite_env ((a, ▫) :: (θ2 ++ X ~ ▫) ++ (Y, ▪) :: θ1) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, ▪) :: (θ2 ++ X ~ ▫) ++ θ1)) in HE. inverts~ HE.
      rewrite_env ((a, ▪) :: (θ2 ++ X ~ ▫) ++ (Y, ▪) :: θ1) in HE'. inverts~ HE'.
      econstructor...
    + rewrite_env (((a, dbind_typ A) :: (θ2 ++ X ~ ▫) ++ θ1)) in HE. inverts~ HE.
      rewrite_env ((a, dbind_typ A) :: (θ2 ++ X ~ ▫) ++ (Y, ▪) :: θ1) in HE'. inverts~ HE'.
      econstructor...
      forwards*: IHθ2. solve_notin.
      applys d_mono_typ_in_ss_to_denv_rename_tvar...
      rewrite_env ((θ2 ++ X ~ ▫) ++ θ1)...
Qed.


Lemma d_wf_typ_from_d_mono_typ_in_ss_to_denv : forall θ T,
    d_mono_typ (ss_to_denv θ) T ->
    θ ⊢ T.
Proof with eauto using d_mono_typ_d_wf_typ.
  intros * HD. induction* T; try solve_by_invert.
  2-4: inverts* HD.
  - induction θ; simpl in HD.
    + inverts* HD...
    + destruct a. destruct d.
      all: inverts HD.
      1-2: forwards* [?|?]: binds_cons_1 H1.
      all: forwards*: IHθ; applys~ d_wf_typ_weaken_cons.
Qed.

Lemma wf_ss_to_d_wf_env : forall θ,
    wf_ss θ -> d_wf_env θ.
Proof.
  intros. induction H. all: econstructor; eauto.
  applys~ d_wf_typ_from_d_mono_typ_in_ss_to_denv.
Qed.

Lemma binds_typ_subst_with_wf_ss : forall  X U Y θ1 θ2 Y',
  wf_ss (θ2 ++ (Y, ▫) :: θ1) ->
  X ~ U ∈ (θ2 ++ (Y, ▫) :: θ1) -> Y' ∉ dom (θ2 ++ θ1) ->
  X ~ ({` Y' /ᵗ Y} U) ∈ (map (subst_tvar_in_dbind ` Y' Y) θ2 ++ (Y', ▫) :: θ1).
Proof.
  intros. induction θ2; simpl in *; auto.
  - inversion H0.
    + inversion H2.
    + assert (θ1 ⊢ U).
      { eapply dwf_env_binds_d_wf_typ; eauto. inverts H. applys~ wf_ss_to_d_wf_env. }
      rewrite subst_tvar_in_typ_fresh_eq; auto.
      eapply d_new_tv_notin_wf_typ; eauto. applys~ wf_ss_to_d_wf_env.
  - destruct a. inversion H0.
    + inversion H2. auto.
    + apply binds_cons_3.
      apply IHθ2; auto.
      inversion H; auto.
Qed.

Lemma trans_typ_rename : forall θ1 θ2 Aᵃ Aᵈ X X',
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  X' `notin` dom (θ2 ++ θ1) ->
  map (subst_tvar_in_dbind (` X') X) θ2  ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵗ {` X' /ᵗ X} Aᵃ ⇝ {` X' /ᵗ X} Aᵈ.
Proof with auto with Hdb_transfer.
  intros. dependent induction H; simpl; auto...
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + econstructor... apply wf_ss_rename...
    + econstructor... apply wf_ss_rename... applys* binds_flag_subst.
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + econstructor... apply wf_ss_rename...
    + apply trans_typ__stvar. apply wf_ss_rename... applys* binds_flag_subst.
  - unfold eq_dec. destruct (EqDec_eq_of_X X0 X); subst.
    + exfalso. applys* wf_ss_etvar_tvar_false_middle.
    + econstructor. apply wf_ss_rename...
      applys* binds_typ_subst_with_wf_ss.
  - econstructor... apply wf_ss_rename...
  - econstructor... apply wf_ss_rename...
  - econstructor... apply wf_ss_rename...
  - eapply trans_typ__all with (L := L `union` singleton X `union` singleton X').
    intros. inst_cofinites_with X0.
    rewrite typ_subst_open_comm...
    rewrite typ_subst_open_comm...
    rewrite_env (map (subst_tvar_in_dbind ` X' X) ((X0, ▫) :: θ2) ++ (X', ▫) :: θ1).
    eapply H0...
Qed.


Corollary trans_typ_rename_cons : forall θ Aᵃ Aᵈ X X',
  (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  X' `notin` dom θ ->
  (X', dbind_tvar_empty) :: θ ⫦ᵗ {` X' /ᵗ X} Aᵃ ⇝ {` X' /ᵗ X} Aᵈ.
Proof.
  intros.
  rewrite_env (map (subst_tvar_in_dbind (` X') X) nil  ++ (X', dbind_tvar_empty) :: θ).
  eapply trans_typ_rename; auto.
Qed.


Lemma a_wf_typ_trans_typ : forall θ Γ Ω Aᵃ,
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->
  ⊢ᵃ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  exists Aᵈ, trans_typ θ Aᵃ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros.
  generalize dependent Ω.
  generalize dependent θ.
  dependent induction H; intros...
  - exists (` X). econstructor...
    eapply trans_wl_in_ss_tvar...
  - exists (` X). eapply trans_typ__stvar...
    eapply trans_wl_in_ss_stvar...
  - eapply trans_wl_in_ss_etvar in H...
    destruct H as [T].
    exists T...
  - apply IHa_wf_typ1 in H2 as Htrans_typ1...
    apply IHa_wf_typ2 in H2 as Htrans_typ2...
    destruct Htrans_typ1 as [A1ᵈ]. destruct Htrans_typ2 as [A2ᵈ].
    exists (typ_arrow A1ᵈ A2ᵈ). econstructor...
  - inst_cofinites_by (L `union` dom (awl_to_aenv Γ)  `union` ftvar_in_typ A) using_name X.
    assert (⊢ᵃ aworklist_constvar Γ X abind_tvar_empty)...
    eapply H1 with (Ω:=dworklist_constvar Ω X dbind_tvar_empty) (θ:=(X, dbind_tvar_empty)::θ) in H4...
    destruct H4 as [Axᵈ].
    exists (typ_all (close_typ_wrt_typ X Axᵈ)).
    eapply trans_typ__all with (L:=L `union` dom θ). intros.
    erewrite subst_tvar_in_typ_intro by auto.
    erewrite (subst_tvar_in_typ_intro X (close_typ_wrt_typ X Axᵈ)) by apply close_typ_notin.
    apply trans_typ_rename_cons...
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

(* Lemma ss_wf_typ_trans_typ  : forall θ Aᵃ,
  (ss_to_aenv θ) Aᵃ ->
  ⊢ᵃ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  exists Aᵈ, trans_typ θ Aᵃ Aᵈ. *)


Lemma trans_exp_rename_var : forall θ eᵃ eᵈ x x',
  θ ⫦ᵉ eᵃ ⇝ eᵈ ->
  θ ⫦ᵉ {(exp_var_f x') /ᵉ x} eᵃ ⇝ {(exp_var_f x') /ᵉ x} eᵈ
with trans_body_rename_var : forall θ bᵃ bᵈ x x',
  θ ⫦ᵇ bᵃ ⇝ bᵈ ->
  θ ⫦ᵇ {(exp_var_f x') /ᵇ x} bᵃ ⇝ {(exp_var_f x') /ᵇ x} bᵈ.
Proof with auto with Hdb_transfer.
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
  X' \notin dom (θ2 ++ θ1) ->
  map (subst_tvar_in_dbind (` X') X) θ2 ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵉ subst_tvar_in_exp (` X') X eᵃ ⇝ subst_tvar_in_exp (` X') X eᵈ
with trans_body_rename_tvar : forall θ1 θ2 bᵃ bᵈ X X',
  θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵇ bᵃ ⇝ bᵈ ->
  X' \notin dom (θ2 ++ θ1) ->
  map (subst_tvar_in_dbind (` X') X) θ2 ++ (X', dbind_tvar_empty) :: θ1 ⫦ᵇ subst_tvar_in_body (` X') X bᵃ ⇝ subst_tvar_in_body (` X') X bᵈ.
Proof with auto using wf_ss_rename with Hdb_transfer.
  - intros. dependent induction H; simpl; auto...
    + pick fresh Y and apply trans_exp__abs.
      rewrite 2 subst_tvar_in_exp_open_exp_wrt_exp_var. forwards*: H0 Y.
    + pick fresh Y and apply trans_exp__tabs.
      rewrite 2 subst_tvar_in_body_open_body_wrt_typ_var...
      replace ( (Y, ▫) :: map (subst_tvar_in_dbind ` X' X) θ2  ++ (X', ▫) :: θ1 )
        with ( map (subst_tvar_in_dbind ` X' X) ((Y, ▫) ::θ2) ++ (X', ▫) :: θ1 ).
      applys* trans_body_rename_tvar. solve_notin.
      auto.
    + econstructor.
      apply IHtrans_exp...
      apply trans_typ_rename...
    + econstructor.
      apply IHtrans_exp...
      apply trans_typ_rename...
  - intros. dependent induction H; simpl; auto...
    + econstructor.
      eapply trans_exp_rename_tvar...
      apply trans_typ_rename...
Qed.


Lemma a_wf_exp_trans_exp : forall θ Γ Ω eᵃ,
  a_wf_exp (awl_to_aenv Γ) eᵃ ->
  ⊢ᵃ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  exists eᵈ, trans_exp θ eᵃ eᵈ
with a_wf_body_trans_body : forall θ Γ Ω bᵃ,
  a_wf_body (awl_to_aenv Γ) bᵃ ->
  ⊢ᵃ Γ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  exists bᵈ, trans_body θ bᵃ bᵈ.
Proof with eauto with Hdb_transfer.
  - intros.
    generalize dependent Ω.
    generalize dependent θ.
    dependent induction H; intros.
    + exists exp_unit...
    + exists (exp_var_f x)...
    + inst_cofinites_by (L `union` (fvar_in_exp e) `union` dom (awl_to_aenv Γ)).
      assert (⊢ᵃ aworklist_consvar Γ x (abind_typ T)) by auto.
      eapply a_wf_typ_trans_typ in H...
      destruct H as [Tᵈ].
      eapply H1 with (θ:=θ) in H4...
      destruct H4 as [eᵈ].
      exists (exp_abs (close_exp_wrt_exp x eᵈ)).
      eapply trans_exp__abs with (L:=L `union` fvar_in_exp e `union` fvar_in_exp eᵈ). intros.
      erewrite (subst_var_in_exp_intro x)...
      erewrite (subst_var_in_exp_intro x ((close_exp_wrt_exp x eᵈ) )) by apply close_exp_notin.
      apply trans_exp_rename_var...
      rewrite open_exp_wrt_exp_close_exp_wrt_exp...
    + apply IHa_wf_exp1 in H2 as Htrans_e1; auto.
      apply IHa_wf_exp2 in H2 as Htrans_e2; auto.
      destruct Htrans_e1 as [e1ᵈ].
      destruct Htrans_e2 as [e2ᵈ].
      exists (exp_app e1ᵈ e2ᵈ)...
    + inst_cofinites_by (L `union` dom (awl_to_aenv Γ) `union` ftvar_in_body body5) using_name X.
      assert (⊢ᵃ aworklist_constvar Γ X abind_tvar_empty) by auto.
      eapply a_wf_body_trans_body with (Ω:=dworklist_constvar Ω X dbind_tvar_empty) (θ:=(X, dbind_tvar_empty)::θ) in H2...
      destruct H2 as [bᵈ].
      exists (exp_tabs (close_body_wrt_typ X bᵈ)).
      eapply trans_exp__tabs with (L:=L `union` dom θ). intros.
      erewrite (subst_tvar_in_body_intro X)...
      erewrite (subst_tvar_in_body_intro X (close_body_wrt_typ X bᵈ)) by apply close_body_tvar_notin.
      rewrite open_body_wrt_typ_close_body_wrt_typ.
      rewrite_env (nil ++ X ~ ▫ ++ θ) in H2.
      forwards*: trans_body_rename_tvar X0 H2.
    + apply IHa_wf_exp in H2 as Htrans_e; auto.
      eapply a_wf_typ_trans_typ with (θ:=θ) (Ω:=Ω) in H as Htrans_A; auto.
      destruct Htrans_e as [eᵈ].
      destruct Htrans_A as [Aᵈ].
      exists (exp_tapp eᵈ Aᵈ)...
    + apply IHa_wf_exp in H2 as Htrans_e; auto.
      eapply a_wf_typ_trans_typ with (θ:=θ) (Ω:=Ω) in H as Htrans_A; auto.
      destruct Htrans_e as [eᵈ].
      destruct Htrans_A as [Aᵈ].
      exists (exp_anno eᵈ Aᵈ)...
  - intros.
    generalize dependent Ω.
    generalize dependent θ.
    dependent induction H; intros.
    + eapply a_wf_exp_trans_exp in H0...
      eapply a_wf_typ_trans_typ in H...
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


(* not used now *)
Lemma tran_wl_dwl_ss_same_tvar_stvar : forall Γ Ω θ,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  ss_no_etvar θ = denv_no_var (dwl_to_denv Ω).
Proof with auto with Hdb_transfer.
  intros. dependent induction H...
  - simpl... rewrite IHtrans_worklist...
  - simpl... rewrite IHtrans_worklist...
Qed.


Lemma trans_wl_d_wf_stvar : forall Γ Ω θ X,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  wf_ss θ -> X ~ ▪ ∈ θ ->
  a_wf_typ (awl_to_aenv Γ) ` X ->
  dwl_to_denv Ω ⊢ ` X.
Proof with try solve_by_invert.
  intros * Hs Hw Ha Hb. induction Hs; simpl in *.
  - inverts Hb...
  - forwards*: IHHs.
  - inverts Ha... inverts Hb...
    + inverts H2.
      * inverts* H0.
      * forwards*: IHHs. now inverts~ Hw.
        rewrite_env ((X0 ~ ▫) ++ dwl_to_denv Ω). applys* d_wf_typ_weaken_head.
    + inverts H2...
      * forwards*: IHHs. now inverts~ Hw.
        rewrite_env ((X0 ~ ▫) ++ dwl_to_denv Ω). applys* d_wf_typ_weaken_head.
    + inverts H2...
      * forwards*: IHHs. now inverts~ Hw.
        rewrite_env ((X0 ~ ▫) ++ dwl_to_denv Ω). applys* d_wf_typ_weaken_head.
  - inverts Ha...
    + inverts* H.
    + inverts* Hb...
      all: inverts H2...
      2: { inverts* H0. }
      all: inverts Hw.
      all:  rewrite_env ((X0 ~ ▪) ++ dwl_to_denv Ω); applys* d_wf_typ_weaken_head.
  - inverts Hb...
    all: inverts H2...
    all: rewrite_env ([(x, dbind_typ A1ᵈ)] ++ dwl_to_denv Ω); applys* d_wf_typ_weaken_head.
  - inverts Ha... inverts Hw. inverts Hb...
    all: inverts H7... 1,2,4: forwards*: IHHs.
    + inverts H5. exfalso. applys* binds_dom_contradiction.
Qed.

Lemma trans_wl_d_wf_tvar : forall Γ Ω θ X,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  wf_ss θ -> X ~ ▫ ∈ θ ->
  a_wf_typ (awl_to_aenv Γ) ` X ->
  dwl_to_denv Ω ⊢ ` X.
Proof with try solve_by_invert.
  intros * Hs Hw Ha Hb. induction Hs; simpl in *.
  - inverts Hb...
  - forwards*: IHHs.
  - inverts Ha...
    + inverts* H.
    + inverts* Hb...
      all: inverts H2...
      1: { inverts* H0. }
      all: inverts Hw.
      all: rewrite_env ((X0 ~ ▫) ++ dwl_to_denv Ω); applys* d_wf_typ_weaken_head.
  - inverts Ha... inverts Hb...
      all: inverts H2...
      2: { inverts* H0. }
      all: inverts Hw.
      all: rewrite_env ((X0 ~ ▪) ++ dwl_to_denv Ω); applys* d_wf_typ_weaken_head.
  - inverts Hb...
    all: inverts H2...
    all: rewrite_env ([(x, dbind_typ A1ᵈ)] ++ dwl_to_denv Ω); applys* d_wf_typ_weaken_head.
  - inverts Ha... inverts Hw. inverts Hb...
    all: inverts H7... 1,2,4: forwards*: IHHs.
    + inverts H5. exfalso. applys* binds_dom_contradiction.
Qed.

Lemma trans_wl_wf_bind_typ : forall Γ Ω θ X T,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  binds X (dbind_typ T) θ ->
  dwl_to_denv Ω ⊢ T.
Proof.
  intros. dependent induction H...
  - inversion H0.
  - simpl. auto.
  - inversion H0...
    dependent destruction H1.
    simpl. apply d_wf_typ_weaken_cons. auto.
  - inversion H0...
    dependent destruction H1.
    simpl. apply d_wf_typ_weaken_cons. auto.
  - simpl. apply d_wf_typ_weaken_cons. auto.
  - simpl. inversion H5.
    dependent destruction H6.
    eapply d_sub_dwft; eauto.
    auto.
Qed.

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

Lemma tran_wl_wf_trans_typ : forall Γ Ω θ Aᵃ Aᵈ,
  lc_typ Aᵃ ->
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  θ ⫦ᵗ Aᵃ ⇝ Aᵈ ->
  a_wf_typ (awl_to_aenv Γ) Aᵃ ->
  d_wf_typ (dwl_to_denv Ω) Aᵈ.
Proof with eauto with Hdb_transfer.
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
    + applys* trans_wl_d_wf_tvar.
    + applys* trans_wl_d_wf_stvar.
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
Qed.


Lemma trans_wl_dom_upper_bound : forall θ Γ Ω,
  nil ⫦ Γ ⇝ Ω ⫣ θ ->
  dom (dwl_to_denv Ω) [<=] dom (awl_to_aenv Γ).
Proof with auto with Hdb_transfer.
  intros. dependent induction H; simpl...
  - fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
  - rewrite IHtrans_worklist... fsetdec.
Qed.


(* not used now *)
Lemma a_wf_wl_d_wf_wl : forall θ Γ Ω,
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> ⊢ᵈʷ Ω.
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
    eapply tran_wl_wf_trans_typ with (Aᵃ:=A1ᵃ)...
    eapply trans_typ_lc_atyp...
Abort.


Lemma a_wf_wl_d_wf_env : forall θ Γ Ω,
  ⊢ᵃ Γ -> nil ⫦ Γ ⇝ Ω ⫣ θ -> ⊢ dwl_to_denv Ω.
Proof with eauto.
  intros. dependent induction H0; dependent destruction H; simpl...
  - econstructor...
    rewrite trans_wl_dom_upper_bound...
  - econstructor...
    rewrite trans_wl_dom_upper_bound...
  - econstructor...
    eapply tran_wl_wf_trans_typ with (Aᵃ:=A1ᵃ)...
    eapply trans_typ_lc_atyp...
    rewrite trans_wl_dom_upper_bound...
Qed.


(* depedent destruction all non-atomic ⊢ᵃ relation *)
Ltac destruct_a_wf_wl :=
  repeat
    lazymatch goal with
    | H : a_wf_wl (aworklist_conswork ?Γ ?w) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_consvar ?Γ ?w ?b) |- _ => dependent destruction H
    | H : a_wf_wl (aworklist_constvar ?Γ ?X ?b) |- _ => dependent destruction H
    | H : a_wf_work ?Ω ?w |- _ => dependent destruction H
    | H : a_wf_typ ?E (open_typ_wrt_typ ?A ?T) |- _ => fail
    | H : a_wf_typ ?E (?Ct ?A1 ?A2) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?b) |- _ => dependent destruction H
    | H : a_wf_exp ?E (?Ce ?e1 ?e2) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _ _) |- _ => dependent destruction H
    | H : a_wf_cont ?E (?C_C _ _ _) |- _ => dependent destruction H
    end.

Lemma a_wf_work_applied : forall Γ c A w,
  a_wf_cont Γ c ->
  a_wf_typ Γ A ->
  apply_cont c A w ->
  a_wf_work Γ w.
Proof with eauto with Hdb_transfer.
  intros. induction H1; try solve [destruct_a_wf_wl; constructor; eauto with Hdb_transfer].
Qed.


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

Lemma wf_subst_set_strength_tvar : forall θ θ' X,
  wf_ss (θ' ++ θ) ->
  X `notin` dom (θ' ++ θ) ->
  wf_ss (θ' ++ X ~ ▫ ++ θ).
Proof with auto with Hdb_transfer.
  intros. induction θ'.
  - simpl in *. constructor...
  - destruct a. destruct d; simpl in *.
    + dependent destruction H. econstructor...
    + dependent destruction H. econstructor...
    + dependent destruction H. econstructor...
      rewrite ss_to_denv_app in *.
      replace ((X, ▫) :: θ) with ([(X, ▫)] ++ θ). rewrite ss_to_denv_app.
      applys~ d_mono_typ_weaken.
      now auto.
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
    rewrite ss_to_denv_app in *.
    replace ((X, ▫) :: θ1) with ([(X, ▫)] ++ θ1). rewrite ss_to_denv_app.
    applys~ d_mono_typ_weaken.
    now auto.
Qed.

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

Corollary etvar_bind_no_etvar: forall θ X1 X2 A1 A2,
  wf_ss θ ->
  X1 ~ A1 ∈  θ ->
  X2 ~ A2 ∈ θ ->
  X1 \notin ftvar_in_typ A2.
Proof with eauto with Hdb_transfer.
  intros; eapply wf_ss_typ_no_etvar... clear H0.
  induction H; simpl in *; try solve_by_invert.
  - forwards* [?|?]: binds_cons_1 H1; intuition auto; subst; try solve_by_invert.
    rewrite_env (X ~ ▫ ++ ss_to_denv θ). applys~ d_wf_typ_weaken_head.
  - forwards* [?|?]: binds_cons_1 H1; intuition auto; subst; try solve_by_invert.
    rewrite_env (X ~ ▪ ++ ss_to_denv θ). applys~ d_wf_typ_weaken_head.
  - forwards* [?|?]: binds_cons_1 H1; intuition auto; subst; try solve_by_invert.
    inverts H5. applys~ d_mono_typ_d_wf_typ.
Qed.

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
        econstructor... applys* binds_change_middle.
      * exists ` X... intuition... applys trans_typ__stvar.
        applys* wf_ss_bind_to_tvar.
        applys* binds_change_middle_2. all: intro HF; inverts HF.
      * exists A1. split.
        -- rewrite subst_tvar_in_typ_fresh_eq...
           eapply etvar_bind_no_etvar...
        -- econstructor... applys* binds_change_middle.
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
    + eapply trans_typ__all with (L:=L `union` (dom (θ2 ++ (X, ▫) :: θ1))); intros.
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
Qed.


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

Lemma ss_wf_typ_trans_typ : forall θ Aᵃ,
  ss_wf_typ θ Aᵃ ->
  exists Aᵈ, θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros. induction H...
  - exists*. econstructor. admit.
  - admit.
  - admit.
  - admit.
Admitted. (* The lemma does not hold without wf_ss θ condition *)


Hint Resolve trans_typ_lc_atyp : Hdb_transfer.
Hint Resolve trans_typ_lc_dtyp : Hdb_transfer.

Lemma ss_to_denv_smaller_dom : forall θ,
    dom (ss_to_denv θ) [<=] dom θ.
Proof with simpl; try fsetdec.
  intros. induction θ... destruct a. destruct d...
Qed.

Lemma d_mono_typ_ftvar : forall θ A,
    d_mono_typ θ A -> ftvar_in_typ A [<=] dom θ.
Proof with simpl; try fsetdec.
  intros * Hd. inductions Hd...
  - apply binds_In in H...
Qed.

Corollary d_mono_typ_in_ss_to_denv_ftvar : forall θ A,
    d_mono_typ (ss_to_denv θ) A -> ftvar_in_typ A [<=] dom θ.
Proof with simpl; try fsetdec.
  intros * Hd.
  lets: ss_to_denv_smaller_dom θ.
  forwards~: d_mono_typ_ftvar (ss_to_denv θ) A...
Qed.

Lemma wf_ss_ftvar : forall θ X A,
    wf_ss θ -> X ~ A ∈ θ -> ftvar_in_typ A [<=] dom θ.
Proof with simpl; fsetdec.
  intros * Hw Hb. induction Hw; intros; try solve_by_invert.
  - inverts Hb.
    + inverts H0.
    + forwards~: IHHw...
  - inverts Hb.
    + inverts H0.
    + forwards~: IHHw...
  - inverts Hb.
    + inverts H1. forwards: d_mono_typ_in_ss_to_denv_ftvar H0...
    + forwards~: IHHw...
Qed.

Lemma trans_typ_ftvar : forall θ X A,
    θ ⫦ᵗ ` X ⇝ A -> ftvar_in_typ A [<=] dom θ.
Proof with simpl; try fsetdec.
  introv Ht. induction Ht...
  - apply binds_In in H0...
  - apply binds_In in H0...
  - applys* wf_ss_ftvar.
  - pick fresh Y. inst_cofinites_with Y.
    forwards: ftvar_in_typ_open_typ_wrt_typ_lower A1ᵈ ` Y.
    forwards Ha: KeySetProperties.remove_equal (ftvar_in_typ A1ᵈ) Y. solve_notin.
    assert (Hl: ftvar_in_typ A1ᵈ [<=] dom ((Y, ▫) :: θ)) by fsetdec.
    forwards* Hr: AtomSetNotin.D.F.remove_s_m Y Y Hl.
    forwards He: KeySetProperties.remove_add (dom θ) Y. solve_notin.
    simpl in Hr. clear H H0 H1 Fr Hl. fsetdec.
Qed.

Lemma trans_typ_rev_subst : forall θ1 θ2 Bᵃ Bᵈ X Aᵃ A'ᵈ,
  lc_typ Aᵃ ->
  X `notin` dom (θ2 ++ θ1) ->
  θ1 ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ2 ++ θ1 ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ A'ᵈ ->
  exists Aᵈ, {Bᵈ /ᵗ X} Aᵈ = A'ᵈ /\ θ2 ++ (X, dbind_tvar_empty) :: θ1 ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros * Hlc Hfv Hwft Hinst.
  generalize dependent θ2. generalize dependent X. generalize dependent A'ᵈ.
  dependent induction Hlc; simpl in *; intros.
  - dependent destruction Hinst.
    exists typ_unit...
  - dependent destruction Hinst.
    exists typ_top...
  - dependent destruction Hinst;
    exists typ_bot...
  - destruct (X0 == X) in *; destruct (X == X0) in *; subst; try contradiction.
    + exists (` X0). simpl. unfold eq_dec. destruct (EqDec_eq_of_X X0 X0).
      * split.
        ** rewrite_env (nil ++ θ1) in Hwft.
           forwards: trans_typ_wf_ss Hinst.
           forwards~ HW: trans_typ_weaken θ2 Hwft.
           simpl in HW. forwards*: trans_typ_det HW Hinst.
           now eauto using wf_ss_uniq.
        ** econstructor...
      * contradiction.
    + exists A'ᵈ. split.
      * rewrite~ subst_tvar_in_typ_fresh_eq.
        forwards: trans_typ_ftvar Hinst. solve_notin.
      * rewrite_env (θ2 ++ X0 ~ ▫ ++ θ1). applys~ trans_typ_weaken.
        applys~ wf_subst_set_strength_tvar.
        applys* trans_typ_wf_ss.
  (* - destruct (X0 == X).
    (* - exists (ld_t_var_f x5).
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
      * inversion HinstA; split; auto...  *)
    + (* T and  A'ᵈ is the same and does not contain X *)
      exists T. split.
      * admit.
      * econstructor...
    + exists A'ᵈ. split.
      * admit.
      * admit. *)
  - dependent destruction Hinst.
    apply IHHlc1 in Hinst1... destruct Hinst1 as [A1'ᵈ].
    apply IHHlc2 in Hinst2... destruct Hinst2 as [A2'ᵈ].
    exists (typ_arrow A1'ᵈ A2'ᵈ); simpl...
    intuition... subst...
  - dependent destruction Hinst.
    pick fresh X0. inst_cofinites_with X0.
    rewrite typ_subst_open_comm in H1...
    rewrite_env (((X0, dbind_tvar_empty) :: θ2) ++ θ1) in H1.
    apply H0 in H1...
    destruct H1 as [Aᵈ].
    exists (typ_all (close_typ_wrt_typ X0 Aᵈ)). simpl.
    rewrite subst_tvar_in_typ_close_typ_wrt_typ...
    split...
    + apply f_equal. erewrite typ_open_r_close_l... intuition.
    + eapply trans_typ__all with (L:=L `union` dom (θ2 ++ (X, ▫) :: θ1)); intros.
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
Qed.


Lemma trans_typ_rev_subs_cons : forall θ Bᵃ Bᵈ X Aᵃ A'ᵈ,
  lc_typ Aᵃ ->
  X `notin` dom θ ->
  θ ⫦ᵗ Bᵃ ⇝ Bᵈ ->
  θ ⫦ᵗ {Bᵃ /ᵗ X} Aᵃ ⇝ A'ᵈ ->
  exists Aᵈ, {Bᵈ /ᵗ X} Aᵈ = A'ᵈ /\ (X, dbind_tvar_empty) :: θ ⫦ᵗ Aᵃ ⇝ Aᵈ.
Proof with eauto with Hdb_transfer.
  intros.
  rewrite_env (nil ++ θ) in H2.
  eapply trans_typ_rev_subst in H2...
Qed.



Definition transfer (Γ : aworklist) (Ω : dworklist)  : Prop :=
  exists θ', trans_worklist nil Γ Ω θ'.