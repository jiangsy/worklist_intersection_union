Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import ln_utils.

Fixpoint exp_size (e : exp) : nat :=
  match e with
  | exp_unit => 1
  | exp_var_b _ => 1
  | exp_var_f _ => 1
  | exp_abs e => 1 + exp_size e
  | exp_app e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_tabs (body_anno e _) => 1 + exp_size e
  | exp_tapp e _ => 1 + exp_size e
  | exp_anno e _ => 1 + exp_size e
  end.

Fixpoint exp_size_cont (c : cont) : nat :=
  match c with
  | cont_infabs c => 1 + exp_size_cont c
  | cont_infabsunion _ c => 1 + exp_size_cont c
  | cont_infapp e c => 1 + exp_size e + exp_size_cont c
  | cont_inftapp _ c => 1 + exp_size_cont c
  | cont_inftappunion _ _ c => 1 + exp_size_cont c
  | cont_unioninftapp _ c => 1 + exp_size_cont c
  | cont_unioninfabs _ c => 1 + exp_size_cont c
  | cont_sub A => 0
  end.

Definition exp_size_work (w : work) : nat :=
  match w with
  | work_infer e c => exp_size e + exp_size_cont c
  | work_check e _ => exp_size e
  | work_infabs _ c => exp_size_cont c
  | work_infabsunion _ _ c => exp_size_cont c
  | work_infapp _ e c => exp_size e + exp_size_cont c
  | work_inftapp _ _ c => exp_size_cont c
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ c => exp_size_cont c
  | work_unioninftapp _ _ c => exp_size_cont c
  | work_unioninfabs _ _ c => exp_size_cont c
  | work_apply c _ => exp_size_cont c
  end.

Fixpoint exp_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => exp_size_wl Γ'
  | aworklist_consvar Γ' _ _ => exp_size_wl Γ'
  | aworklist_conswork Γ' w => exp_size_work w + exp_size_wl Γ'
  end.

Fixpoint judge_size_cont (c : cont) : nat :=
  match c with
  | cont_infabs c => 1 + judge_size_cont c
  | cont_infabsunion _ c => 1 + judge_size_cont c
  | cont_infapp _ c => 3 + judge_size_cont c
  | cont_inftapp _ c => 1 + judge_size_cont c
  | cont_inftappunion _ _ c => 1 + judge_size_cont c
  | cont_unioninftapp _ c => 1 + judge_size_cont c
  | cont_unioninfabs _ c => 1 + judge_size_cont c
  | cont_sub A => 0
  end.

Definition judge_size_work (w : work) : nat :=
  match w with
  | work_infer e c => 1 + exp_size_cont c
  | work_check e _ => 2 + exp_size e
  | work_infabs _ c => 1 + exp_size_cont c
  | work_infabsunion _ _ c => 1 + exp_size_cont c
  | work_infapp _ e c => 3 + exp_size_cont c
  | work_inftapp _ _ c => 1 + exp_size_cont c
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ c => 1 + exp_size_cont c
  | work_unioninftapp _ _ c => 1 + exp_size_cont c
  | work_unioninfabs _ _ c => 1 + exp_size_cont c
  | work_apply c _ => exp_size_cont c
  end.

Fixpoint judge_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => judge_size_wl Γ'
  | aworklist_consvar Γ' _ _ => judge_size_wl Γ'
  | aworklist_conswork Γ' w => judge_size_work w + judge_size_wl Γ'
  end.

Hint Constructors a_wl_red : core.

Lemma decidablity_lemma : forall ne nj Γ,
  ⊢ᵃ Γ ->
  exp_size_wl Γ < ne ->
  judge_size_wl Γ < nj ->
  Γ ⟶ᵃʷ⁎⋅ \/ ¬ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros ne. induction ne; intro nj; induction nj.
  - intros. inversion H0.
  - intros. inversion H0.
  - intros. inversion H1.
  - intros. dependent destruction H; auto.
Admitted.

Inductive split_size : aworklist -> typ -> nat -> Prop :=
  | split_size_unit : forall Γ,
      split_size Γ typ_unit 0
  | split_size_bot : forall Γ,
      split_size Γ typ_bot 0
  | split_size_top : forall Γ,
      split_size Γ typ_top 0
  | split_size_var_f : forall Γ X,
      split_size Γ (typ_var_f X) 0
  | split_size_var_b : forall Γ n,
      split_size Γ (typ_var_b n) 0
  | split_size_arrow : forall Γ A1 A2,
      a_smono_typ (awl_to_aenv Γ) (typ_arrow A1 A2) ->
      split_size Γ (typ_arrow A1 A2) 0
  | split_size_arrow_s : forall Γ A1 A2 n1 n2,
      ~ a_smono_typ (awl_to_aenv Γ) (typ_arrow A1 A2) ->
      split_size Γ A1 n1 -> split_size Γ A2 n2 ->
      split_size Γ (typ_arrow A1 A2) (1 + n1 + n2)
  | split_size_all : forall L Γ A n,
      ( forall X , X \notin L ->
        split_size (aworklist_constvar Γ X abind_stvar_empty) (open_typ_wrt_typ A (typ_var_f X)) n) ->
      split_size Γ (typ_all A) n
  | split_size_union : forall Γ A1 A2 n1 n2,
      split_size Γ A1 n1 ->
      split_size Γ A2 n2 ->
      split_size Γ (typ_union A1 A2) (n1 + n2)
  | split_size_intersection : forall Γ A1 A2 n1 n2,
      split_size Γ A1 n1 ->
      split_size Γ A2 n2 ->
      split_size Γ (typ_intersection A1 A2) (n1 + n2)
.

Hint Constructors split_size : core.
Hint Constructors a_smono_typ : core.

Theorem smono_typ_dec : forall Δ A,
  a_smono_typ Δ A \/ ~ a_smono_typ Δ A.
Proof.
  intros A Hwf.
  induction Hwf; auto; try solve [right; intro Hcontra; inversion Hcontra].
Qed.

Theorem split_size_total : forall Γ A,
  a_wf_typ (awl_to_aenv Γ) A ->
  exists n, split_size Γ A n.
Proof.
  intros Γ A Hwf.
  dependent induction Hwf; auto; try solve [exists 0; auto].
  - specialize (IHHwf1 Γ).
    specialize (IHHwf2 Γ).
    destruct IHHwf1 as [n1 Hss1]; auto.
    destruct IHHwf2 as [n2 Hss2]; auto.
    destruct (smono_typ_dec (awl_to_aenv Γ) (typ_arrow A1 A2)) as [Hsmono | Hnsmono].
    + exists 0. auto.
    + exists (1 + n1 + n2). auto.
  - pick fresh X. inst_cofinites_with X. 
    specialize (H1 (aworklist_constvar Γ X abind_tvar_empty)).
    destruct H1 as [n Hss]; auto.
    exists n. admit.
  - specialize (IHHwf1 Γ).
    specialize (IHHwf2 Γ).
    destruct IHHwf1 as [n1 Hss1]; auto.
    destruct IHHwf2 as [n2 Hss2]; auto.
    exists (n1 + n2). auto.
  - specialize (IHHwf1 Γ).
    specialize (IHHwf2 Γ).
    destruct IHHwf1 as [n1 Hss1]; auto.
    destruct IHHwf2 as [n2 Hss2]; auto.
    exists (n1 + n2). auto.
Admitted.

Theorem split_size_det : forall Γ A n1 n2,
  split_size Γ A n1 ->
  split_size Γ A n2 ->
  n1 = n2.
Proof.
  intros Γ A n1 n2 Hss1.
  generalize dependent n2.
  dependent induction Hss1;
  try solve [intros n' Hss; dependent destruction Hss; auto].
  - intros n' Hss. dependent destruction Hss; auto.
    unfold not in H0. apply H0 in H. contradiction.
  - intros n' Hss.
    dependent destruction Hss.
    + unfold not in H. apply H in H0. contradiction.
    + apply IHHss1_1 in Hss1. apply IHHss1_2 in Hss2.
      subst. auto.
  - intros n' Hss.
    dependent destruction Hss.
    pick fresh X. inst_cofinites_with X.
    apply H0 in H1. subst. auto.
Qed.
