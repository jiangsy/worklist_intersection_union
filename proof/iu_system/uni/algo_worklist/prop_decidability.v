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

Inductive split_size_work : aworklist -> work -> nat -> Prop :=
  | split_size_work_infer : forall Γ e c,
      split_size_work Γ (work_infer e c) 0
  | split_size_work_check : forall Γ e A,
      split_size_work Γ (work_check e A) 0
  | split_size_work_infabs : forall Γ A c n,
      split_size Γ A n ->
      split_size_work Γ (work_infabs A c) n
  | split_size_work_infabsunion : forall Γ A1 A2 c,
      split_size_work Γ (work_infabsunion A1 A2 c) 0
  | split_size_work_infapp : forall Γ A e c,
      split_size_work Γ (work_infapp A e c) 0
  | split_size_work_inftapp : forall Γ A1 A2 c,
      split_size_work Γ (work_inftapp A1 A2 c) 0
  | split_size_work_sub : forall Γ A1 A2 n1 n2,
      split_size Γ A1 n1 ->
      split_size Γ A2 n2 ->
      split_size_work Γ (work_sub A1 A2) (n1 + n2)
  | split_size_work_inftappunion : forall Γ A1 A2 A3 c,
      split_size_work Γ (work_inftappunion A1 A2 A3 c) 0
  | split_size_work_unioninftapp : forall Γ A1 A2 c,
      split_size_work Γ (work_unioninftapp A1 A2 c) 0
  | split_size_work_unioninfabs : forall Γ A1 A2 c,
      split_size_work Γ (work_unioninfabs A1 A2 c) 0
  | split_size_work_apply : forall Γ c A,
      split_size_work Γ (work_apply c A) 0.

Hint Constructors split_size_work : core.

Theorem split_size_work_det : forall Γ w n1 n2,
  split_size_work Γ w n1 ->
  split_size_work Γ w n2 ->
  n1 = n2.
Proof.
  intros Γ w n1 n2 Hss1.
  generalize dependent n2.
  dependent induction Hss1;
  try solve [intros n' Hss; dependent destruction Hss; auto].  
  - intros n' Hss. dependent destruction Hss; auto.
    eapply split_size_det; eauto.
  - intros n' Hss. dependent destruction Hss; auto.
    eapply split_size_det; eauto.
Qed.

Theorem split_size_work_total : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w ->
  exists n, split_size_work Γ w n.
Proof.
  intros Γ w Hwf.
  dependent induction Hwf; auto; try solve [exists 0; auto].
  - apply split_size_total in H; auto.
    destruct H as [n Hss].
    exists n. auto.
  - apply split_size_total in H; auto.
    apply split_size_total in H0; auto.
    destruct H as [n1 Hss1].
    destruct H0 as [n2 Hss2].
    exists (n1 + n2). auto.
Qed.

Inductive split_size_wl : aworklist -> nat -> Prop :=
  | split_size_wl_empty : split_size_wl aworklist_empty 0
  | split_size_wl_constvar : forall Γ X A n,
      split_size_wl Γ n ->
      split_size_wl (aworklist_constvar Γ X A) n
  | split_size_wl_consvar : forall Γ X A n,
      split_size_wl Γ n ->
      split_size_wl (aworklist_consvar Γ X A) n
  | split_size_wl_conswork : forall Γ w m n,
      split_size_work Γ w m ->
      split_size_wl Γ n ->
      split_size_wl (aworklist_conswork Γ w) (m + n).

Hint Constructors split_size_wl : core.

Theorem split_size_wl_det : forall Γ n1 n2,
  split_size_wl Γ n1 ->
  split_size_wl Γ n2 ->
  n1 = n2.
Proof.
  intros Γ n1 n2 Hss1.
  generalize dependent n2.
  dependent induction Hss1;
  try solve [intros n' Hss; dependent destruction Hss; auto].
  - intros n' Hss. dependent destruction Hss; auto.
    apply IHHss1 in Hss. subst.
    eapply split_size_work_det in H; eauto. 
Qed.

Theorem split_size_wl_total : forall Γ,
  a_wf_wl Γ -> exists n, split_size_wl Γ n.
Proof.
  intros Γ Hwf.
  dependent induction Hwf; auto;
  try solve [destruct IHHwf as [n Hss]; exists n; auto].
  - exists 0. auto.
  - destruct IHHwf as [n Hss].
    apply split_size_work_total in H; auto.
    destruct H as [m Hss'].
    exists (m + n). auto.
Qed.

Fixpoint all_size (A : typ) : nat :=
  match A with
  | typ_unit => 0
  | typ_bot => 0
  | typ_top => 0
  | typ_var_f _ => 0
  | typ_var_b _ => 0
  | typ_arrow A1 A2 => all_size A1 + all_size A2
  | typ_all A => 1 + all_size A
  | typ_union A1 A2 => all_size A1 + all_size A2
  | typ_intersection A1 A2 => all_size A1 + all_size A2
  end.

Definition all_size_work (w : work) : nat :=
  match w with
  | work_infer _ _ => 0
  | work_check _ _ => 0
  | work_infabs A _ => all_size A
  | work_infabsunion _ _ _ => 0
  | work_infapp _ _ _ => 0
  | work_inftapp _ _ _ => 0
  | work_sub A1 A2 => all_size A1 + all_size A2
  | work_inftappunion _ _ _ _ => 0
  | work_unioninftapp _ _ _ => 0
  | work_unioninfabs _ _ _ => 0
  | work_apply _ _ => 0
  end.

Fixpoint all_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => all_size_wl Γ'
  | aworklist_consvar Γ' _ _ => all_size_wl Γ'
  | aworklist_conswork Γ' w => all_size_work w + all_size_wl Γ'
  end.

Inductive measure : aworklist -> typ -> nat -> Prop :=
  | measure_typ : forall Γ A n,
      split_size Γ A n -> 
      measure Γ A (3 * n + all_size A).

Hint Constructors measure : core.

Theorem measure_det : forall Γ A n1 n2,
  measure Γ A n1 ->
  measure Γ A n2 ->
  n1 = n2.
Proof.
  intros Γ A n1 n2 Hm1.
  generalize dependent n2.
  dependent induction Hm1.
  - intros n' Hm. dependent destruction Hm.
    eapply split_size_det in H; eauto.
Qed.

Theorem measure_total : forall Γ A,
  a_wf_typ (awl_to_aenv Γ) A ->
  exists n, measure Γ A n.
Proof.
  intros Γ A Hwf.
  dependent induction Hwf; auto;
  try solve [exists (3 * 0 + 0); apply measure_typ; auto].
  - specialize (IHHwf1 Γ).
    specialize (IHHwf2 Γ).
    destruct IHHwf1 as [n1 Hm1]; auto.
    destruct IHHwf2 as [n2 Hm2]; auto.
    inversion Hm1. subst.
    inversion Hm2. subst.
    destruct (smono_typ_dec (awl_to_aenv Γ) (typ_arrow A1 A2)) as [Hsmono | Hnsmono].
    + exists (3 * 0 + all_size (typ_arrow A1 A2)). auto.
    + exists (3 * (1 + n + n0) + all_size (typ_arrow A1 A2)). auto.
  - pick fresh X. inst_cofinites_with X.
    specialize (H1 (aworklist_constvar Γ X abind_tvar_empty)).
    destruct H1 as [n Hm]; auto.
    inversion Hm. subst.
    exists (3 * n0 + all_size (typ_all A)).
    apply measure_typ. admit.
  - specialize (IHHwf1 Γ).
    specialize (IHHwf2 Γ).
    destruct IHHwf1 as [n1 Hm1]; auto.
    destruct IHHwf2 as [n2 Hm2]; auto.
    inversion Hm1. subst.
    inversion Hm2. subst.
    exists (3 * (n + n0) + all_size (typ_union A1 A2)). auto.
  - specialize (IHHwf1 Γ).
    specialize (IHHwf2 Γ).
    destruct IHHwf1 as [n1 Hm1]; auto.
    destruct IHHwf2 as [n2 Hm2]; auto.
    inversion Hm1. subst.
    inversion Hm2. subst.
    exists (3 * (n + n0) + all_size (typ_intersection A1 A2)). auto.
Admitted.

Inductive measure_work : aworklist -> work -> nat -> Prop :=
  | measure_work_infer : forall Γ e c,
      measure_work Γ (work_infer e c) 0
  | measure_work_check : forall Γ e A,
      measure_work Γ (work_check e A) 0
  | measure_work_infabs : forall Γ A c n,
      measure Γ A n ->
      measure_work Γ (work_infabs A c) n
  | measure_work_infabsunion : forall Γ A1 A2 c,
      measure_work Γ (work_infabsunion A1 A2 c) 0
  | measure_work_infapp : forall Γ A e c,
      measure_work Γ (work_infapp A e c) 0
  | measure_work_inftapp : forall Γ A1 A2 c,
      measure_work Γ (work_inftapp A1 A2 c) 0
  | measure_work_sub : forall Γ A1 A2 n1 n2,
      measure Γ A1 n1 -> measure Γ A2 n2 ->
      measure_work Γ (work_sub A1 A2) (n1 + n2)
  | measure_work_inftappunion : forall Γ A1 A2 A3 c,
      measure_work Γ (work_inftappunion A1 A2 A3 c) 0
  | measure_work_unioninftapp : forall Γ A1 A2 c,
      measure_work Γ (work_unioninftapp A1 A2 c) 0
  | measure_work_unioninfabs : forall Γ A1 A2 c,
      measure_work Γ (work_unioninfabs A1 A2 c) 0
  | measure_work_apply : forall Γ c A,
      measure_work Γ (work_apply c A) 0.

Hint Constructors measure_work : core.

Theorem measure_work_det : forall Γ w n1 n2,
  measure_work Γ w n1 ->
  measure_work Γ w n2 ->
  n1 = n2.
Proof.
  intros Γ w n1 n2 Hm1.
  generalize dependent n2.
  dependent induction Hm1;
  try solve [intros n' Hm; dependent destruction Hm; auto].
  - intros n' Hm. dependent destruction Hm; auto.
    eapply measure_det in H; eauto.
  - intros n' Hm. dependent destruction Hm; auto.
    eapply measure_det in H; eauto.
    eapply measure_det in H0; eauto.
Qed.

Theorem measure_work_total : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w ->
  exists n, measure_work Γ w n.
Proof.
  intros Γ w Hwf.
  dependent induction Hwf; auto;
  try solve [exists 0; auto].
  - apply measure_total in H; auto.
    destruct H as [n Hm].
    exists n. auto.
  - apply measure_total in H; auto.
    apply measure_total in H0; auto.
    destruct H as [n1 Hm1].
    destruct H0 as [n2 Hm2].
    exists (n1 + n2). auto.
Qed.

Inductive measure_wl : aworklist -> nat -> Prop :=
  | measure_wl_empty : measure_wl aworklist_empty 0
  | measure_wl_consevar : forall Γ X A1 A2 n,
      measure_wl Γ n ->
      measure_wl (aworklist_constvar Γ X (abind_bound A1 A2)) (1 + n)
  | measure_wl_constvar : forall Γ X n,
      measure_wl Γ n ->
      measure_wl (aworklist_constvar Γ X abind_tvar_empty) n
  | measure_wl_conssvar : forall Γ X n,
      measure_wl Γ n ->
      measure_wl (aworklist_constvar Γ X abind_stvar_empty) n
  | measure_wl_consvar : forall Γ X A n,
      measure_wl Γ n ->
      measure_wl (aworklist_consvar Γ X A) n
  | measure_wl_conswork : forall Γ w m n,
      measure_work Γ w m ->
      measure_wl Γ n ->
      measure_wl (aworklist_conswork Γ w) (m + n).

Hint Constructors measure_wl : core.

Theorem measure_wl_det : forall Γ n1 n2,
  measure_wl Γ n1 ->
  measure_wl Γ n2 ->
  n1 = n2.
Proof.
  intros Γ n1 n2 Hm1.
  generalize dependent n2.
  dependent induction Hm1;
  try solve [intros n' Hm; dependent destruction Hm; auto].
  - intros n' Hm. dependent destruction Hm; auto.
    eapply measure_work_det in H; eauto.
Qed.

Theorem measure_wl_total : forall Γ,
  a_wf_wl Γ -> exists n, measure_wl Γ n.
Proof.
  intros Γ Hwf.
  dependent induction Hwf; auto;
  try solve [destruct IHHwf as [n Hm]; exists n; auto].
  - exists 0. auto.
  - destruct IHHwf as [n Hm]. exists (1 + n). auto.
  - destruct IHHwf as [n Hm].
    apply measure_work_total in H; auto.
    destruct H as [m Hm'].
    exists (m + n). auto.
Qed.
