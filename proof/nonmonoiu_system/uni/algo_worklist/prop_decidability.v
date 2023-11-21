Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Coq.micromega.Lia.


Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_small_step.
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
  | work_infer e c => 1 + judge_size_cont c
  | work_check e _ => 2 + exp_size e
  | work_infabs _ c => 1 + judge_size_cont c
  | work_infabsunion _ _ c => 1 + judge_size_cont c
  | work_infapp _ e c => 3 + judge_size_cont c
  | work_inftapp _ _ c => 1 + judge_size_cont c
  | work_sub _ _ => 1
  | work_inftappunion _ _ _ c => 1 + judge_size_cont c
  | work_unioninftapp _ _ c => 1 + judge_size_cont c
  | work_unioninfabs _ _ c => 1 + judge_size_cont c
  | work_apply c _ => judge_size_cont c
  end.

Fixpoint judge_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => judge_size_wl Γ'
  | aworklist_consvar Γ' _ _ => judge_size_wl Γ'
  | aworklist_conswork Γ' w => judge_size_work w + judge_size_wl Γ'
  end.

Hint Constructors a_wl_red : core.

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
      a_mono_typ (awl_to_aenv Γ) (typ_arrow A1 A2) ->
      split_size Γ (typ_arrow A1 A2) 0
  | split_size_arrow_s : forall Γ A1 A2 n1 n2,
      ~ a_mono_typ (awl_to_aenv Γ) (typ_arrow A1 A2) ->
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
Hint Constructors a_mono_typ : core.

Theorem smono_typ_dec : forall Δ A,
  a_mono_typ Δ A \/ ~ a_mono_typ Δ A.
Proof.
  intros A Hwf.
  induction Hwf; auto; try solve [right; intro Hcontra; inversion Hcontra].
Admitted.

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

Inductive measure1 : aworklist -> typ -> nat -> Prop :=
  | measure1_typ : forall Γ A n,
      split_size Γ A n -> 
      measure1 Γ A (3 * n + all_size A).

Hint Constructors measure1 : core.

Theorem measure1_det : forall Γ A n1 n2,
  measure1 Γ A n1 ->
  measure1 Γ A n2 ->
  n1 = n2.
Proof.
  intros Γ A n1 n2 Hm1.
  generalize dependent n2.
  dependent induction Hm1.
  - intros n' Hm. dependent destruction Hm.
    eapply split_size_det in H; eauto.
Qed.

Theorem measure1_total : forall Γ A,
  a_wf_typ (awl_to_aenv Γ) A ->
  exists n, measure1 Γ A n.
Proof.
  intros Γ A Hwf.
  dependent induction Hwf; auto;
  try solve [exists (3 * 0 + 0); apply measure1_typ; auto].
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
    apply measure1_typ. admit.
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

Inductive measure1_work : aworklist -> work -> nat -> Prop :=
  | measure1_work_infer : forall Γ e c,
      measure1_work Γ (work_infer e c) 0
  | measure1_work_check : forall Γ e A,
      measure1_work Γ (work_check e A) 0
  | measure1_work_infabs : forall Γ A c n,
      measure1 Γ A n ->
      measure1_work Γ (work_infabs A c) n
  | measure1_work_infabsunion : forall Γ A1 A2 c,
      measure1_work Γ (work_infabsunion A1 A2 c) 0
  | measure1_work_infapp : forall Γ A e c,
      measure1_work Γ (work_infapp A e c) 0
  | measure1_work_inftapp : forall Γ A1 A2 c,
      measure1_work Γ (work_inftapp A1 A2 c) 0
  | measure1_work_sub : forall Γ A1 A2 n1 n2,
      measure1 Γ A1 n1 -> measure1 Γ A2 n2 ->
      measure1_work Γ (work_sub A1 A2) (n1 + n2)
  | measure1_work_inftappunion : forall Γ A1 A2 A3 c,
      measure1_work Γ (work_inftappunion A1 A2 A3 c) 0
  | measure1_work_unioninftapp : forall Γ A1 A2 c,
      measure1_work Γ (work_unioninftapp A1 A2 c) 0
  | measure1_work_unioninfabs : forall Γ A1 A2 c,
      measure1_work Γ (work_unioninfabs A1 A2 c) 0
  | measure1_work_apply : forall Γ c A,
      measure1_work Γ (work_apply c A) 0.

Hint Constructors measure1_work : core.

Theorem measure1_work_det : forall Γ w n1 n2,
  measure1_work Γ w n1 ->
  measure1_work Γ w n2 ->
  n1 = n2.
Proof.
  intros Γ w n1 n2 Hm1.
  generalize dependent n2.
  dependent induction Hm1;
  try solve [intros n' Hm; dependent destruction Hm; auto].
  - intros n' Hm. dependent destruction Hm; auto.
    eapply measure1_det in H; eauto.
  - intros n' Hm. dependent destruction Hm; auto.
    eapply measure1_det in H; eauto.
    eapply measure1_det in H0; eauto.
Qed.

Theorem measure1_work_total : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w ->
  exists n, measure1_work Γ w n.
Proof.
  intros Γ w Hwf.
  dependent induction Hwf; auto;
  try solve [exists 0; auto].
  - apply measure1_total in H; auto.
    destruct H as [n Hm].
    exists n. auto.
  - apply measure1_total in H; auto.
    apply measure1_total in H0; auto.
    destruct H as [n1 Hm1].
    destruct H0 as [n2 Hm2].
    exists (n1 + n2). auto.
Qed.

Inductive measure1_wl : aworklist -> nat -> Prop :=
  | measure1_wl_empty : measure1_wl aworklist_empty 0
  | measure1_wl_consevar : forall Γ X A1 A2 n,
      measure1_wl Γ n ->
      measure1_wl (aworklist_constvar Γ X (abind_bound A1 A2)) (1 + n)
  | measure1_wl_constvar : forall Γ X n,
      measure1_wl Γ n ->
      measure1_wl (aworklist_constvar Γ X abind_tvar_empty) n
  | measure1_wl_conssvar : forall Γ X n,
      measure1_wl Γ n ->
      measure1_wl (aworklist_constvar Γ X abind_stvar_empty) n
  | measure1_wl_consvar : forall Γ X A n,
      measure1_wl Γ n ->
      measure1_wl (aworklist_consvar Γ X A) n
  | measure1_wl_conswork : forall Γ w m n,
      measure1_work Γ w m ->
      measure1_wl Γ n ->
      measure1_wl (aworklist_conswork Γ w) (m + n).

Hint Constructors measure1_wl : core.

Theorem measure1_wl_det : forall Γ n1 n2,
  measure1_wl Γ n1 ->
  measure1_wl Γ n2 ->
  n1 = n2.
Proof.
  intros Γ n1 n2 Hm1.
  generalize dependent n2.
  dependent induction Hm1;
  try solve [intros n' Hm; dependent destruction Hm; auto].
  - intros n' Hm. dependent destruction Hm; auto.
    eapply measure1_work_det in H; eauto.
Qed.

Theorem measure1_wl_total : forall Γ,
  a_wf_wl Γ -> exists n, measure1_wl Γ n.
Proof.
  intros Γ Hwf.
  dependent induction Hwf; auto;
  try solve [destruct IHHwf as [n Hm]; exists n; auto].
  - exists 0. auto.
  - destruct IHHwf as [n Hm]. exists (1 + n). auto.
  - destruct IHHwf as [n Hm].
    apply measure1_work_total in H; auto.
    destruct H as [m Hm'].
    exists (m + n). auto.
Qed.

Fixpoint measure2_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => 1 + measure2_wl Γ'
  | aworklist_consvar Γ' _ _ => 1 + measure2_wl Γ'
  | aworklist_conswork Γ' _ => measure2_wl Γ'
  end.

Lemma decidablity_lemma : forall ne nj nm nmm Γ m,
  ⊢ᵃ Γ ->
  exp_size_wl Γ < ne ->
  judge_size_wl Γ < nj ->
  measure1_wl Γ m -> m < nm ->
  measure2_wl Γ < nmm ->
  Γ ⟶ᵃʷ⁎⋅ \/ ¬ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros ne; induction ne;
  intro nj; induction nj;
  intros nm; induction nm;
  intros nmm; induction nmm;
  try solve [intros; inversion H0];
  try solve [intros; inversion H1];
  try solve [intros; inversion H4].
  intros. inversion H3.
  intros Γ m Hwf He Hj Hm Hle Hmm.
  dependent destruction Hwf; auto.
  - simpl in Hmm. apply lt_S_n in Hmm.
    dependent destruction Hm.
    eapply IHnmm in Hmm as Jg; eauto.
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    eapply Jg in Hcontra; eauto.
  - simpl in Hmm. apply lt_S_n in Hmm.
    dependent destruction Hm.
    eapply IHnmm in Hmm as Jg; eauto.
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    eapply Jg in Hcontra; eauto.
  - simpl in Hmm. apply lt_S_n in Hmm.
    dependent destruction Hm.
    eapply IHnmm in Hmm as Jg; eauto.
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    eapply Jg in Hcontra; eauto.
  - simpl in Hmm. apply lt_S_n in Hmm.
    dependent destruction Hm. apply lt_S_n in Hle.
    eapply IHnmm in Hmm as Jg; eauto.
    (* destruct Jg as [Jg | Jg]; auto. *)
    admit. (* TODO *)
  - dependent destruction H.
    + simpl in He.
      simpl in Hj. apply lt_S_n in Hj.
      dependent destruction Hm.
      simpl in Hmm.
      dependent destruction H.
      * simpl in He. apply lt_S_n in He.
        dependent destruction H1. simpl in Hle.
        assert (Hm': measure1_wl (aworklist_conswork Γ (work_apply c typ_unit)) n).
        { replace n with (0 + n); auto. }
        eapply IHne in Hm' as Jg; eauto.
        destruct Jg as [Jg | Jg]; auto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        eapply Jg in Hcontra; eauto.
      * simpl in He. apply lt_S_n in He.
        dependent destruction H1. simpl in Hle.
        assert (Hm': measure1_wl (aworklist_conswork Γ (work_apply c A)) n).
        { replace n with (0 + n); auto. }
        eapply IHne in Hm' as Jg; eauto.
        destruct Jg as [Jg | Jg]; auto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        admit.
        (* eapply Jg in Hcontra; eauto. *)
Admitted.

Theorem a_wl_mul_red_trans : forall Γ1 Γ2 Γ3,
  a_wl_mul_red Γ1 Γ2 ->
  a_wl_mul_red Γ2 Γ3 ->
  a_wl_mul_red Γ1 Γ3.
Proof.
  induction 1; auto.
  intros. apply IHa_wl_mul_red in H1.
  eapply a_wl_mul_red__step; eauto.
Qed.

(* Inductive measure_tst_sub : aworklist -> typ -> typ -> nat -> Prop :=
  | measure_tst_sub_top : forall Γ A,
      measure_tst_sub Γ A typ_top 0
  | measure_tst_sub_bot : forall Γ A,
      measure_tst_sub Γ typ_bot A 0
  | measure_tst_sub_unit : forall Γ,
      measure_tst_sub Γ typ_unit typ_unit 0
  | measure_tst_sub_var_f : forall Γ X,
      measure_tst_sub Γ (typ_var_f X) (typ_var_f X) 0
  | measure_tst_sub_arrow : forall Γ A1 A2 B1 B2 n1 n2,
      measure_tst_sub Γ B1 A1 n1 ->
      measure_tst_sub Γ A2 B2 n2 ->
      measure_tst_sub Γ (typ_arrow A1 A2) (typ_arrow B1 B2) (1 + n1 + n2)
  | measure_tst_sub_intersection1 : forall Γ A1 B1 B2 n1 n2,
      measure_tst_sub Γ A1 B1 n1 ->
      measure_tst_sub Γ A1 B2 n2 ->
      measure_tst_sub Γ A1 (typ_intersection B1 B2) (1 + n1 + n2)
  | measure_tst_sub_intersection2 : forall Γ A1 B1 B2 n1 n2,
      measure_tst_sub Γ B1 A1 n1 ->
      measure_tst_sub Γ B2 A1 n2 ->
      measure_tst_sub Γ (typ_intersection B1 B2) A1 (1 + max n1 n2)
  | measure_tst_sub_union1 : forall Γ A1 A2 B1 n1 n2,
      measure_tst_sub Γ B1 A1 n1 ->
      measure_tst_sub Γ B1 A2 n2 ->
      measure_tst_sub Γ B1 (typ_union A1 A2) (1 + max n1 n2)
  | measure_tst_sub_union2 : forall Γ A1 B1 B2 n1 n2,
      measure_tst_sub Γ B1 A1 n1 ->
      measure_tst_sub Γ B2 A1 n2 ->
      measure_tst_sub Γ (typ_union B1 B2) A1 (1 + n1 + n2)
.

Theorem measure_tst_sub_det : forall Γ A B n1 n2,
  measure_tst_sub Γ A B n1 ->
  measure_tst_sub Γ A B n2 ->
  n1 = n2.
Proof.
  intros Γ A B n1 n2 Hm1.
  generalize dependent n2.
  induction Hm1.
  -  intros n2 Hm2. dependent destruction Hm2; auto.
Qed.


Inductive measure_tst_work : aworklist -> work -> nat -> Prop :=
  | measure_tst_work_infer : forall Γ e c,
      measure_tst_work Γ (work_infer e c) 0
  | measure_tst_work_check : forall Γ e A,
      measure_tst_work Γ (work_check e A) 0
  | measure_tst_work_infabs : forall Γ A c,
      measure_tst_work Γ (work_infabs A c) 0
  | measure_tst_work_infabsunion : forall Γ A1 A2 c,
      measure_tst_work Γ (work_infabsunion A1 A2 c) 0
  | measure_tst_work_infapp : forall Γ A e c,
      measure_tst_work Γ (work_infapp A e c) 0
  | measure_tst_work_inftapp : forall Γ A1 A2 c,
      measure_tst_work Γ (work_inftapp A1 A2 c) 0
  | measure_tst_work_sub : forall Γ A1 A2 n,
      measure_tst_sub Γ A1 A2 n
      measure_tst_work Γ (work_sub A1 A2) n
  | measure_tst_work_inftappunion : forall Γ A1 A2 A3 c,
      measure_tst_work Γ (work_inftappunion A1 A2 A3 c) 0
.

Inductive measure_tst_wl : aworklist -> nat -> Prop :=
  | measure_tst_wl_empty : measure_tst_wl aworklist_empty 0
  | measure_tst_wl_constvar : forall Γ X A n,
      measure_tst_wl Γ n ->
      measure_tst_wl (aworklist_constvar Γ X A) (1 + n)
  | measure_tst_wl_consvar : forall Γ X A n,
      measure_tst_wl Γ n ->
      measure_tst_wl (aworklist_consvar Γ X A) (1 + n)
  | measure_tst_wl_conswork : forall Γ w m n,
      measure1_work Γ w m ->
      measure_tst_wl Γ n ->
      measure_tst_wl (aworklist_conswork Γ w) (m + n). *)

Fixpoint typ_size (A : typ) : nat :=
  match A with
  | typ_unit => 1
  | typ_bot => 1
  | typ_top => 1
  | typ_var_f _ => 1
  | typ_var_b _ => 1
  | typ_arrow A1 A2 => 1 + typ_size A1 + typ_size A2
  | typ_all A => 1 + typ_size A
  | typ_union A1 A2 => 1 + typ_size A1 + typ_size A2
  | typ_intersection A1 A2 => 1 + typ_size A1 + typ_size A2
  end.

Inductive worklist_eq : aworklist -> aworklist -> Prop :=
  | worklist_eq_refl : forall Γ, worklist_eq Γ Γ.

Theorem decidablity_lemma_sub : forall N A B Γ,
  typ_size A + typ_size B < N ->
  a_wf_typ (awl_to_aenv Γ) A -> a_wf_typ (awl_to_aenv Γ) B ->
  a_wf_wl Γ ->
  (exists Γ',
    a_wl_mul_red (aworklist_conswork Γ (work_sub A B)) Γ' /\
    worklist_eq Γ Γ' /\
    judge_size_wl Γ' <= judge_size_wl Γ) \/
  (a_wl_red (aworklist_conswork Γ (work_sub A B)) -> False).
Proof.
  intros N; dependent induction N;
  intros A B Γ Hsize HwfA HwfB Hwfl;
  try solve [inversion Hsize].
  destruct A; destruct B.
  - left. exists Γ. split; auto.
    eapply a_wl_mul_red__step; eauto.
    split; auto. apply worklist_eq_refl.
  - left. exists Γ. split; auto.
    eapply a_wl_mul_red__step; eauto.
    split; auto. apply worklist_eq_refl.
  - right. intros Hcontra. dependent destruction Hcontra.
  - right. intros Hcontra. dependent destruction Hcontra.
  - dependent destruction HwfB.
    + right. intros Hcontra. dependent destruction Hcontra. admit. (* safe *)
    + right. intros Hcontra. dependent destruction Hcontra. admit. (* safe *)
    + admit.
  - right. intros Hcontra. dependent destruction Hcontra.
  - right. intros Hcontra. dependent destruction Hcontra.
  - simpl in *. apply lt_S_n in Hsize.
    assert (Hsize1: 1 + typ_size B1 < N). { lia. }
    assert (Hsize2: 1 + typ_size B2 < N). { lia. }
    destruct (IHN typ_unit B1 Γ Hsize1) as [[Γ' [Hred [Heq Hle]]]| ]; auto.
    + admit. (* wf *)
    + left. exists Γ'. split; auto.
      eapply a_wl_mul_red__step with (Γ2:=(aworklist_conswork Γ (work_sub typ_unit B1))); eauto.
    + destruct (IHN typ_unit B2 Γ Hsize2) as [[Γ' [Hred [Heq Hle]]]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ'. split; auto.
        eapply a_wl_mul_red__step with (Γ2:=(aworklist_conswork Γ (work_sub typ_unit B2))); eauto.
      * right. intros Hcontra. dependent destruction Hcontra.
        -- apply H. auto.
        -- apply H0. auto.
  - simpl in *. apply lt_S_n in Hsize.
    assert (Hsize1: 1 + typ_size B1 < N). { lia. }
    assert (Hsize2: 1 + typ_size B2 < N). { lia. }
    destruct (IHN typ_unit B2 (aworklist_conswork Γ (work_sub typ_unit B1)) Hsize2) as [[Γ' [Hred [Heq Hle]]]| ]; auto.
    + admit. (* wf *) 
    + admit. (* wf *)
    + assert (Heq': exists Γ'', Γ' = aworklist_conswork Γ'' (work_sub typ_unit B1)).
        { admit. (* possible lemma *) }
      destruct Heq' as [Γ'' Heq']. subst.
      destruct (IHN typ_unit B1 Γ'' Hsize1) as [[Γ''' [Hred' [Heq' Hle']]]| ]; auto.
      * admit. (* wf *) 
      * admit. (* wf *) 
      * left. exists Γ'''. split; auto.
        eapply a_wl_mul_red__step; eauto.
        eapply a_wl_mul_red_trans; eauto.
        split. admit. (* worklist_eq trans *)
        simpl in *. lia.
      * right. intros Hcontra. dependent destruction Hcontra.
        admit. (* Critical *) 
    + right. intros. dependent destruction H0.
      apply H. auto.
  - right. intros Hcontra. dependent destruction Hcontra.
  - left. exists Γ. split; auto.
    eapply a_wl_mul_red__step; eauto.
    split; auto. apply worklist_eq_refl.
  - right. intros Hcontra. dependent destruction Hcontra.
  - inversion HwfB.
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
  - simpl in *. apply lt_S_n in Hsize.
    dependent destruction HwfA.
    inst_cofinites_by (L `union` dom (awl_to_aenv Γ)) using_name X.
    assert (Hsize': typ_size (A ^ᵈ X) + 1 < N). { admit. }
    destruct (IHN (A ^ᵈ X) typ_unit (aworklist_constvar Γ X (abind_bound typ_bot typ_top)) Hsize') as [[Γ' [Hred [Heq Hle]]]| ]; auto.
    + admit. (* wf *)
    + left. exists Γ'. split; auto.
      eapply a_wl_mul_red__step; eauto.
      split. admit. (* worklist_eq *)
      simpl in *. lia.
    + right. intros Hcontra. dependent destruction Hcontra.
      admit. (* rename *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - dependent destruction HwfA.
    inst_cofinites_by (L `union` dom (awl_to_aenv Γ)) using_name X.
    assert (Hsize': typ_size (A ^ᵈ X) + typ_size (B ^ᵈ X) < N). { admit. }
    destruct (IHN (A ^ᵈ X) (B ^ᵈ X) (aworklist_constvar Γ X abind_stvar_empty) Hsize') as [[Γ' [Hred [Heq Hle]]]| ]; auto.
    + admit. (* wf *)
    + admit. (* wf *)
    + left. exists Γ'. split; auto.
      eapply a_wl_mul_red__step; eauto.
Admitted.  
  (* apply lt_S_n in Hsize.   
    left. exists Γ'. split; auto.
      eapply a_wl_mul_red__step with (Γ2:=(aworklist_conswork Γ (work_sub typ_unit B1))); eauto.
      split; auto. apply worklist_eq_refl.
    destruct (IHN (typ_arrow A1 A2) (typ_arrow B1 B2) Γ Hsize) as [[Γ' [Hred [Heq Hle]]]| ]; auto.
    + left. exists Γ'. split; auto.
      eapply a_wl_mul_red__step; eauto.
      split; auto. apply worklist_eq_refl.
    + right. intros Hcontra. dependent destruction Hcontra.
      eapply H in H0; eauto.
  destruct Hlca.
  - destruct Hlcb.
    + left. exists Γ. split; auto.
      eapply a_wl_mul_red__step; eauto.
      split; auto. apply worklist_eq_refl.
    + left. exists Γ. split; auto.
      eapply a_wl_mul_red__step; eauto.
      split; auto. apply worklist_eq_refl.
    + right. intros Hcontra. dependent destruction Hcontra.
    + right. intros Hcontra. dependent destruction Hcontra. *)

(* Theorem decidablity_lemma_infabs : forall A, lc_typ A ->
  forall Γ c, a_wf_wl Γ ->
  (exists Γ' T1 T2,
    a_wl_mul_red (aworklist_conswork Γ (work_infabs A c))
                 (aworklist_conswork Γ' (work_apply c (typ_arrow T1 T2))) /\
    judge_size_wl Γ' <= judge_size_wl Γ) \/
  (a_wl_red (aworklist_conswork Γ (work_infabs A c)) -> False).
Proof.
  intros A Hlct. dependent induction Hlct; intros Γ c Hwfl.
  - right. intros. dependent destruction H.
  - right. intros. dependent destruction H. 
  - left. exists Γ, typ_top, typ_bot.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - left. admit. (* I need to write the right small-step version first. *)
  - left. exists Γ, A1, A2.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - inst_cofinites_by (dom (awl_to_aenv Γ)).
    destruct (H0 x (aworklist_constvar Γ x (abind_bound typ_bot typ_top)) c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step; eauto.
    + right. intros. dependent destruction H2.
      admit. (* rename *)
  - destruct (IHHlct1 Γ (cont_infabsunion A2 c)) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + assert (Hac: apply_cont (cont_infabsunion A2 c) (typ_arrow T1 T2) (work_infabsunion (typ_arrow T1 T2) A2 c)).
        { apply applycont__infabsunion. }
      assert (Hred: a_wl_mul_red (aworklist_conswork Γ' (work_apply (cont_infabsunion A2 c) (typ_arrow T1 T2)))
                                 (aworklist_conswork Γ' (work_infabs A2 ((cont_unioninfabs (typ_arrow T1 T2) c))))).
        { eapply a_wl_mul_red__step; eauto. }
      destruct (IHHlct2 Γ' (cont_unioninfabs (typ_arrow T1 T2) c)) as [[Γ'' [T1' [T2' []]]]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ'', (typ_intersection T1 T1'), (typ_union T2 T2'). split.
        -- eapply a_wl_mul_red__step; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           assert (Hac1: apply_cont (cont_unioninfabs (typ_arrow T1 T2) c) (typ_arrow T1' T2') (work_unioninfabs (typ_arrow T1 T2) (typ_arrow T1' T2') c)).
            { apply applycont__unioninfabs. }
            eapply a_wl_mul_red_trans; eauto.
        -- simpl in *. lia.
      * right. intros. dependent destruction H2.
        eapply H1 with (Γ' := Γ'0) (c' := c') (T := T).
        dependent destruction H3.
        dependent destruction H2.
        eapply a_wl_mul_red__step; eauto.

        eapply a_wl_mul_red__step; eauto.
        dependent destruction H3. admit. (* IMPORTANT *)
    + right. intros. dependent destruction H0.
      dependent destruction H0. apply H in H1. contradiction.
  - destruct (IHHlct1 Γ c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_infabs A1 c))); eauto.
    + destruct (IHHlct2 Γ c) as [[Γ' [T1 [T2 []]]]| ]; auto.
      * left. exists Γ', T1, T2. split; auto.
        eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_infabs A2 c))); eauto.
      * right. intros. dependent destruction H1.
        dependent destruction H1.
        -- apply H in H2. contradiction.
        -- apply H0 in H2. contradiction.
Admitted. *)

Inductive D_infabs : nat -> aworklist -> Prop :=
  | D_infabs_apply : forall n Γ c T1 T2,
      judge_size_wl Γ <= n ->
      D_infabs n (aworklist_conswork Γ (work_apply c (typ_arrow T1 T2)))
  | D_infabs_step : forall n Γ,
      (forall Γ', a_wl_red_ss Γ Γ' -> D_infabs n Γ') -> D_infabs n Γ.

Theorem test :
  forall A, lc_typ A ->
  forall Γ, a_wf_wl Γ ->
  forall c, D_infabs (judge_size_wl Γ) (aworklist_conswork Γ (work_infabs A c)).
Proof.
  induction 1; intros Γ Hwfl c.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
    apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
    apply D_infabs_apply. simpl. lia.
  - admit.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
    apply D_infabs_apply. simpl. lia.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
    assert (Heq: judge_size_wl Γ = judge_size_wl (aworklist_constvar Γ X (abind_bound typ_bot typ_top))).
      { simpl. auto. }
    rewrite Heq.
    apply H0. admit.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
    apply IHlc_typ1. auto.
  - apply D_infabs_step. intros Γ' Hred.
    dependent destruction Hred.
    apply IHlc_typ1. auto.
    apply IHlc_typ2. auto.
Admitted.

Inductive D : nat -> aworklist -> Prop :=
  | D_base : forall n Γ, judge_size_wl Γ <= n -> D n Γ
  | D_step : forall n Γ,
      (forall Γ', a_wl_red_ss Γ Γ' -> D n Γ') -> D n Γ.

Theorem test1 : forall N A B Γ,
  typ_size A + typ_size B < N ->
  a_wf_typ (awl_to_aenv Γ) A -> a_wf_typ (awl_to_aenv Γ) B ->
  a_wf_wl Γ -> D (judge_size_wl Γ) (aworklist_conswork Γ (work_sub A B)).
Proof.
  intros N; dependent induction N;
  intros A B Γ Hsize HwfA HwfB Hwfl;
  try solve [inversion Hsize]. destruct A.
  - destruct B.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
      apply D_base. auto.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
      apply D_base. auto.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
    + admit.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
      eapply IHN; eauto. simpl in *. lia.
      dependent destruction HwfB. auto.
      eapply IHN; eauto. simpl in *. lia.
      dependent destruction HwfB. auto.
    + apply D_step. intros Γ' Hred.
      dependent destruction Hred.
      simpl in *.
      eapply IHN. eauto. simpl in *. lia.
      eapply IHN; eauto. simpl in *. lia.
      dependent destruction HwfB. auto.
      eapply IHN; eauto. simpl in *. lia.
      dependent destruction HwfB. auto.


Inductive all_br_dec_infabs : typ -> Prop :=
  | all_br_dec_infabs_A : forall A,
      (forall A1 A2, A <> typ_intersection A1 A2) ->
      (forall A1 A2, A <> typ_union A1 A2) ->
      (forall A1, A <> typ_all A1) ->
      (forall Γ c, a_wf_wl Γ ->
        (exists Γ' T1 T2,
          a_wl_mul_red (aworklist_conswork Γ (work_infabs A c))
                      (aworklist_conswork Γ' (work_apply c (typ_arrow T1 T2))) /\
          judge_size_wl Γ' <= judge_size_wl Γ) \/
        (a_wl_red (aworklist_conswork Γ (work_infabs A c)) -> False)) ->
      all_br_dec_infabs A
  | all_br_dec_infabs_all : forall A,
      (forall X, all_br_dec_infabs (open_typ_wrt_typ A (typ_var_f X))) ->
      all_br_dec_infabs (typ_all A)
  | all_br_dec_infabs_union : forall A1 A2,
      all_br_dec_infabs A1 -> all_br_dec_infabs A2 ->
      all_br_dec_infabs (typ_union A1 A2)
  | all_br_dec_infabs_intersection1 : forall A1 A2,
      all_br_dec_infabs A1 ->
      all_br_dec_infabs (typ_intersection A1 A2)
  | all_br_dec_infabs_intersection2 : forall A1 A2,
      all_br_dec_infabs A2 ->
      all_br_dec_infabs (typ_intersection A1 A2)
.


Theorem decidablity_lemma_infabs : forall A, lc_typ A -> all_br_dec_infabs A.
Proof.
  intros A Hlct. dependent induction Hlct.
  - apply all_br_dec_infabs_A; unfold not.
    intros A1 A2 Hcontra; inversion Hcontra.
    intros A1 A2 Hcontra; inversion Hcontra.
    intros A1 Hcontra; inversion Hcontra.
    intros Γ c Hwfl. right. intros Hcontra. dependent destruction Hcontra.
  - apply all_br_dec_infabs_A.
    unfold not; intros A1 A2 Hcontra; inversion Hcontra.
    unfold not; intros A1 A2 Hcontra; inversion Hcontra.
    unfold not; intros A1 Hcontra; inversion Hcontra.
    intros Γ c Hwfl. right. intros Hcontra. dependent destruction Hcontra.
  - apply all_br_dec_infabs_A.
    unfold not; intros A1 A2 Hcontra; inversion Hcontra.
    unfold not; intros A1 A2 Hcontra; inversion Hcontra.
    unfold not; intros A1 Hcontra; inversion Hcontra.
    intros Γ c Hwfl. left. exists Γ, typ_top, typ_bot.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - admit. (* I need to write the right small-step version first. *)
  - apply all_br_dec_infabs_A.
    unfold not; intros ? ? Hcontra; inversion Hcontra.
    unfold not; intros ? ? Hcontra; inversion Hcontra.
    unfold not; intros ? Hcontra; inversion Hcontra.
    intros Γ c Hwfl. left. exists Γ, A1, A2.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - apply all_br_dec_infabs_all. intros X. apply H0.
  - apply all_br_dec_infabs_union; auto.
  - apply all_br_dec_infabs_intersection1. auto.
Admitted.

Lemma all_br_dec_infabs_dec : forall A,
  all_br_dec_infabs A -> 
  (forall Γ c, a_wf_wl Γ ->
    (exists Γ' T1 T2,
      a_wl_mul_red (aworklist_conswork Γ (work_infabs A c))
                  (aworklist_conswork Γ' (work_apply c (typ_arrow T1 T2))) /\
      judge_size_wl Γ' <= judge_size_wl Γ) \/
    (a_wl_red (aworklist_conswork Γ (work_infabs A c)) -> False)).
Proof.
  intros A Hdec. dependent induction Hdec.
  - intros Γ c Hwfl. destruct (H2 Γ c Hwfl) as [[Γ' [T1 [T2 []]]]| ]; auto.
  - intros Γ c Hwfl. inst_cofinites_by (dom (awl_to_aenv Γ)).
    destruct (H0 x (aworklist_constvar Γ x (abind_bound typ_bot typ_top)) c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step; eauto.
    + right. intros. dependent destruction H2.
      admit. (* rename *)
  - intros Γ c Hwfl. destruct (IHHdec1 Γ (cont_infabsunion A2 c) Hwfl) as [[Γ' [T1 [T2 []]]]| ].
    + assert (Hac: apply_cont (cont_infabsunion A2 c) (typ_arrow T1 T2) (work_infabsunion (typ_arrow T1 T2) A2 c)).
        { apply applycont__infabsunion. }
      assert (Hred: a_wl_mul_red (aworklist_conswork Γ' (work_apply (cont_infabsunion A2 c) (typ_arrow T1 T2)))
                                 (aworklist_conswork Γ' (work_infabs A2 ((cont_unioninfabs (typ_arrow T1 T2) c))))).
        { eapply a_wl_mul_red__step; eauto. }
      destruct (IHHdec2 Γ' (cont_unioninfabs (typ_arrow T1 T2) c)) as [[Γ'' [T1' [T2' []]]]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ'', (typ_intersection T1 T1'), (typ_union T2 T2'). split.
        -- eapply a_wl_mul_red__step; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           assert (Hac1: apply_cont (cont_unioninfabs (typ_arrow T1 T2) c) (typ_arrow T1' T2') (work_unioninfabs (typ_arrow T1 T2) (typ_arrow T1' T2') c)).
            { apply applycont__unioninfabs. }
            eapply a_wl_mul_red_trans; eauto.
        -- simpl in *. lia.
      * right. intros. dependent destruction H2. admit. (* IMPORTANT *)
    + right. intros. dependent destruction H0.
      apply H in H0. contradiction.
Admitted.


     unfold open_typ_wrt_typ in H. specialize H with x0. simpl in H.
  inversion H.
  intros A Hlct. dependent induction Hlct; intros Γ c Hwfl.
  - right. intros. dependent destruction H.
  - right. intros. dependent destruction H. 
  - left. exists Γ, typ_top, typ_bot.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - left. admit. (* I need to write the right small-step version first. *)
  - left. exists Γ, A1, A2.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - inst_cofinites_by (dom (awl_to_aenv Γ)).
    destruct (H0 x (aworklist_constvar Γ x (abind_bound typ_bot typ_top)) c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step; eauto.
    + right. intros. dependent destruction H2.
      admit. (* rename *)
  - destruct (IHHlct1 Γ (cont_infabsunion A2 c)) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + assert (Hac: apply_cont (cont_infabsunion A2 c) (typ_arrow T1 T2) (work_infabsunion (typ_arrow T1 T2) A2 c)).
        { apply applycont__infabsunion. }
      assert (Hred: a_wl_mul_red (aworklist_conswork Γ' (work_apply (cont_infabsunion A2 c) (typ_arrow T1 T2)))
                                 (aworklist_conswork Γ' (work_infabs A2 ((cont_unioninfabs (typ_arrow T1 T2) c))))).
        { eapply a_wl_mul_red__step; eauto. }
      destruct (IHHlct2 Γ' (cont_unioninfabs (typ_arrow T1 T2) c)) as [[Γ'' [T1' [T2' []]]]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ'', (typ_intersection T1 T1'), (typ_union T2 T2'). split.
        -- eapply a_wl_mul_red__step; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           assert (Hac1: apply_cont (cont_unioninfabs (typ_arrow T1 T2) c) (typ_arrow T1' T2') (work_unioninfabs (typ_arrow T1 T2) (typ_arrow T1' T2') c)).
            { apply applycont__unioninfabs. }
            eapply a_wl_mul_red_trans; eauto.
        -- simpl in *. lia.
      * right. intros. dependent destruction H2. admit. (* IMPORTANT *)
    + right. intros. dependent destruction H0.
      apply H in H0. contradiction.
  - destruct (IHHlct1 Γ c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_infabs A1 c))); eauto.
    + destruct (IHHlct2 Γ c) as [[Γ' [T1 [T2 []]]]| ]; auto.
      * left. exists Γ', T1, T2. split; auto.
        eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_infabs A2 c))); eauto.
      * right. intros. dependent destruction H1.
        dependent destruction H1.
        -- apply H in H2. contradiction.
        -- apply H0 in H2. contradiction.
Admitted.

Theorem decidablity_lemma_infabs : forall A, lc_typ A ->
  forall Γ c, a_wf_wl Γ ->
  (exists Γ' T1 T2,
    a_wl_mul_red (aworklist_conswork Γ (work_infabs A c))
                 (aworklist_conswork Γ' (work_apply c (typ_arrow T1 T2))) /\
    judge_size_wl Γ' <= judge_size_wl Γ) \/
  (a_wl_mul_red (aworklist_conswork Γ (work_infabs A c)) aworklist_empty -> False).
Proof.
  intros A Hlct. dependent induction Hlct; intros Γ c Hwfl.
  - right. intros. dependent destruction H. inversion H.
  - right. intros. dependent destruction H. inversion H. 
  - left. exists Γ, typ_top, typ_bot.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - left. admit. (* I need to write the right small-step version first. *)
  - left. exists Γ, A1, A2.
    split; auto. eapply a_wl_mul_red__step; eauto.
  - inst_cofinites_by (dom (awl_to_aenv Γ)).
    destruct (H0 x (aworklist_constvar Γ x (abind_bound typ_bot typ_top)) c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step; eauto.
    + right. intros. dependent destruction H2.
      dependent destruction H2.
      admit. (* rename *)
  - destruct (IHHlct1 Γ (cont_infabsunion A2 c)) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + assert (Hac: apply_cont (cont_infabsunion A2 c) (typ_arrow T1 T2) (work_infabsunion (typ_arrow T1 T2) A2 c)).
        { apply applycont__infabsunion. }
      assert (Hred: a_wl_mul_red (aworklist_conswork Γ' (work_apply (cont_infabsunion A2 c) (typ_arrow T1 T2)))
                                 (aworklist_conswork Γ' (work_infabs A2 ((cont_unioninfabs (typ_arrow T1 T2) c))))).
        { eapply a_wl_mul_red__step; eauto. }
      destruct (IHHlct2 Γ' (cont_unioninfabs (typ_arrow T1 T2) c)) as [[Γ'' [T1' [T2' []]]]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ'', (typ_intersection T1 T1'), (typ_union T2 T2'). split.
        -- eapply a_wl_mul_red__step; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           assert (Hac1: apply_cont (cont_unioninfabs (typ_arrow T1 T2) c) (typ_arrow T1' T2') (work_unioninfabs (typ_arrow T1 T2) (typ_arrow T1' T2') c)).
            { apply applycont__unioninfabs. }
            eapply a_wl_mul_red_trans; eauto.
        -- simpl in *. lia.
      * right. intros. dependent destruction H2.
        dependent destruction H2.
        dependent destruction H3. admit. (* IMPORTANT *)
    + right. intros. dependent destruction H0.
      dependent destruction H0. apply H in H1. contradiction.
  - destruct (IHHlct1 Γ c) as [[Γ' [T1 [T2 []]]]| ]; auto.
    + left. exists Γ', T1, T2. split; auto.
      eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_infabs A1 c))); eauto.
    + destruct (IHHlct2 Γ c) as [[Γ' [T1 [T2 []]]]| ]; auto.
      * left. exists Γ', T1, T2. split; auto.
        eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_infabs A2 c))); eauto.
      * right. intros. dependent destruction H1.
        dependent destruction H1.
        -- apply H in H2. contradiction.
        -- apply H0 in H2. contradiction.
Admitted.


Theorem decidablity_lemma_inftapp : forall A, lc_typ A ->
  forall Γ B c, a_wf_wl Γ ->
  (exists Γ' T,
    a_wl_mul_red (aworklist_conswork Γ (work_inftapp A B c))
                 (aworklist_conswork Γ' (work_apply c T)) /\
    judge_size_wl Γ' <= judge_size_wl Γ) \/
  (a_wl_mul_red (aworklist_conswork Γ (work_inftapp A B c)) aworklist_empty -> False).
Proof.
  intros A Hlct. dependent induction Hlct; intros Γ B c Hwfl.
  - right. intros. dependent destruction H. inversion H.
  - right. intros. dependent destruction H. inversion H.
  - left. exists Γ, typ_bot. split; auto.
    eapply a_wl_mul_red__step; eauto.
  - right. intros. dependent destruction H. inversion H.
  - right. intros. dependent destruction H. inversion H.
  - left. exists Γ, (A ^^ᵈ B). split; auto.
    eapply a_wl_mul_red__step; eauto.
  - destruct (IHHlct1 Γ B (cont_inftappunion A2 B c)) as [[Γ' [T []]]| ]; auto.
    + assert (Hac: apply_cont (cont_inftappunion A2 B c) T (work_inftappunion T A2 B c)).
        { apply applycont__tappunion. }
      assert (Hred: a_wl_mul_red (aworklist_conswork Γ' (work_apply (cont_inftappunion A2 B c) T))
                                 (aworklist_conswork Γ' (work_inftapp A2 B  (  (cont_unioninftapp T c)  ) ))).
        { eapply a_wl_mul_red__step; eauto. }
      destruct (IHHlct2 Γ' B (cont_unioninftapp T c)) as [[Γ'' [T' []]]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ'', (typ_union T T'). split.
        -- eapply a_wl_mul_red__step; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           eapply a_wl_mul_red_trans; eauto.
           assert (Hac1: apply_cont (cont_unioninftapp T c) T' (work_unioninftapp T T' c)).
             { apply applycont__unioninftapp. }
           eapply a_wl_mul_red_trans; eauto.
        -- lia.
      * right. intros. dependent destruction H2.
        dependent destruction H2.
        dependent destruction H3. admit. (* IMPORTANT *) 
    + right. intros. dependent destruction H0.
      dependent destruction H0.
      apply H in H1. contradiction.
  - destruct (IHHlct1 Γ B c) as [[Γ' [T []]]| ]; auto.
    + left. exists Γ', T. split; auto.
      eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_inftapp A1 B c))); eauto.
    + destruct (IHHlct2 Γ B c) as [[Γ' [T []]]| ]; auto.
      * left. exists Γ', T. split; auto.
        eapply a_wl_mul_red__step with (Γ2 := (aworklist_conswork Γ (work_inftapp A2 B c))); eauto.
      * right. intros. dependent destruction H1.
        dependent destruction H1.
        -- apply H in H2. contradiction.
        -- apply H0 in H2. contradiction.
Admitted. 

Theorem decidablity_lemma_infabs : forall A, lc_typ A ->
  forall Γ c, a_wf_wl Γ ->
  (exists Γ',
    a_wl_mul_red (aworklist_conswork Γ (work_infabs A c)) Γ' /\
    judge_size_wl Γ' < judge_size_wl (aworklist_conswork Γ (work_infabs A c))) \/
  (a_wl_mul_red (aworklist_conswork Γ (work_infabs A c)) aworklist_empty -> False).
Proof.
  intros A Hlct. dependent induction Hlct; intros Γ c Hwfl.
  - right. intros. dependent destruction H. inversion H.
  - right. intros. dependent destruction H. inversion H. 
  - left. exists (aworklist_conswork Γ (work_apply c (typ_arrow typ_top typ_bot))).
    split; auto. eapply a_wl_mul_red__step; eauto.
  - left. admit. (* I need to write the right small-step version first. *)
  - left. exists (aworklist_conswork Γ (work_apply c (typ_arrow A1 A2))).
    split; auto. eapply a_wl_mul_red__step; eauto.
  - inst_cofinites_by (dom (awl_to_aenv Γ)).
    destruct (H0 x (aworklist_constvar Γ x (abind_bound typ_bot typ_top)) c) as [[Γ' []]| ]; auto.
    + left. exists Γ'. split; auto.
      eapply a_wl_mul_red__step; eauto.
    + right. intros. dependent destruction H2.
      dependent destruction H2.
      admit. (* rename *)
  - destruct (IHHlct1 Γ (cont_infabsunion A2 c)) as [[Γ' []]| ]; auto.
    dependent destruction H.
    + apply Nat.le_neq in H0. destruct H0. destruct H0. auto.
    + simpl in *.
      destruct (IHHlct2 Γ' c) as [[Γ'' []]| ]; auto.
      * admit. (* wf *)
      * left. exists Γ''. split.
        -- eapply a_wl_mul_red__step; eauto.
        eapply a_wl_mul_red__step; eauto.
    + left. exists Γ'. split; auto.
      * eapply a_wl_mul_red__step; eauto.
      * simpl in *.

  inst_cofinites_by Γ.
    destruct (H1 (aworklist_constvar Γ x abind_tvar_empty)); auto.
    + destruct H2 as [Γ' [? ?]]. left.
      exists (aworklist_conswork Γ' (work_infabs (open_typ_wrt_typ A (typ_var_f x)) c)).
      split.
      * eapply a_wl_mul_red__step; eauto.
    apply a_wf_wl__constvar.
    + left. exists Γ'. split. auto.
      eapply a_wl_mul_red__step; eauto.
  - right. intros. inversion H.
  - 
    exists (aworklist_conswork Γ (work_apply (cont_infabs c) typ_unit)).
    split.
    + apply a_wl_mul_red_conswork.
      apply a_wl_mul_red_infabs.
    + simpl. lia.
  apply a_wl_mul_red_conswork.
  apply a_wl_mul_red_infabs.
  
Qed.

