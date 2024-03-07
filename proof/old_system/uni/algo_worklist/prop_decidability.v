Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Coq.micromega.Lia.

Require Import uni.notations.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import ln_utils.

Fixpoint iu_size (A : typ) : nat :=
  match A with
  | typ_unit => 0
  | typ_bot => 0
  | typ_top => 0
  | typ_var_f _ => 0
  | typ_var_b _ => 0
  | typ_arrow A1 A2 => iu_size A1 + iu_size A2
  | typ_all A => iu_size A
  | typ_union A1 A2 => 2 + iu_size A1 + iu_size A2
  | typ_intersection A1 A2 => 2 + iu_size A1 + iu_size A2
  end.

Fixpoint exp_size (e : exp) : nat :=
  match e with
  | exp_unit => 1
  | exp_var_b _ => 1
  | exp_var_f _ => 1
  | exp_abs e => 1 + exp_size e
  | exp_app e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_tabs b => 1 + body_size b
  | exp_tapp e _ => 1 + exp_size e
  | exp_anno e A => 1 + exp_size e * (1 + iu_size A)
  end
with body_size (b : body) : nat :=
  match b with 
  | body_anno e A => exp_size e * (1 + iu_size A)
  end.

Lemma exp_size_gt_0 : forall e,
  exp_size e > 0.
Proof.
  induction e; simpl; try lia.
Qed.

Fixpoint exp_size_cont (c : cont) : nat :=
  match c with
  | cont_infabs c => exp_size_cont c
  | cont_infabsunion _ c => exp_size_cont c
  | cont_infapp e c => exp_size e + exp_size_cont c
  | cont_inftapp _ c => exp_size_cont c
  | cont_inftappunion _ _ c => exp_size_cont c
  | cont_unioninftapp _ c => exp_size_cont c
  | cont_unioninfabs _ c => exp_size_cont c
  | cont_sub A => 0
  end.

Definition exp_size_work (w : work) : nat :=
  match w with
  | work_infer e c => exp_size e + exp_size_cont c
  | work_check e A => exp_size e * (1 + iu_size A)
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
  | cont_infabs c => judge_size_cont c
  | cont_infabsunion _ c => judge_size_cont c
  | cont_infapp _ c => 4 + judge_size_cont c
  | cont_inftapp _ c => judge_size_cont c
  | cont_inftappunion _ _ c => judge_size_cont c
  | cont_unioninftapp _ c => judge_size_cont c
  | cont_unioninfabs _ c => judge_size_cont c
  | cont_sub A => 0
  end.

Definition judge_size_work (w : work) : nat :=
  match w with
  | work_infer _ c => 2 + judge_size_cont c
  | work_check _ _ => 3
  | work_infabs _ c => judge_size_cont c
  | work_infabsunion _ _ c => judge_size_cont c
  | work_infapp _ _ c => 4 + judge_size_cont c
  | work_inftapp _ _ c => judge_size_cont c
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ c => judge_size_cont c
  | work_unioninftapp _ _ c => judge_size_cont c
  | work_unioninfabs _ _ c => judge_size_cont c
  | work_apply c _ => 1 + judge_size_cont c
  end.

Fixpoint judge_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => judge_size_wl Γ'
  | aworklist_consvar Γ' _ _ => judge_size_wl Γ'
  | aworklist_conswork Γ' w => judge_size_work w + judge_size_wl Γ'
  end.

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
  | split_size_arrow_s : forall Γ A1 A2 n1 n2 n,
      ~ a_mono_typ (awl_to_aenv Γ) (typ_arrow A1 A2) ->
      split_size Γ A1 n1 -> split_size Γ A2 n2 ->
      n = n1 + n2 ->
      split_size Γ (typ_arrow A1 A2) (S n)
  | split_size_all : forall L Γ A n,
      ( forall X , X \notin L ->
        split_size (aworklist_constvar Γ X abind_stvar_empty) (open_typ_wrt_typ A (typ_var_f X)) n) ->
      split_size Γ (typ_all A) n
  | split_size_union : forall Γ A1 A2 n1 n2 n,
      split_size Γ A1 n1 ->
      split_size Γ A2 n2 ->
      n = n1 + n2 ->
      split_size Γ (typ_union A1 A2) (S n)
  | split_size_intersection : forall Γ A1 A2 n1 n2 n,
      split_size Γ A1 n1 ->
      split_size Γ A2 n2 ->
      n = n1 + n2 ->
      split_size Γ (typ_intersection A1 A2) (S n).

Theorem split_size_total : forall Γ A,
  a_wf_typ (awl_to_aenv Γ) A -> exists n, split_size Γ A n.
Admitted.

Theorem split_size_det : forall Γ A n1 n2,
  split_size Γ A n1 -> split_size Γ A n2 -> n1 = n2.
Admitted.

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
  | split_size_work_sub : forall Γ A1 A2 n1 n2 n,
      split_size Γ A1 n1 ->
      split_size Γ A2 n2 ->
      n = n1 + n2 ->
      split_size_work Γ (work_sub A1 A2) n
  | split_size_work_inftappunion : forall Γ A1 A2 A3 c,
      split_size_work Γ (work_inftappunion A1 A2 A3 c) 0
  | split_size_work_unioninftapp : forall Γ A1 A2 c,
      split_size_work Γ (work_unioninftapp A1 A2 c) 0
  | split_size_work_unioninfabs : forall Γ A1 A2 c,
      split_size_work Γ (work_unioninfabs A1 A2 c) 0
  | split_size_work_apply : forall Γ c A,
      split_size_work Γ (work_apply c A) 0.

Theorem split_size_work_total : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w -> exists n, split_size_work Γ w n.
Admitted.

Theorem split_size_work_det : forall Γ w n1 n2,
  split_size_work Γ w n1 -> split_size_work Γ w n2 -> n1 = n2.
Admitted.

Inductive split_size_wl : aworklist -> nat -> Prop :=
  | split_size_wl_empty : split_size_wl aworklist_empty 0
  | split_size_wl_constvar : forall Γ X A n,
      split_size_wl Γ n ->
      split_size_wl (aworklist_constvar Γ X A) n
  | split_size_wl_consvar : forall Γ X A n,
      split_size_wl Γ n ->
      split_size_wl (aworklist_consvar Γ X A) n
  | split_size_wl_conswork : forall Γ w m n k,
      split_size_work Γ w m ->
      split_size_wl Γ n ->
      k = m + n ->
      split_size_wl (aworklist_conswork Γ w) k.

Theorem split_size_wl_det : forall Γ n1 n2,
  split_size_wl Γ n1 -> split_size_wl Γ n2 -> n1 = n2.
Admitted.

Theorem split_size_wl_total : forall Γ,
  a_wf_wl Γ -> exists n, split_size_wl Γ n.
Admitted.

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

Inductive measp : aworklist -> typ -> nat -> Prop :=
  | measp_typ : forall Γ A m n,
      split_size Γ A m -> 
      n = 3 * m + all_size A ->
      measp Γ A n.

Theorem measp_total : forall Γ A,
  a_wf_typ (awl_to_aenv Γ) A -> exists n, measp Γ A n.
Admitted.

Theorem measp_det : forall Γ A n1 n2,
  measp Γ A n1 -> measp Γ A n2 -> n1 = n2.
Admitted.

Inductive measp_work : aworklist -> work -> nat -> Prop :=
  | measp_work_infer : forall Γ e c,
      measp_work Γ (work_infer e c) 0
  | measp_work_check : forall Γ e A,
      measp_work Γ (work_check e A) 0
  | measp_work_infabs : forall Γ A c,
      measp_work Γ (work_infabs A c) 0
  | measp_work_infabsunion : forall Γ A1 A2 c,
      measp_work Γ (work_infabsunion A1 A2 c) 0
  | measp_work_infapp : forall Γ A e c,
      measp_work Γ (work_infapp A e c) 0
  | measp_work_inftapp : forall Γ A1 A2 c,
      measp_work Γ (work_inftapp A1 A2 c) 0
  | measp_work_sub : forall Γ A1 A2 n1 n2 n,
      measp Γ A1 n1 -> measp Γ A2 n2 ->
      n = n1 * (1 + iu_size A2) + n2 * (1 + iu_size A1) ->
      measp_work Γ (work_sub A1 A2) n
  | measp_work_inftappunion : forall Γ A1 A2 A3 c,
      measp_work Γ (work_inftappunion A1 A2 A3 c) 0
  | measp_work_unioninftapp : forall Γ A1 A2 c,
      measp_work Γ (work_unioninftapp A1 A2 c) 0
  | measp_work_unioninfabs : forall Γ A1 A2 c,
      measp_work Γ (work_unioninfabs A1 A2 c) 0
  | measp_work_apply : forall Γ c A,
      measp_work Γ (work_apply c A) 0.

Theorem measp_work_total : forall Γ w,
  a_wf_work (awl_to_aenv Γ) w -> exists n, measp_work Γ w n.
Admitted.

Theorem measp_work_det : forall Γ w n1 n2,
  measp_work Γ w n1 -> measp_work Γ w n2 -> n1 = n2.
Admitted.

Inductive measp_wl : aworklist -> nat -> Prop :=
  | measp_wl_empty : measp_wl aworklist_empty 0
  | measp_wl_consevar : forall Γ X n,
      measp_wl Γ n ->
      measp_wl (aworklist_constvar Γ X abind_etvar_empty) (S n)
  | measp_wl_constvar : forall Γ X n,
      measp_wl Γ n ->
      measp_wl (aworklist_constvar Γ X abind_tvar_empty) n
  | measp_wl_conssvar : forall Γ X n,
      measp_wl Γ n ->
      measp_wl (aworklist_constvar Γ X abind_stvar_empty) n
  | measp_wl_consvar : forall Γ X A n,
      measp_wl Γ n ->
      measp_wl (aworklist_consvar Γ X A) n
  | measp_wl_conswork : forall Γ w m n k,
      measp_work Γ w m ->
      measp_wl Γ n ->
      k = m + n ->
      measp_wl (aworklist_conswork Γ w) k.

#[local]Hint Constructors split_size split_size_work split_size_wl : core.
#[local]Hint Constructors measp measp_work measp_wl : core.
#[local]Hint Constructors a_wl_red a_wf_wl : core.

Theorem measp_wl_total : forall Γ,
  a_wf_wl Γ -> exists n, measp_wl Γ n.
Admitted.

Theorem measp_wl_det : forall Γ n1 n2,
  measp_wl Γ n1 -> measp_wl Γ n2 -> n1 = n2.
Admitted.

Lemma measp_mono' : forall Γ A n,
  measp Γ A n -> a_mono_typ (awl_to_aenv Γ) A -> n = 0.
Admitted.

Lemma measp_mono : forall Γ A,
  a_mono_typ (awl_to_aenv Γ) A -> measp Γ A 0.
Proof.
  intros Γ A Hmono.
  eapply a_mono_typ_wf in Hmono as H.
  eapply measp_total in H.
  dependent destruction H.
  eapply measp_mono' in H as H'; eauto.
  subst. eauto.
Qed.

Lemma measp_top' : forall Γ n,
  measp Γ typ_top n -> n = 0.
Proof.
  intros. dependent destruction H.
  dependent destruction H. simpl. lia.
Qed.

Lemma measp_bot : forall Γ n,
  measp Γ typ_bot n -> n = 0.
Proof.
  intros. dependent destruction H.
  dependent destruction H. simpl. lia.
Qed.

Fixpoint weight (A : typ) : nat :=
  match A with
  | typ_unit => 1
  | typ_bot => 1
  | typ_top => 1
  | typ_var_f _ => 1
  | typ_var_b _ => 1
  | typ_arrow A1 A2 => 1 + weight A1 + weight A2
  | typ_all A => 2 + weight A
  | typ_union A1 A2 => 1 + weight A1 + weight A2
  | typ_intersection A1 A2 => 1 + weight A1 + weight A2
  end.

Lemma weight_gt_0 : forall A,
  weight A > 0.
Proof.
  induction A; simpl; lia.
Qed.

Definition weight_work (w : work) : nat :=
  match w with
  | work_sub A1 A2 => weight A1 * (1 + iu_size A2) + weight A2 * (1 + iu_size A1)
  | _ => 0
  end.

Fixpoint weight_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => 1 + weight_wl Γ'
  | aworklist_consvar Γ' _ _ => 1 + weight_wl Γ'
  | aworklist_conswork Γ' w => weight_work w + weight_wl Γ'
  end.

#[local]Hint Constructors a_wl_red a_wf_wl : core.

Fixpoint infabs_depth (A : typ) : nat :=
  match A with
  | typ_arrow _ _ => 1
  | typ_bot => 2
  | typ_all A => 1 + infabs_depth A
  | typ_intersection A1 A2 => 1 + infabs_depth A1 + infabs_depth A2
  | typ_union A1 A2 => 2 + infabs_depth A1 + infabs_depth A2
  | typ_var_f _ => 2
  | typ_var_b _ => 2
  | _ => 0
  end.

Fixpoint infabs_depth_cont (c : cont) : nat :=
  match c with
  | cont_infabs c => 1 + infabs_depth_cont c
  | cont_infabsunion A c => 1 + infabs_depth A + infabs_depth_cont c
  | cont_unioninfabs _ c => 1 + infabs_depth_cont c
  | _ => 0
  end.

Definition infabs_depth_work (w : work) : nat :=
  match w with
  | work_infabs A c => infabs_depth A + infabs_depth_cont c
  | work_infabsunion _ A c => 1 + infabs_depth A + infabs_depth_cont c
  | work_unioninfabs _ _ c => 1 + infabs_depth_cont c
  | _ => 0
  end.

Fixpoint infabs_depth_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => infabs_depth_wl Γ'
  | aworklist_consvar Γ' _ _ => infabs_depth_wl Γ'
  | aworklist_conswork Γ' w => infabs_depth_work w + infabs_depth_wl Γ'
  end.

#[local]Hint Unfold infabs_depth infabs_depth_work infabs_depth_wl : core.

Fixpoint inftapp_all_size (A : typ) : nat :=
  match A with
  | typ_all A => 1 + inftapp_all_size A
  | typ_union A1 A2 => inftapp_all_size A1 + inftapp_all_size A2
  | typ_intersection A1 A2 => inftapp_all_size A1 + inftapp_all_size A2
  | _ => 0
  end.

Definition inftapp_all_size_work (w : work) : nat :=
  match w with
  | work_inftapp A _ _ => inftapp_all_size A
  | _ => 0
  end.

Fixpoint inftapp_all_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => inftapp_all_size_wl Γ'
  | aworklist_consvar Γ' _ _ => inftapp_all_size_wl Γ'
  | aworklist_conswork Γ' w => inftapp_all_size_work w + inftapp_all_size_wl Γ'
  end.

Fixpoint inftapp_depth (A : typ) : nat :=
  match A with
  | typ_all A => 1 + inftapp_depth A
  | typ_union A1 A2 => 1 + inftapp_depth A1 + inftapp_depth A2
  | typ_intersection A1 A2 => 1 + inftapp_depth A1 + inftapp_depth A2
  | typ_var_b _ => 1
  | _ => 0
  end.

Fixpoint inftapp_depth_cont_tail_rec (c : cont) (ans : nat) : nat :=
  match c with
  | cont_inftapp B c        => inftapp_depth_cont_tail_rec c ((2 + inftapp_depth B) * ans)
  | cont_inftappunion A B c => inftapp_depth_cont_tail_rec c ((inftapp_depth A) * (2 + inftapp_depth B) + 1 + ans)
  | cont_infabs c           => inftapp_depth_cont_tail_rec c ans
  | cont_infabsunion _ c    => inftapp_depth_cont_tail_rec c ans
  | cont_infapp _ c         => inftapp_depth_cont_tail_rec c ans
  | cont_unioninftapp A c   => inftapp_depth_cont_tail_rec c (1 + inftapp_depth A + ans)
  | cont_unioninfabs _ c    => inftapp_depth_cont_tail_rec c ans
  | _                       => ans
  end.

Definition inftapp_depth_work (w : work) : nat :=
  match w with
  | work_inftapp A B c => inftapp_depth_cont_tail_rec (cont_inftapp B c) (inftapp_depth A)
  | work_inftappunion A1 A2 B c => inftapp_depth_cont_tail_rec c (inftapp_depth A1 + (inftapp_depth A2) * (2 + inftapp_depth B) + 1)
  | work_infer _ c => inftapp_depth_cont_tail_rec c 0
  | work_infabs _ c => inftapp_depth_cont_tail_rec c 0
  | work_infabsunion _ _ c => inftapp_depth_cont_tail_rec c 0
  | work_infapp _ _ c => inftapp_depth_cont_tail_rec c 0
  | work_unioninftapp A1 A2 c => inftapp_depth_cont_tail_rec c (1 + inftapp_depth A1 + inftapp_depth A2)
  | work_unioninfabs _ _ c => inftapp_depth_cont_tail_rec c 0
  | _ => 0
  end.

Fixpoint inftapp_depth_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => inftapp_depth_wl Γ'
  | aworklist_consvar Γ' _ _ => inftapp_depth_wl Γ'
  | aworklist_conswork Γ' w => inftapp_depth_work w + inftapp_depth_wl Γ'
  end.

#[local] Hint Unfold inftapp_depth_cont_tail_rec inftapp_depth inftapp_depth_work inftapp_depth_wl : core.

Fixpoint infabs_judge_size_cont (c : cont) : nat :=
  match c with
  | cont_infabs c => 1 + infabs_judge_size_cont c
  | cont_infabsunion _ c => 3 + infabs_judge_size_cont c
  | cont_infapp _ c => infabs_judge_size_cont c
  | cont_inftapp _ c => infabs_judge_size_cont c
  | cont_inftappunion _ _ c => infabs_judge_size_cont c
  | cont_unioninftapp _ c => infabs_judge_size_cont c
  | cont_unioninfabs _ c => 1 + infabs_judge_size_cont c
  | cont_sub A => 0
  end.

Definition infabs_judge_size_work (w : work) : nat :=
  match w with
  | work_infer _ c => infabs_judge_size_cont c
  | work_check _ _ => 0
  | work_infabs _ c => 1 + infabs_judge_size_cont c
  | work_infabsunion _ _ c => 3 + infabs_judge_size_cont c
  | work_infapp _ _ c => infabs_judge_size_cont c
  | work_inftapp _ _ c => infabs_judge_size_cont c
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ c => infabs_judge_size_cont c
  | work_unioninftapp _ _ c => infabs_judge_size_cont c
  | work_unioninfabs _ _ c => 1 + infabs_judge_size_cont c
  | work_apply c _ => infabs_judge_size_cont c
  end.

Fixpoint infabs_judge_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => infabs_judge_size_wl Γ'
  | aworklist_consvar Γ' _ _ => infabs_judge_size_wl Γ'
  | aworklist_conswork Γ' w => infabs_judge_size_work w + infabs_judge_size_wl Γ'
  end.

Fixpoint inftapp_judge_size_cont (c : cont) : nat :=
  match c with
  | cont_infabs c => inftapp_judge_size_cont c
  | cont_infabsunion _ c => inftapp_judge_size_cont c
  | cont_infapp _ c => inftapp_judge_size_cont c
  | cont_inftapp _ c => 1 + inftapp_judge_size_cont c
  | cont_inftappunion _ _ c => 3 + inftapp_judge_size_cont c
  | cont_unioninftapp _ c => 1 + inftapp_judge_size_cont c
  | cont_unioninfabs _ c => inftapp_judge_size_cont c
  | cont_sub A => 0
  end.

Definition inftapp_judge_size_work (w : work) : nat :=
  match w with
  | work_infer _ c => inftapp_judge_size_cont c
  | work_check _ _ => 0
  | work_infabs _ c => inftapp_judge_size_cont c
  | work_infabsunion _ _ c => inftapp_judge_size_cont c
  | work_infapp _ _ c => inftapp_judge_size_cont c
  | work_inftapp _ _ c => 1 + inftapp_judge_size_cont c
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ c => 3 + inftapp_judge_size_cont c
  | work_unioninftapp _ _ c => 1 + inftapp_judge_size_cont c
  | work_unioninfabs _ _ c => inftapp_judge_size_cont c
  | work_apply c _ => inftapp_judge_size_cont c
  end.

Fixpoint inftapp_judge_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => inftapp_judge_size_wl Γ'
  | aworklist_consvar Γ' _ _ => inftapp_judge_size_wl Γ'
  | aworklist_conswork Γ' w => inftapp_judge_size_work w + inftapp_judge_size_wl Γ'
  end.

Lemma abind_etvar_tvar_false : forall Γ X,
  a_wf_wl Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  binds X abind_tvar_empty (awl_to_aenv Γ) -> False.
Admitted.

Lemma abind_etvar_stvar_false : forall Γ X,
  a_wf_wl Γ ->
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  binds X abind_stvar_empty (awl_to_aenv Γ) -> False.
Admitted.

Lemma abind_tvar_stvar_false : forall Γ X,
  a_wf_wl Γ ->
  binds X abind_tvar_empty (awl_to_aenv Γ) ->
  binds X abind_stvar_empty (awl_to_aenv Γ) -> False.
Admitted.

Lemma iu_size_mono : forall Γ A,
  a_mono_typ Γ A -> iu_size A = 0.
Proof.
  intros Γ A Hmono.
  induction Hmono; simpl; eauto; try lia.
Qed.

Lemma iu_size_subst_mono : forall Γ A X A0,
  a_mono_typ Γ A ->
  iu_size (subst_tvar_in_typ A X A0) = iu_size A0.
Proof.
  intros Γ A X A0 Hmono.
  induction A0; simpl; auto.
  destruct (eq_dec X0 X); subst; simpl; eauto.
  eapply iu_size_mono; eauto.
Qed.

Lemma exp_size_wl_awl_app : forall Γ1 Γ2,
  exp_size_wl (awl_app Γ1 Γ2) = exp_size_wl Γ1 + exp_size_wl Γ2.
Proof.
  intros Γ1.
  induction Γ1; simpl; auto;
    try solve [intros; rewrite IHΓ1; simpl; lia].
Qed.

Lemma exp_size_subst_tvar_in_exp_mono : forall Γ A X e,
  a_mono_typ Γ A ->
  exp_size (subst_tvar_in_exp A X e) = exp_size e
with body_size_subst_tvar_in_body_mono : forall Γ A X b,
  a_mono_typ Γ A ->
  body_size (subst_tvar_in_body A X b) = body_size b.
Proof.
  - intros Γ A X e Hmono.
  induction e; simpl; eauto.
  erewrite iu_size_subst_mono; eauto.
  - intros. destruct b. simpl. 
  erewrite iu_size_subst_mono; eauto. 
Qed.

Lemma exp_size_cont_subst_tvar_in_cont_mono : forall Γ X A c,
  a_mono_typ Γ A ->
  exp_size_cont (subst_tvar_in_cont A X c) = exp_size_cont c.
Proof.
  intros Γ X A c Hmono.
  induction c; simpl; eauto.
  erewrite exp_size_subst_tvar_in_exp_mono; eauto.
Qed.

Lemma exp_size_work_subst_tvar_in_work_mono : forall Γ X A w,
  a_mono_typ Γ A ->
  exp_size_work (subst_tvar_in_work A X w) = exp_size_work w.
Proof.
  intros Γ X A w Hmono.
  induction w; intros; simpl;
    try erewrite exp_size_subst_tvar_in_exp_mono;
    try erewrite exp_size_cont_subst_tvar_in_cont_mono;
    try erewrite iu_size_subst_mono; eauto.
Qed.

Lemma exp_size_wl_subst_tvar_in_aworklist_mono : forall Γ Γ' X A,
  a_mono_typ Γ' A ->
  exp_size_wl (subst_tvar_in_aworklist A X Γ) = exp_size_wl Γ.
Proof.
  intros Γ.
  induction Γ; intros; simpl in *;
    try erewrite exp_size_work_subst_tvar_in_work_mono; eauto.
Qed. 

Lemma exp_size_wl_aworklist_subst : forall Γ X A E Γ1 Γ2,
  aworklist_subst Γ X A E Γ1 Γ2 ->
  exp_size_wl Γ = exp_size_wl Γ1 + exp_size_wl Γ2.
Proof.
  intros Γ X A E Γ1 Γ2 Hsubst.
  induction Hsubst; simpl; auto; try lia.
Qed.

Lemma exp_size_wl_etvar_list : forall E,
  exp_size_wl (etvar_list_to_awl E) = 0.
Proof.
  induction E; simpl; auto.
Qed.

Lemma judge_size_wl_awl_app : forall Γ1 Γ2,
  judge_size_wl (awl_app Γ1 Γ2) = judge_size_wl Γ1 + judge_size_wl Γ2.
Proof.
  intros Γ1.
  induction Γ1; simpl; auto;
    try solve [intros; rewrite IHΓ1; simpl; lia].
Qed.

Lemma judge_size_cont_subst_tvar_in_cont : forall X A c,
  judge_size_cont (subst_tvar_in_cont A X c) = judge_size_cont c.
Proof.
  intros X A c.
  induction c; simpl; eauto.
Qed.

Lemma judge_size_work_subst_tvar_in_work : forall X A w,
  judge_size_work (subst_tvar_in_work A X w) = judge_size_work w.
Proof.
  intros X A w.
  induction w; intros; simpl;
    try erewrite judge_size_cont_subst_tvar_in_cont; eauto.
Qed.

Lemma judge_size_wl_subst_tvar_in_aworklist : forall Γ X A,
  judge_size_wl (subst_tvar_in_aworklist A X Γ) = judge_size_wl Γ.
Proof.
  intros Γ.
  induction Γ; intros; simpl in *;
    try erewrite judge_size_work_subst_tvar_in_work; eauto.
Qed. 

Lemma judge_size_wl_aworklist_subst : forall Γ X A E Γ1 Γ2,
  aworklist_subst Γ X A E Γ1 Γ2 ->
  judge_size_wl Γ = judge_size_wl Γ1 + judge_size_wl Γ2.
Proof.
  intros Γ X A E Γ1 Γ2 Hsubst.
  induction Hsubst; simpl; auto; try lia.
Qed.

Lemma judge_size_wl_etvar_list : forall E,
  judge_size_wl (etvar_list_to_awl E) = 0.
Proof.
  induction E; simpl; auto.
Qed.

Lemma measp_wl_aworklist_subst : forall Γ X A E Γ1 Γ2 n,
  aworklist_subst Γ X A E Γ1 Γ2 ->
  measp_wl Γ n ->
  measp_wl
    (awl_app (subst_tvar_in_aworklist A X Γ2)
      (awl_app (etvar_list_to_awl E) Γ1)) n.
Proof.
  intros Γ X A E Γ1 Γ2 n Hsubst Hmeas.
  induction Hsubst; simpl.
  (* rev? *)
Abort.

Lemma apply_cont_det : forall c A w1 w2,
  apply_cont c A w1 -> apply_cont c A w2 -> w1 = w2.
Proof.
  intros c A w1 w2 Happly1 Happly2.
  induction Happly1; dependent destruction Happly2; eauto.
Qed.

Lemma apply_cont_dec : forall c A,
  (exists w, apply_cont c A w) \/ ((exists w, apply_cont c A w) -> False).
Proof.
  intros c A.
  destruct c; eauto using apply_cont.
  - destruct A;
      try solve [right; intros Hcontra; dependent destruction Hcontra; dependent destruction H];
      eauto using apply_cont.
  - destruct A;
      try solve [right; intros Hcontra; dependent destruction Hcontra; dependent destruction H].
    destruct A2;
      try solve [right; intros Hcontra; dependent destruction Hcontra; dependent destruction H];
      eauto using apply_cont.
Qed.

Lemma apply_cont_exp_size : forall c A w,
  apply_cont c A w -> exp_size_work w = exp_size_cont c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_cont_judge_size : forall c A w,
  apply_cont c A w -> judge_size_work w = judge_size_cont c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_cont_infabs_depth_arr : forall c A B w,
  apply_cont c (typ_arrow A B) w -> infabs_depth_work w <= infabs_depth_cont c.
Proof.
  intros c A B w Happly.
  dependent destruction Happly; simpl; eauto.
Qed.

Lemma inftapp_depth_cont_tail_rec_le : forall c ans1 ans2,
  ans1 <= ans2 ->
  inftapp_depth_cont_tail_rec c ans1 <= inftapp_depth_cont_tail_rec c ans2.
Proof.
  intros c.
  induction c; intros; simpl; eauto; try eapply IHc; try lia.
  assert (inftapp_depth A * ans1 <= inftapp_depth A * ans2).
  { eapply mult_le_compat; eauto. } lia.
Qed.

Lemma inftapp_depth_cont_tail_rec_lt : forall c ans1 ans2,
  ans1 < ans2 ->
  inftapp_depth_cont_tail_rec c ans1 < inftapp_depth_cont_tail_rec c ans2.
Proof.
  intros c.
  induction c; intros; simpl; eauto; try eapply IHc; try lia.
  assert (inftapp_depth A * ans1 <= inftapp_depth A * ans2).
  { eapply mult_le_compat; eauto. lia. } lia.
Qed.

Lemma apply_cont_inftapp_depth_arr : forall c A B w,
  apply_cont c (typ_arrow A B) w -> inftapp_depth_work w <= inftapp_depth_cont_tail_rec c 0.
Proof.
  intros c A B w Happly.
  dependent destruction Happly; try solve [simpl; eauto].
  simpl. eapply inftapp_depth_cont_tail_rec_le; lia.
Qed.

Lemma apply_cont_inftapp_all_size_arr : forall c A B w,
  apply_cont c (typ_arrow A B) w -> inftapp_all_size_work w = 0.
Proof.
  intros c A B w Happly.
  dependent destruction Happly; simpl; eauto.
Qed.

Lemma apply_cont_inftapp_depth_bot : forall c w,
  apply_cont c typ_bot w -> inftapp_depth_work w <= inftapp_depth_cont_tail_rec c 0.
Proof.
  intros c w Happly.
  dependent destruction Happly; simpl; eauto.
  simpl. eapply inftapp_depth_cont_tail_rec_le; lia.
Qed.

Lemma apply_cont_inftapp_all_size_bot : forall c w,
  apply_cont c typ_bot w -> inftapp_all_size_work w = 0.
Proof.
  intros c w Happly.
  dependent destruction Happly; simpl; eauto.
Qed.

Lemma apply_cont_infabs_judge_size : forall c A w,
  apply_cont c A w -> infabs_judge_size_work w = infabs_judge_size_cont c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_cont_inftapp_judge_size : forall c A w,
  apply_cont c A w -> inftapp_judge_size_work w = inftapp_judge_size_cont c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_cont_inftapp_depth : forall c A w,
  apply_cont c A w -> inftapp_depth_work w <= inftapp_depth_cont_tail_rec c (inftapp_depth A).
Proof.
  intros c A w Happly.
  induction Happly; simpl;
    try eapply inftapp_depth_cont_tail_rec_le; try lia.
Qed.

Lemma inftapp_depth_open_typ_wrt_typ_rec : forall A B n,
  inftapp_depth (open_typ_wrt_typ_rec n B A) < (1 + inftapp_depth A) * (1 + inftapp_depth B).
Proof.
  induction A; intros; simpl; eauto; try lia.
  - destruct (lt_eq_lt_dec n n0).
    + destruct s; simpl; eauto; lia.
    + simpl; eauto; lia.
  - specialize (IHA B (S n)). lia.
  - specialize (IHA1 B n). specialize (IHA2 B n). lia.
  - specialize (IHA1 B n). specialize (IHA2 B n). lia.
Qed.

Lemma inftapp_depth_open_typ_wrt_typ : forall A B,
  inftapp_depth (open_typ_wrt_typ A B) < (1 + inftapp_depth A) * (1 + inftapp_depth B).
Proof.
  intros. unfold open_typ_wrt_typ.
  apply inftapp_depth_open_typ_wrt_typ_rec.
Qed.

Lemma decidablity_lemma : forall ne nj nt ntj na naj nm nw Γ m,
  ⊢ᵃ Γ ->
  exp_size_wl Γ < ne ->
  judge_size_wl Γ < nj ->
  inftapp_depth_wl Γ < nt ->
  inftapp_judge_size_wl Γ < ntj ->
  infabs_depth_wl Γ < na ->
  infabs_judge_size_wl Γ < naj ->
  measp_wl Γ m -> m < nm ->
  weight_wl Γ < nw ->
  Γ ⟶ᵃʷ⁎⋅ \/ ¬ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros ne; induction ne;
  intros nj; induction nj;
  intros nt; induction nt;
  intros ntj; induction ntj;
  intros na; induction na;
  intros naj; induction naj;
  intros nm; induction nm;
  intros nw; induction nw; try lia.
  intros Γ m Hwf He Hj Ht Htj Ha Haj Hm Hlt Hw.
  dependent destruction Hwf; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red aW \/ ~ a_wl_red aW).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red aW \/ ~ a_wl_red aW).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red aW \/ ~ a_wl_red aW).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red aW \/ ~ a_wl_red aW).
    { eapply IHnw; eauto; lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction H.
    + dependent destruction Hm.
      dependent destruction H; simpl in *.
      * assert (Jg: a_wl_red (aworklist_conswork aW (work_apply c typ_unit)) \/
                  ~ a_wl_red (aworklist_conswork aW (work_apply c typ_unit))).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; auto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * assert (Jg: a_wl_red (aworklist_conswork aW (work_apply c A)) \/
                  ~ a_wl_red (aworklist_conswork aW (work_apply c A))).
        { eapply IHne; eauto; simpl; try lia. admit. (* safe: wf *) }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        assert (HA: A = A0) by admit. (* safe: wf *)
        subst. apply Jg; auto.
      * right. intro Hcontra.
        dependent destruction Hcontra.
        admit. (* TODO *)
      * assert (Jg: a_wl_red (aworklist_conswork aW (work_infer e1  (  (cont_infabs  (  (cont_infapp e2 c)  ) )  ) )) \/
                  ~ a_wl_red (aworklist_conswork aW (work_infer e1  (  (cont_infabs  (  (cont_infapp e2 c)  ) )  ) ))).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * destruct body5. admit.
        (* TODO *)
      * simpl in *.
        assert (Jg: a_wl_red (aworklist_conswork aW (work_infer e (cont_inftapp A c))) \/
                  ~ a_wl_red (aworklist_conswork aW (work_infer e (cont_inftapp A c)))).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * simpl in *.
        assert (Jg: a_wl_red (aworklist_conswork (aworklist_conswork aW (work_apply c A)) (work_check e A)) \/
                  ~ a_wl_red (aworklist_conswork (aworklist_conswork aW (work_apply c A)) (work_check e A))).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
    + dependent destruction Hm. simpl in *.
      assert (He': exp_size e >= 1) by apply exp_size_gt_0.
      assert (Jg: a_wl_red (aworklist_conswork aW (work_infer e (cont_sub A))) \/
                ~ a_wl_red (aworklist_conswork aW (work_infer e (cont_sub A)))).
      { eapply IHnj; eauto; simpl; try lia. }
      assert (Jg1: forall A1 A2, A = typ_union A1 A2 ->
                  a_wl_red (aworklist_conswork aW (work_check e A1)) \/
                ~ a_wl_red (aworklist_conswork aW (work_check e A1))).
      { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
        eapply IHne; eauto; simpl; try lia. }
      assert (Jg2: forall A1 A2, A = typ_union A1 A2 ->
                  a_wl_red (aworklist_conswork aW (work_check e A2)) \/
                ~ a_wl_red (aworklist_conswork aW (work_check e A2))).
      { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
        eapply IHne; eauto; simpl; try lia. }
      assert (Jg': forall A1 A2, A = typ_intersection A1 A2 ->
                  a_wl_red (aworklist_conswork (aworklist_conswork aW (work_check e A1)) (work_check e A2)) \/
                ~ a_wl_red (aworklist_conswork (aworklist_conswork aW (work_check e A1)) (work_check e A2))).
      { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
        eapply IHne; eauto; simpl; try lia. }
      destruct Jg as [Jg | Jg]; eauto.
      dependent destruction H; simpl in *.
      * dependent destruction H0; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * dependent destruction H0; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- inst_cofinites_by (L `union` (ftvar_in_typ T) `union` (ftvar_in_aworklist aW)).
           assert (Jgt: a_wl_red (aworklist_conswork (aworklist_consvar aW x (abind_var_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top)) \/
                      ~ a_wl_red (aworklist_conswork (aworklist_consvar aW x (abind_var_typ typ_bot)) (work_check  ( open_exp_wrt_exp e (exp_var_f x) )  typ_top))).
           { eapply IHne; eauto; simpl; try lia. admit. (* safe: wf *)
             assert (Hexp: exp_size (open_exp_wrt_exp e (exp_var_f x)) = exp_size e) by admit. (* should be fine *)
             lia. }
           destruct Jgt as [Jgt | Jgt].
           ++ left. eapply a_wl_red__chk_abstop with (L := L `union` (ftvar_in_typ T) `union` (ftvar_in_aworklist aW)).
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** apply Jg; auto.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *) 
        -- right. intro Hcontra. dependent destruction Hcontra.
           ++ eapply Jg; eauto.
           ++ admit. (* safe: wf *)
        -- right. intro Hcontra. dependent destruction Hcontra.
           ++ eapply Jg; eauto.
           ++ eapply abind_etvar_stvar_false; eauto.
        -- admit. (* TODO: two step reduction reduces exp_size *)
        -- pick fresh X.
           assert (JgArr: a_wl_red (aworklist_conswork (aworklist_consvar aW X (abind_var_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f X) )  A2)) \/
                        ~ a_wl_red (aworklist_conswork (aworklist_consvar aW X (abind_var_typ A1)) (work_check  ( open_exp_wrt_exp e (exp_var_f X) )  A2))).
           { eapply IHne; eauto; simpl; try lia. admit. (* safe: wf *)
             assert (Hexp: exp_size (open_exp_wrt_exp e (exp_var_f X)) = exp_size e) by admit. (* should be fine *)
             rewrite Hexp. lia. } 
           destruct JgArr as [JgArr | JgArr]; auto.
           ++ left. eapply a_wl_red__chk_absarrow with (L := union L (union (ftvar_in_typ T) (union (ftvar_in_typ A1) (ftvar_in_typ A2)))); eauto.
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** apply Jg; auto.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * destruct body5.
        dependent destruction H0; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        -- specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        -- specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H1.
      dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      * assert (Jg: a_wl_red (aworklist_conswork Γ (work_infabs (typ_arrow typ_top typ_bot) c)) \/
                  ~ a_wl_red (aworklist_conswork Γ (work_infabs (typ_arrow typ_top typ_bot) c))).
        { eapply IHna; eauto; simpl in *; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * right. intro Hcontra.
        dependent destruction Hcontra.
        admit. (* safe: wf *)
      * right. intro Hcontra.
        dependent destruction Hcontra.
        admit. (* safe: wf *)
      * admit. (* TODO *)
      * destruct (apply_cont_dec c (typ_arrow A1 A2)) as [[w Happly] | Happly];
          try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
                     eapply Happly; eauto].
        assert (Jg: a_wl_red (aworklist_conswork Γ w) \/ 
                    ~ a_wl_red (aworklist_conswork Γ w)).
        { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
          admit. (* safe: wf *)
          eapply IHnaj; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          eapply apply_cont_exp_size in Happly; lia.
          eapply apply_cont_judge_size in Happly; lia.
          eapply apply_cont_inftapp_depth_arr in Happly. lia.
          eapply apply_cont_inftapp_judge_size in Happly; lia.
          eapply apply_cont_infabs_depth_arr in Happly; lia.
          eapply apply_cont_infabs_judge_size in Happly; lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        dependent destruction Hcontra.
        eapply apply_cont_det in Happly; eauto.
        subst. eauto.
      * pick fresh X. inst_cofinites_with X.
        assert (Jg: a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) c)) \/
                    ~ a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) c))).
        { assert (Heq: infabs_depth (open_typ_wrt_typ A (typ_var_f X)) = infabs_depth A) by admit. (* should be fine *)
          eapply IHna; eauto; simpl in *; try lia.
          admit. (* safe: wf *) }
        destruct Jg as [Jg | Jg]; eauto.
        -- left. eapply a_wl_red__infabs_all with (L := L `union` (ftvar_in_typ A) `union` (ftvar_in_aworklist Γ)).
           intros X' Hnin. admit. (* safe: rename *)
        -- right. intro Hcontra.
           dependent destruction Hcontra.
           admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
      * assert (Jg: a_wl_red (aworklist_conswork Γ (work_infabs A1  (  (cont_infabsunion A2 c)  ) )) \/
                  ~ a_wl_red (aworklist_conswork Γ (work_infabs A1  (  (cont_infabsunion A2 c)  ) ))).
        { eapply IHna; eauto; simpl in *; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * assert (Jg1: a_wl_red (aworklist_conswork Γ (work_infabs A1 c)) \/
                   ~ a_wl_red (aworklist_conswork Γ (work_infabs A1 c))).
        { eapply IHna; eauto; simpl in *; try lia. }
        assert (Jg2: a_wl_red (aworklist_conswork Γ (work_infabs A2 c)) \/
                   ~ a_wl_red (aworklist_conswork Γ (work_infabs A2 c))).
        { eapply IHna; eauto; simpl in *; try lia. }
        destruct Jg1 as [Jg1 | Jg1]; eauto.
        destruct Jg2 as [Jg2 | Jg2]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg1; auto. apply Jg2; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      assert (Jg: a_wl_red (aworklist_conswork aW (work_infabs A2  (  (cont_unioninfabs (typ_arrow A1 A0) c)  ) )) \/
                  ~ a_wl_red (aworklist_conswork aW (work_infabs A2  (  (cont_unioninfabs (typ_arrow A1 A0) c)  ) ))).
      { eapply IHnaj; eauto; simpl in *; try lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra. eauto.
    + admit. (* TODO !!! *) 
    + simpl in *. dependent destruction Hm. dependent destruction H2.
      dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      * destruct (apply_cont_dec c typ_bot) as [[w Happly] | Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: a_wl_red (aworklist_conswork Γ w) \/
                  ~ a_wl_red (aworklist_conswork Γ w)).
        { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
          admit. (* safe: wf *)
          eapply IHntj; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          eapply apply_cont_exp_size in Happly; lia.
          eapply apply_cont_judge_size in Happly; lia.
          eapply apply_cont_inftapp_depth_bot in Happly.
          rewrite mult_0_r in Ht. lia.
          eapply apply_cont_inftapp_judge_size in Happly; lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        dependent destruction Hcontra.
        eapply apply_cont_det in Happly; eauto.
        subst. eauto.
      * destruct (apply_cont_dec c (open_typ_wrt_typ A A2)) as [[w Happly] | Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: a_wl_red (aworklist_conswork Γ w) \/
                  ~ a_wl_red (aworklist_conswork Γ w)).
        { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
          admit. (* safe: wf *)
          eapply IHntj; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          eapply apply_cont_exp_size in Happly; lia.
          eapply apply_cont_judge_size in Happly; lia.
          eapply apply_cont_inftapp_depth in Happly.
          assert (Hfact: inftapp_depth (open_typ_wrt_typ A A2) < (1 + inftapp_depth A) * (1 + inftapp_depth A2))
            by eapply inftapp_depth_open_typ_wrt_typ.
          assert (Hfact': inftapp_depth_work w <= inftapp_depth_cont_tail_rec c ((1 + inftapp_depth A) * (1 + inftapp_depth A2))).
          { eapply le_trans; eauto. eapply inftapp_depth_cont_tail_rec_le. lia. }
          assert (Hfact'': inftapp_depth_cont_tail_rec c ((1 + inftapp_depth A) * (1 + inftapp_depth A2)) <= inftapp_depth_cont_tail_rec c
          (S
             (inftapp_depth A +
              S
                (inftapp_depth A +
                 inftapp_depth A2 * S (inftapp_depth A))))).
          { eapply inftapp_depth_cont_tail_rec_le; eauto; lia. }
          lia.
          eapply apply_cont_inftapp_judge_size in Happly; lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        dependent destruction Hcontra.  
        eapply apply_cont_det in Happly; eauto.
        subst. eauto.
      * assert (Jg: a_wl_red (aworklist_conswork Γ (work_inftapp A1 A2  (  (cont_inftappunion A0 A2 c)  ) )) \/
                  ~ a_wl_red (aworklist_conswork Γ (work_inftapp A1 A2  (  (cont_inftappunion A0 A2 c)  ) ))).
        { eapply IHnt; eauto; simpl in *; try lia.
          assert (inftapp_depth_cont_tail_rec c
          (inftapp_depth A0 * S (S (inftapp_depth A2)) + 1 +
           (inftapp_depth A1 +
            (inftapp_depth A1 + inftapp_depth A2 * inftapp_depth A1)))
            < inftapp_depth_cont_tail_rec c
            (S
               (inftapp_depth A1 + inftapp_depth A0 +
                S
                  (inftapp_depth A1 + inftapp_depth A0 +
                   inftapp_depth A2 *
                   S (inftapp_depth A1 + inftapp_depth A0))))).
          { eapply inftapp_depth_cont_tail_rec_lt; eauto; try lia. }
          lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * assert (Jg1: a_wl_red (aworklist_conswork Γ (work_inftapp A1 A2 c)) \/
                   ~ a_wl_red (aworklist_conswork Γ (work_inftapp A1 A2 c))).
        { eapply IHnt; eauto; simpl in *; try lia.
          assert (inftapp_depth_cont_tail_rec c
          (inftapp_depth A1 +
           (inftapp_depth A1 + inftapp_depth A2 * inftapp_depth A1))
                    <  inftapp_depth_cont_tail_rec c
                    (S
                       (inftapp_depth A1 + inftapp_depth A0 +
                        S
                          (inftapp_depth A1 + inftapp_depth A0 +
                           inftapp_depth A2 *
                           S (inftapp_depth A1 + inftapp_depth A0))))).
          { eapply inftapp_depth_cont_tail_rec_lt; eauto; try lia. }
          lia. }
        assert (Jg2: a_wl_red (aworklist_conswork Γ (work_inftapp A0 A2 c)) \/
                   ~ a_wl_red (aworklist_conswork Γ (work_inftapp A0 A2 c))).
        { eapply IHnt; eauto; simpl in *; try lia.
          assert (inftapp_depth_cont_tail_rec c
          (inftapp_depth A0 +
           (inftapp_depth A0 + inftapp_depth A2 * inftapp_depth A0))
                    < inftapp_depth_cont_tail_rec c
                    (S
                       (inftapp_depth A1 + inftapp_depth A0 +
                        S
                          (inftapp_depth A1 + inftapp_depth A0 +
                           inftapp_depth A2 *
                           S (inftapp_depth A1 + inftapp_depth A0))))).
          { eapply inftapp_depth_cont_tail_rec_lt; eauto; try lia. }
          lia. }
        destruct Jg1 as [Jg1 | Jg1]; eauto.
        destruct Jg2 as [Jg2 | Jg2]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg1; auto. apply Jg2; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H3.
      assert (Jg: a_wl_red (aworklist_conswork Γ (work_inftapp A2 B  (  (cont_unioninftapp A1 c)  ) )) \/
                ~ a_wl_red (aworklist_conswork Γ (work_inftapp A2 B  (  (cont_unioninftapp A1 c)  ) ))).
      { eapply IHntj; eauto; simpl; try lia.
        assert (inftapp_depth_cont_tail_rec c
        (S
           (inftapp_depth A1 +
            (inftapp_depth A2 +
             (inftapp_depth A2 + inftapp_depth B * inftapp_depth A2))))
             <= inftapp_depth_cont_tail_rec c
             (inftapp_depth A1 +
              inftapp_depth A2 * S (S (inftapp_depth B)) + 1)).
          { eapply inftapp_depth_cont_tail_rec_le; eauto; try lia. }
        lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H2.
      destruct (apply_cont_dec c (typ_union A1 A2)) as [[w Happly] | Happly];
      try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
        eapply Happly; eauto].
      assert (Jg: a_wl_red (aworklist_conswork Γ w) \/
                ~ a_wl_red (aworklist_conswork Γ w)).
      { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
        admit. (* safe: wf *)
        eapply IHntj; eauto; simpl in *; try lia.
        admit. (* safe: wf *)
        eapply apply_cont_exp_size in Happly; lia.
        eapply apply_cont_judge_size in Happly; lia.
        eapply apply_cont_inftapp_depth in Happly.
        assert (inftapp_depth_cont_tail_rec c
        (inftapp_depth (typ_union A1 A2)) <= inftapp_depth_cont_tail_rec c
        (S (inftapp_depth A1 + inftapp_depth A2))). 
        { eapply inftapp_depth_cont_tail_rec_le; eauto; lia. }
        lia.
        eapply apply_cont_inftapp_judge_size in Happly; lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      dependent destruction Hcontra.
      eapply apply_cont_det in Happly; eauto.
      subst. eauto.
    + simpl in *. dependent destruction Hm. dependent destruction H2.
      dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra];
      dependent destruction H1;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      destruct (apply_cont_dec c (typ_arrow  ( (typ_intersection A1 A2) )   ( (typ_union A0 A3) ) )) as [[w Happly] | Happly];
      try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
        eapply Happly; eauto].
      assert (Jg: a_wl_red (aworklist_conswork Γ w) \/
                ~ a_wl_red (aworklist_conswork Γ w)).
      { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
        admit. (* safe: wf *)
        eapply IHnaj; eauto; simpl in *; try lia.
        admit. (* safe: wf *)
        eapply apply_cont_exp_size in Happly; lia.
        eapply apply_cont_judge_size in Happly; lia.
        (* eapply apply_cont_inftapp_all_size_arr in Happly; lia. *)
        eapply apply_cont_inftapp_depth_arr in Happly; lia.
        eapply apply_cont_inftapp_judge_size in Happly; lia.
        eapply apply_cont_infabs_depth_arr in Happly; lia.
        eapply apply_cont_infabs_judge_size in Happly; lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      dependent destruction Hcontra.
      eapply apply_cont_det in Happly; eauto.
      subst. eauto.
    + simpl in *. dependent destruction Hm. dependent destruction H1.
      dependent destruction H1. dependent destruction H3.
      assert (Hw': weight A >= 1) by apply weight_gt_0.
      assert (Hw'0: weight A0 >= 1) by apply weight_gt_0.
      assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
      { eapply IHnw; eauto; simpl; try lia. }
      assert (JgInter1: forall A1 A2, A0 = typ_intersection A1 A2 ->
                a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A A1)) (work_sub A A2)) \/
              ~ a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A A1)) (work_sub A A2))).
      { intros A1 A2 Heq. subst. dependent destruction H3.
        eapply IHnw with (m := ((3 * m + all_size A) * (1 + iu_size A2) + (3 * n2 + all_size A2) * (1 + iu_size A)) + ((3 * m + all_size A) * (1 + iu_size A1) + (3 * n1 + all_size A1) * (1 + iu_size A)) + n); eauto; try lia.
        admit. (* safe: wf *)
        assert (HspA: split_size (aworklist_conswork Γ (work_sub A A1)) A m) by admit.
        assert (HspA2: split_size (aworklist_conswork Γ (work_sub A A1)) A2 n2) by admit.
        eapply measp_wl_conswork with
          (m := ((3 * m + all_size A) * (1 + iu_size A2) + (3 * n2 + all_size A2) * (1 + iu_size A)))
          (n := ((3 * m + all_size A) * (1 + iu_size A1) + (3 * n1 + all_size A1) * (1 + iu_size A)) + n); eauto; try lia.
        assert (Hle:
          (3 * m + all_size A) * (1 + iu_size A2) +
          (3 * n2 + all_size A2) * (1 + iu_size A) +
          ((3 * m + all_size A) * (1 + iu_size A1) +
          (3 * n1 + all_size A1) * (1 + iu_size A)) + n <=
          (3 * m + all_size A) * (1 + iu_size (typ_intersection A1 A2)) +
          (3 * S (n1 + n2) + all_size (typ_intersection A1 A2)) * (1 + iu_size A) + n).
        { simpl. lia. }
        lia. simpl in *. lia. }
      assert (JgInter2: forall A1 A2, A = typ_intersection A1 A2 ->
                a_wl_red (aworklist_conswork Γ (work_sub A1 A0)) \/
              ~ a_wl_red (aworklist_conswork Γ (work_sub A1 A0))).
      { intros A1 A2 Heq. subst. dependent destruction H1.
        eapply IHnw; eauto; simpl in *; try lia.
        admit. (* safe: wf *) }
      assert (JgInter3: forall A1 A2, A = typ_intersection A1 A2 ->
                a_wl_red (aworklist_conswork Γ (work_sub A2 A0)) \/
              ~ a_wl_red (aworklist_conswork Γ (work_sub A2 A0))).
      { intros A1 A2 Heq. subst. dependent destruction H1.
        eapply IHnw; eauto; simpl in *; try lia.
        admit. (* safe: wf *) }
      assert (JgUnion1: forall A1 A2, A0 = typ_union A1 A2 ->
                a_wl_red (aworklist_conswork Γ (work_sub A A1)) \/
              ~ a_wl_red (aworklist_conswork Γ (work_sub A A1))).
      { intros A1 A2 Heq. subst. dependent destruction H3.
        eapply IHnw; eauto; simpl in *; try lia.
        admit. (* safe: wf *) }
      assert (JgUnion2: forall A1 A2, A0 = typ_union A1 A2 ->
                a_wl_red (aworklist_conswork Γ (work_sub A A2)) \/
              ~ a_wl_red (aworklist_conswork Γ (work_sub A A2))).
      { intros A1 A2 Heq. subst. dependent destruction H3.
        eapply IHnw; eauto; simpl in *; try lia.
        admit. (* safe: wf *) }
      assert (JgUnion3: forall A1 A2, A = typ_union A1 A2 ->
                a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A1 A0)) (work_sub A2 A0)) \/
              ~ a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A1 A0)) (work_sub A2 A0))).
      { intros A1 A2 Heq. subst. dependent destruction H1.
        eapply IHnw with (m := ((3 * n2 + all_size A2) * (1 + iu_size A0) + (3 * m0 + all_size A0) * (1 + iu_size A2)) +
                                ((3 * n1 + all_size A1) * (1 + iu_size A0) + (3 * m0 + all_size A0) * (1 + iu_size A1)) + n); eauto; try lia.
        admit. (* safe: wf *)
        assert (HspA: split_size (aworklist_conswork Γ (work_sub A1 A0)) A0 m0) by admit.
        assert (HspA2: split_size (aworklist_conswork Γ (work_sub A1 A0)) A2 n2) by admit.
        eapply measp_wl_conswork with
          (m := ((3 * n2 + all_size A2) * (1 + iu_size A0) + (3 * m0 + all_size A0) * (1 + iu_size A2)))
          (n := ((3 * n1 + all_size A1) * (1 + iu_size A0) + (3 * m0 + all_size A0) * (1 + iu_size A1)) + n); eauto; try lia.
        assert (Hle: (3 * n2 + all_size A2) * (1 + iu_size A0) +
        (3 * m0 + all_size A0) * (1 + iu_size A2) +
        ((3 * n1 + all_size A1) * (1 + iu_size A0) +
        (3 * m0 + all_size A0) * (1 + iu_size A1)) + n <=
        (3 * S (n1 + n2) + all_size (typ_union A1 A2)) * (1 + iu_size A0) +
        (3 * m0 + all_size A0) * iu_size (typ_union A1 A2) + n).
        { simpl. lia. }
        lia. simpl in *. lia. }
      assert (JgAlll: forall A1 X L, A = typ_all A1 ->
                neq_all A0 ->
                neq_intersection A0 ->
                neq_union A0 ->
                X \notin  L ->
                a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_sub  ( open_typ_wrt_typ A1 (typ_var_f X) )  A0)) \/
              ~ a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_sub  ( open_typ_wrt_typ A1 (typ_var_f X) )  A0))).
      { intros A1 X L Heq HneqAll HneqInter HneqUnion Hnin. subst. dependent destruction H1.
        assert (HspA: split_size (aworklist_constvar Γ X abind_etvar_empty) ( open_typ_wrt_typ A1 (typ_var_f X) ) n0) by admit.
        assert (HspA0: split_size (aworklist_constvar Γ X abind_etvar_empty) A0 m0) by admit.
        assert (Heq: iu_size (typ_all A1) = iu_size (A1 ^ᵈ X)) by admit. (* safe *)
        eapply IHnw with (m := (3 * n0 + all_size (A1 ^ᵈ X)) * (1 + iu_size A0) +
                                (3 * m0 + all_size A0) * (1 + iu_size (A1 ^ᵈ X)) + S n); eauto; try lia.
        admit. (* safe: wf *)
        eapply measp_wl_conswork; eauto.
        assert (Heq': all_size (typ_all A1) = all_size (A1 ^ᵈ X) + 1) by admit. (* safe *)
        rewrite Heq in Hlt. rewrite Heq' in Hlt. lia.
        assert (Heq': weight (A1 ^ᵈ X) = weight A1) by admit. (* safe *)
        assert (Hgt: weight A0 >= 1) by apply weight_gt_0.
        simpl in *. rewrite <- Heq. rewrite Heq'. lia. }
      assert (JgInst1: forall (E:list typvar) (Γ1 Γ2:aworklist) (X:typvar),
                A = typ_var_f X ->
                binds X abind_etvar_empty (awl_to_aenv Γ) ->
                a_mono_typ (awl_to_aenv Γ) A0 ->
                aworklist_subst Γ X A0 E Γ1 Γ2 ->
                a_wl_red (awl_app (subst_tvar_in_aworklist A0 X Γ2) (awl_app (etvar_list_to_awl E) Γ1)) \/
                ~ a_wl_red (awl_app (subst_tvar_in_aworklist A0 X Γ2) (awl_app (etvar_list_to_awl E) Γ1))).
      { intros E Γ1 Γ2 X Heq Hbin Hmono Hsub. subst.
        eapply IHnw.
        admit. (* safe: wf *)
        - rewrite exp_size_wl_awl_app.
          rewrite exp_size_wl_awl_app.
          rewrite exp_size_wl_etvar_list.
          erewrite exp_size_wl_subst_tvar_in_aworklist_mono; eauto. simpl.
          eapply exp_size_wl_aworklist_subst in Hsub as Heq. lia.
        - rewrite judge_size_wl_awl_app.
          rewrite judge_size_wl_awl_app.
          rewrite judge_size_wl_etvar_list.
          erewrite judge_size_wl_subst_tvar_in_aworklist; eauto. simpl.
          eapply judge_size_wl_aworklist_subst in Hsub as Heq. lia.
        - admit.
        - admit. 
        - admit.
        - admit.
        - admit.
        - admit.
        - admit.
      }
      dependent destruction H.
      * dependent destruction H0;
          try solve [right; intro Hcontra;
            dependent destruction Hcontra];
          try solve [destruct Jg as [Jg | Jg]; eauto;
            right; intro Hcontra; dependent destruction Hcontra;
            eapply Jg; eauto].
        -- right. intro Hcontra. dependent destruction Hcontra.
           eapply abind_etvar_tvar_false; eauto.
        -- right. intro Hcontra. dependent destruction Hcontra.
            eapply abind_etvar_stvar_false; eauto.
        -- admit. (* TODO *)
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply JgInter1'; eauto.
      * dependent destruction H0;
          try solve [right; intro Hcontra;
            dependent destruction Hcontra];
          try solve [destruct Jg as [Jg | Jg]; eauto;
            right; intro Hcontra; dependent destruction Hcontra;
            eapply Jg; eauto];
          destruct Jg as [Jg | Jg]; eauto;
          try solve [right; intro Hcontra; dependent destruction Hcontra;
            eapply Jg; eauto; dependent destruction H5].
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply Jg; eauto. eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply Jg; eauto. eapply JgInter1'; eauto.
      * dependent destruction H0;
          try solve [right; intro Hcontra;
            dependent destruction Hcontra];
          try solve [destruct Jg as [Jg | Jg]; eauto;
            right; intro Hcontra; dependent destruction Hcontra;
            eapply Jg; eauto];
          try solve [right; intro Hcontra; dependent destruction Hcontra;
            dependent destruction H5].
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply JgInter1'; eauto.
      * admit. (* TODO *)
      * admit. (* TODO *)
      * admit. (* TODO *)
      * dependent destruction H1;
          try solve [right; intro Hcontra;
            dependent destruction Hcontra];
          try solve [destruct Jg as [Jg | Jg]; eauto;
            right; intro Hcontra; dependent destruction Hcontra;
            eapply Jg; eauto].
        -- right. intro Hcontra. dependent destruction Hcontra.
           eapply abind_etvar_tvar_false; eauto.
           eapply abind_etvar_tvar_false; eauto.
        -- right. intro Hcontra. dependent destruction Hcontra.
           eapply abind_etvar_stvar_false; eauto.
           eapply abind_etvar_stvar_false; eauto.
        -- admit. (* TODO *)
        -- assert (JgArr: a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A0 A1)) (work_sub A2 A3)) \/
                        ~ a_wl_red (aworklist_conswork (aworklist_conswork Γ (work_sub A0 A1)) (work_sub A2 A3))).
           { assert (Hle: forall ns1 ns2 ns0 ns3,
                      split_size (aworklist_conswork Γ (work_sub A0 A1)) A2 ns2 ->
                      split_size (aworklist_conswork Γ (work_sub A0 A1)) A3 ns3 ->
                      split_size Γ A0 ns0 -> split_size Γ A1 ns1 ->
                      ((3 * ns2 + all_size A2) * (1 + iu_size A3) +
                      (3 * ns3 + all_size A3) * (1 + iu_size A2)) +
                      ((3 * ns0 + all_size A0) * (1 + iu_size A1) +
                      (3 * ns1 + all_size A1) * (1 + iu_size A0))
                        <= n0 * (1 + iu_size (typ_arrow A0 A3)) + n1 * (1 + iu_size (typ_arrow A1 A2))).
                    { intros ns1 ns2 ns0 ns3 Hns2 Hns3 Hns0 Hns1.
                      rewrite H3. rewrite H5.
                      assert (Hle': ns1 + ns2 <= m) by admit. (* CHECK THIS! *)
                      assert (Hle'': ns0 + ns3 <= m0) by admit. (* CHECK THIS! *)
                      eapply le_trans with (m := (3 * (ns1 + ns2) + all_size (typ_arrow A1 A2)) * (1 + iu_size (typ_arrow A0 A3))
                                               + (3 * (ns0 + ns3) + all_size (typ_arrow A0 A3)) * (1 + iu_size (typ_arrow A1 A2))).
                      simpl in *. lia. admit. (* safe: oh my lia. *) }
            assert (Hs2: exists ns2, split_size (work_sub A0 A1 ⫤ Γ) A2 ns2) by admit.
            assert (Hs3: exists ns3, split_size (work_sub A0 A1 ⫤ Γ) A3 ns3) by admit.
            assert (Hs0: exists ns0, split_size Γ A0 ns0) by admit.
            assert (Hs1: exists ns1, split_size Γ A1 ns1) by admit.
            destruct Hs2 as [ns2 Hs2]. destruct Hs3 as [ns3 Hs3].
            destruct Hs0 as [ns0 Hs0]. destruct Hs1 as [ns1 Hs1].
            specialize (Hle ns1 ns2 ns0 ns3 Hs2 Hs3 Hs0 Hs1).
            eapply IHnw with (m := ((3 * ns2 + all_size A2) * (1 + iu_size A3) +
                                    (3 * ns3 + all_size A3) * (1 + iu_size A2)) +
                                    ((3 * ns0 + all_size A0) * (1 + iu_size A1) +
                                    (3 * ns1 + all_size A1) * (1 + iu_size A0)) + n); eauto.
            eapply measp_wl_conswork with (n := ((3 * ns0 + all_size A0) * (1 + iu_size A1) +
                                                    (3 * ns1 + all_size A1) * (1 + iu_size A0)) + n); eauto; try lia.
            lia. simpl in *. lia. }
            destruct JgArr as [JgArr | JgArr]; eauto.
            right. intro Hcontra. dependent destruction Hcontra.
            apply JgArr; auto.
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply JgInter1'; eauto.
      * dependent destruction H1.
        (* can use some tatics, while have to solve the binding problem first*) 
        -- pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. eapply a_wl_red__sub_alll with (L := union L (ftvar_in_typ A)); eauto.
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
        -- pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. eapply a_wl_red__sub_alll with (L := union L (ftvar_in_typ A)); eauto.
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
        -- destruct Jg as [Jg | Jg]; eauto.
           pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. eapply a_wl_red__sub_alll with (L := union L (ftvar_in_typ A)); eauto.
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** apply Jg; auto.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
        -- pick fresh x. inst_cofinites_with x.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. eapply a_wl_red__sub_alll with (L := union L (union (singleton X) (ftvar_in_typ A))); eauto.
              intros x' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
              ** dependent destruction H7.
        -- pick fresh x. inst_cofinites_with x.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. eapply a_wl_red__sub_alll with (L := union L (union (singleton X) (ftvar_in_typ A))); eauto.
              intros x' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
              ** dependent destruction H7.
        -- pick fresh x. inst_cofinites_with x.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. eapply a_wl_red__sub_alll with (L := union L (union (singleton X) (ftvar_in_typ A))); eauto.
              intros x' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
              ** dependent destruction H7.
        -- pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           admit. admit. admit. (* safe *) 
           ++ left. eapply a_wl_red__sub_alll with (L := union L (union (ftvar_in_typ A) (union (ftvar_in_typ A1) (ftvar_in_typ A2)))); eauto.
              admit. admit. admit. (* safe *)
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
        -- dependent destruction H3. dependent destruction H5.
           pick fresh X. inst_cofinites_with X.
           assert (Heq: all_size A = all_size (A ^ᵈ X)) by admit. (* safe *)
           assert (Heq0: all_size A0 = all_size (A0 ^ᵈ X)) by admit. (* safe *)
           assert (Heq': iu_size A = iu_size (A ^ᵈ X)) by admit. (* safe *)
           assert (Heq0': iu_size A0 = iu_size (A0 ^ᵈ X)) by admit. (* safe *)
           assert (Heq'': weight A = weight (A ^ᵈ X)) by admit. (* safe *)
           assert (Heq0'': weight A0 = weight (A0 ^ᵈ X)) by admit. (* safe *)
           assert (JgAll: a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ A0 (typ_var_f X) ) )) \/
                        ~ a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ A0 (typ_var_f X) ) ))).
           { eapply IHnw with (m := (3 * n1 + all_size (A ^ᵈ X)) * iu_size (A0 ^ᵈ X) + (3 * n3 + all_size (A0 ^ᵈ X)) * iu_size (A ^ᵈ X) + n); eauto; simpl in *; try lia.
             admit. (* safe: wf *)
             eapply measp_wl_conswork; eauto; try lia. 
             admit.
             }
           destruct JgAll as [JgAll | JgAll]; eauto.
           ++ left. eapply a_wl_red__sub_all with (L := union L (union L0 (union L1 (union L2 (union (ftvar_in_typ A) (ftvar_in_typ A0)))))); eauto.
              intros X' Hnin. admit. (* safe: rename *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** dependent destruction H7.
              ** admit. (* TODO: check this! I am suffering from bindings. (should be fine, I guess) *)
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           ++ dependent destruction H7.
           ++ eapply JgUnion1'; eauto.
           ++ eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           ++ dependent destruction H6.
           ++ eapply JgInter1'; eauto.
    * dependent destruction H1;
        try solve [edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto;
                   right; intro Hcontra; dependent destruction Hcontra;
                   eapply JgUnion3'; eauto; try dependent destruction H7].
      -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
         edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
         edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         eapply JgUnion1'; eauto. eapply JgUnion2'; eauto. eapply JgUnion3'; eauto.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         eapply JgInter1'; eauto. eapply JgUnion3'; eauto.
    * dependent destruction H1;
        edestruct JgInter2 as [JgInter2' | JgInter2']; eauto;
        edestruct JgInter3 as [JgInter3' | JgInter3']; eauto;
        try solve [right; intro Hcontra; dependent destruction Hcontra;
          try solve [eapply JgInter2'; eauto]; try solve [eapply JgInter3'; eauto];
          dependent destruction H7].
      -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
         edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         eapply JgInter2'; eauto. eapply JgInter3'; eauto.
         eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         eapply JgInter1'; eauto. eapply JgInter2'; eauto. eapply JgInter3'; eauto.
  + simpl in *.
    edestruct (apply_cont_dec c A) as [[w Happly] | Happly].
    * eapply apply_cont_exp_size in Happly as Hes.
      eapply apply_cont_judge_size in Happly as Hjs.
      destruct (measp_wl_total (aworklist_conswork aW w)) as [m' Hms].
      admit. (* safe: wf *) 
      assert (JgApply: a_wl_red (aworklist_conswork aW w) \/
                     ~ a_wl_red (aworklist_conswork aW w)).
      { eapply IHnj with (m := m'); simpl; eauto; try lia. admit. (* safe: wf *) }
      destruct JgApply as [JgApply | JgApply]; eauto.
      right. intro Hcontra. dependent destruction Hcontra.
      eapply apply_cont_det in Happly; eauto. subst. eapply JgApply; eauto.
Admitted.
