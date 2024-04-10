Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Coq.micromega.Lia.

Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import uni.algo_worklist.prop_rename.
Require Import uni.algo_worklist.prop_completeness.
Require Import uni.algo_worklist.transfer.
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

Fixpoint exp_size (Γ : aworklist) (e : exp) : nat :=
  match e with
  | exp_unit => 1
  | exp_var_b _ => 1
  | exp_var_f _ => 1
  | exp_abs e => 1 + exp_size Γ e
  | exp_app e1 e2 => 1 + exp_size Γ e1 + exp_size Γ e2 * (1 + exp_split_size (awl_to_aenv Γ) e1)
  | exp_tabs b => 1 + body_size Γ b
  | exp_tapp e _ => 1 + exp_size Γ e
  | exp_anno e A => 1 + exp_size Γ e * (1 + iu_size A)
  end
with body_size (Γ : aworklist) (b : body) : nat :=
  match b with 
  | body_anno e A => exp_size Γ e * (1 + iu_size A)
  end.

Lemma exp_size_gt_0 : forall Γ e,
  exp_size Γ e > 0.
Proof.
  induction e; simpl; try lia.
Qed.

Fixpoint exp_size_conts (Γ : aworklist) (cs : conts) : nat :=
  match cs with
  | conts_infabs cd => exp_size_contd Γ cd
  | conts_inftapp _ cs => exp_size_conts Γ cs
  | conts_inftappunion _ _ cs => exp_size_conts Γ cs
  | conts_unioninftapp _ cs => exp_size_conts Γ cs
  | conts_sub A => 0
  end
with exp_size_contd (Γ : aworklist) (cd : contd) : nat :=
  match cd with
  | contd_infabsunion _ cd => exp_size_contd Γ cd
  | contd_infapp n e cs => exp_size Γ e * (1 + n) + exp_size_conts Γ cs
  | contd_unioninfabs _ _ cd => exp_size_contd Γ cd
  end.

Definition exp_size_work (Γ : aworklist) (w : work) : nat :=
  match w with
  | work_infer e cs => exp_size Γ e + exp_size_conts Γ cs
  | work_check e A => exp_size Γ e * (1 + iu_size A)
  | work_infabs _ cd => exp_size_contd Γ cd
  | work_infabsunion _ _ _ cd => exp_size_contd Γ cd
  | work_infapp A _ e cs => exp_size Γ e * (1 + iu_size A) + exp_size_conts Γ cs
  | work_inftapp _ _ cs => exp_size_conts Γ cs
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ cs => exp_size_conts Γ cs
  | work_unioninftapp _ _ cs => exp_size_conts Γ cs
  | work_unioninfabs _ _ _ _ cd => exp_size_contd Γ cd
  | work_applys cs _ => exp_size_conts Γ cs
  | work_applyd cd _ _ => exp_size_contd Γ cd
  end.

Fixpoint exp_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => exp_size_wl Γ'
  | aworklist_consvar Γ' _ _ => exp_size_wl Γ'
  | aworklist_conswork Γ' w => exp_size_work Γ' w + exp_size_wl Γ'
  end.

Fixpoint judge_size_conts (cs : conts) : nat :=
  match cs with
  | conts_infabs cd => judge_size_contd cd
  | conts_inftapp _ cs => judge_size_conts cs
  | conts_inftappunion _ _ cs => judge_size_conts cs
  | conts_unioninftapp _ cs => judge_size_conts cs
  | conts_sub _ => 0
  end
with judge_size_contd (cd : contd) : nat :=
  match cd with
  | contd_infabsunion _ cd => judge_size_contd cd
  | contd_infapp _ _ cs => 5 + judge_size_conts cs
  | contd_unioninfabs _ _ cd => judge_size_contd cd
  end.

Definition judge_size_work (w : work) : nat :=
  match w with
  | work_infer e cs => 2 + judge_size_conts cs
  | work_check e A => 3
  | work_infabs _ cd => judge_size_contd cd
  | work_infabsunion _ _ _ cd => judge_size_contd cd
  | work_infapp _ _ e cs => 5 + judge_size_conts cs
  | work_inftapp _ _ cs => judge_size_conts cs
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ cs => judge_size_conts cs
  | work_unioninftapp _ _ cs => judge_size_conts cs
  | work_unioninfabs _ _ _ _ cd => judge_size_contd cd
  | work_applys cs _ => 1 + judge_size_conts cs
  | work_applyd cd _ _ => 1 + judge_size_contd cd
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
  | split_size_work_infabs : forall Γ A c,
      split_size_work Γ (work_infabs A c) 0
  | split_size_work_infabsunion : forall Γ A1 B1 A2 c,
      split_size_work Γ (work_infabsunion A1 B1 A2 c) 0
  | split_size_work_infapp : forall Γ A B e c,
      split_size_work Γ (work_infapp A B e c) 0
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
  | split_size_work_unioninfabs : forall Γ A1 B1 A2 B2 c,
      split_size_work Γ (work_unioninfabs A1 B1 A2 B2 c) 0
  | split_size_work_applys : forall Γ cs A,
      split_size_work Γ (work_applys cs A) 0
  | split_size_work_applyd : forall Γ cd A B,
      split_size_work Γ (work_applyd cd A B) 0.

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
  | work_infabs _ _ => 0
  | work_infabsunion _ _ _ _ => 0
  | work_infapp _ _ _ _ => 0
  | work_inftapp _ _ _ => 0
  | work_sub A1 A2 => all_size A1 + all_size A2
  | work_inftappunion _ _ _ _ => 0
  | work_unioninftapp _ _ _ => 0
  | work_unioninfabs _ _ _ _ _ => 0
  | work_applys _ _ => 0
  | work_applyd _ _ _ => 0
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
  | measp_work_infabsunion : forall Γ A1 B1 A2 c,
      measp_work Γ (work_infabsunion A1 B1 A2 c) 0
  | measp_work_infapp : forall Γ A B e c,
      measp_work Γ (work_infapp A B e c) 0
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
  | measp_work_unioninfabs : forall Γ A1 B1 A2 B2 c,
      measp_work Γ (work_unioninfabs A1 B1 A2 B2 c) 0
  | measp_work_applys : forall Γ cs A,
      measp_work Γ (work_applys cs A) 0
  | measp_work_applyd : forall Γ cd A B,
      measp_work Γ (work_applyd cd A B) 0.

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

Fixpoint infabs_depth_contd (cd : contd) : nat :=
  match cd with
  | contd_infabsunion A cd => 1 + infabs_depth A + infabs_depth_contd cd
  | contd_unioninfabs _ _ cd => 1 + infabs_depth_contd cd
  | _ => 0
  end.

Definition infabs_depth_conts (cs : conts) : nat :=
  match cs with
  | conts_infabs cd => 1 + infabs_depth_contd cd
  | _ => 0
  end.

Definition infabs_depth_work (w : work) : nat :=
  match w with
  | work_infabs A c => infabs_depth A + infabs_depth_contd c
  | work_infabsunion _ _ A c => 1 + infabs_depth A + infabs_depth_contd c
  | work_unioninfabs _ _ _ _ c => 1 + infabs_depth_contd c
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

Fixpoint inftapp_depth (A : typ) : nat :=
  match A with
  | typ_all A => 1 + inftapp_depth A
  | typ_union A1 A2 => 1 + inftapp_depth A1 + inftapp_depth A2
  | typ_intersection A1 A2 => 1 + inftapp_depth A1 + inftapp_depth A2
  | typ_var_b _ => 1
  | _ => 0
  end.

Fixpoint inftapp_depth_conts_tail_rec (cs : conts) (ans : nat) : nat :=
  match cs with
  | conts_infabs cd            => inftapp_depth_contd_tail_rec cd ans
  | conts_inftapp B cs         => inftapp_depth_conts_tail_rec cs ((2 + inftapp_depth B) * ans)
  | conts_inftappunion A B cs  => inftapp_depth_conts_tail_rec cs ((inftapp_depth A) * (2 + inftapp_depth B) + 1 + ans)
  | conts_unioninftapp A cs    => inftapp_depth_conts_tail_rec cs (1 + inftapp_depth A + ans)
  | _                          => ans
  end
with inftapp_depth_contd_tail_rec (cd : contd) (ans : nat) : nat :=
  match cd with
  | contd_infabsunion _ cd => inftapp_depth_contd_tail_rec cd ans
  | contd_infapp _ _ cs => inftapp_depth_conts_tail_rec cs ans
  | contd_unioninfabs _ _ cd => inftapp_depth_contd_tail_rec cd ans
  end.

Definition inftapp_depth_work (w : work) : nat :=
  match w with
  | work_inftapp A B cs => inftapp_depth_conts_tail_rec (conts_inftapp B cs) (inftapp_depth A)
  | work_inftappunion A1 A2 B cs => inftapp_depth_conts_tail_rec cs (inftapp_depth A1 + (inftapp_depth A2) * (2 + inftapp_depth B) + 1)
  | work_infer _ cs => inftapp_depth_conts_tail_rec cs 0
  | work_infabs _ cd => inftapp_depth_contd_tail_rec cd 0
  | work_infabsunion _ _ _ cd => inftapp_depth_contd_tail_rec cd 0
  | work_infapp _ _ _ cs => inftapp_depth_conts_tail_rec cs 0
  | work_unioninftapp A1 A2 cs => inftapp_depth_conts_tail_rec cs (1 + inftapp_depth A1 + inftapp_depth A2)
  | work_unioninfabs _ _ _ _ cd => inftapp_depth_contd_tail_rec cd 0
  | _ => 0
  end.

Fixpoint inftapp_depth_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => inftapp_depth_wl Γ'
  | aworklist_consvar Γ' _ _ => inftapp_depth_wl Γ'
  | aworklist_conswork Γ' w => inftapp_depth_work w + inftapp_depth_wl Γ'
  end.

#[local] Hint Unfold inftapp_depth_conts_tail_rec inftapp_depth_contd_tail_rec inftapp_depth inftapp_depth_work inftapp_depth_wl : core.

Fixpoint infabs_judge_size_conts (cs : conts) : nat :=
  match cs with
  | conts_infabs cd => 1 + infabs_judge_size_contd cd
  | conts_inftapp _ cs => infabs_judge_size_conts cs
  | conts_inftappunion _ _ cs => infabs_judge_size_conts cs
  | conts_unioninftapp _ cs => infabs_judge_size_conts cs
  | conts_sub _ => 0
  end
with infabs_judge_size_contd (cd : contd) : nat :=
  match cd with
  | contd_infabsunion _ cd => 3 + infabs_judge_size_contd cd
  | contd_infapp _ _ cs => infabs_judge_size_conts cs
  | contd_unioninfabs _ _ cd => 1 + infabs_judge_size_contd cd
  end.

Definition infabs_judge_size_work (w : work) : nat :=
  match w with
  | work_infer _ cs => infabs_judge_size_conts cs
  | work_check _ _ => 0
  | work_infabs _ cd => 1 + infabs_judge_size_contd cd
  | work_infabsunion _ _ _ cd => 3 + infabs_judge_size_contd cd
  | work_infapp _ _ _ cs => infabs_judge_size_conts cs
  | work_inftapp _ _ cs => infabs_judge_size_conts cs
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ cs => infabs_judge_size_conts cs
  | work_unioninftapp _ _ cs => infabs_judge_size_conts cs
  | work_unioninfabs _ _ _ _ cd => 1 + infabs_judge_size_contd cd
  | work_applys cs _ => infabs_judge_size_conts cs
  | work_applyd cd _ _ => infabs_judge_size_contd cd
  end.

Fixpoint infabs_judge_size_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0 
  | aworklist_constvar Γ' _ _ => infabs_judge_size_wl Γ'
  | aworklist_consvar Γ' _ _ => infabs_judge_size_wl Γ'
  | aworklist_conswork Γ' w => infabs_judge_size_work w + infabs_judge_size_wl Γ'
  end.

Fixpoint inftapp_judge_size_conts (cs : conts) : nat :=
  match cs with
  | conts_infabs cd => inftapp_judge_size_contd cd
  | conts_inftapp _ cs => 1 + inftapp_judge_size_conts cs
  | conts_inftappunion _ _ cs => 3 + inftapp_judge_size_conts cs
  | conts_unioninftapp _ cs => 1 + inftapp_judge_size_conts cs
  | conts_sub _ => 0
  end
with inftapp_judge_size_contd (cd : contd) : nat :=
  match cd with
  | contd_infabsunion _ cd => inftapp_judge_size_contd cd
  | contd_infapp _ _ cs => inftapp_judge_size_conts cs
  | contd_unioninfabs _ _ cd => inftapp_judge_size_contd cd
  end.

Definition inftapp_judge_size_work (w : work) : nat :=
  match w with
  | work_infer _ cs => inftapp_judge_size_conts cs
  | work_check _ _ => 0
  | work_infabs _ cd => inftapp_judge_size_contd cd
  | work_infabsunion _ _ _ cd => inftapp_judge_size_contd cd
  | work_infapp _ _ _ cs => inftapp_judge_size_conts cs
  | work_inftapp _ _ cs => 1 + inftapp_judge_size_conts cs
  | work_sub _ _ => 0
  | work_inftappunion _ _ _ cs => 3 + inftapp_judge_size_conts cs
  | work_unioninftapp _ _ cs => 1 + inftapp_judge_size_conts cs
  | work_unioninfabs _ _ _ _ cd => inftapp_judge_size_contd cd
  | work_applys cs _ => inftapp_judge_size_conts cs
  | work_applyd cd _ _ => inftapp_judge_size_contd cd
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

(* Lemma exp_size_wl_awl_app : forall Γ1 Γ2,
  exp_size_wl (awl_app Γ1 Γ2) = exp_size_wl Γ1 + exp_size_wl Γ2.
Proof.
  intros Γ1.
  induction Γ1; simpl; auto;
    try solve [intros; rewrite IHΓ1; simpl; lia].
Admitted
Qed. *)

Lemma exp_size_subst_tvar_in_exp_mono : forall Γ A X e,
  a_mono_typ (awl_to_aenv Γ) A ->
  exp_size Γ (subst_tvar_in_exp A X e) = exp_size Γ e
with body_size_subst_tvar_in_body_mono : forall Γ A X b,
  a_mono_typ (awl_to_aenv Γ) A ->
  body_size Γ (subst_tvar_in_body A X b) = body_size Γ b.
(* Proof.
  - intros Γ A X e Hmono.
  induction e; simpl; eauto.
  erewrite iu_size_subst_mono; eauto.
  - intros. destruct b. simpl. 
  erewrite iu_size_subst_mono; eauto. 
Qed. *)
Admitted.

Lemma exp_size_conts_subst_tvar_in_conts_mono : forall Γ X A c,
  a_mono_typ (awl_to_aenv Γ) A ->
  exp_size_conts Γ (subst_tvar_in_conts A X c) = exp_size_conts Γ c
with exp_size_contd_subst_tvar_in_contd_mono : forall Γ X A c,
  a_mono_typ (awl_to_aenv Γ) A ->
  exp_size_contd Γ (subst_tvar_in_contd A X c) = exp_size_contd Γ c.
Proof.
  intros Γ X A c Hmono.
  induction c; simpl; eauto.
  intros Γ X A c Hmono.
  induction c; simpl; eauto.
  erewrite exp_size_subst_tvar_in_exp_mono; eauto.
Qed.

Lemma exp_size_work_subst_tvar_in_work_mono : forall Γ X A w,
  a_mono_typ (awl_to_aenv Γ) A ->
  exp_size_work Γ (subst_tvar_in_work A X w) = exp_size_work Γ w.
Proof.
  intros Γ X A w Hmono.
  induction w; intros; simpl;
    try erewrite exp_size_subst_tvar_in_exp_mono;
    try erewrite exp_size_conts_subst_tvar_in_conts_mono;
    try erewrite exp_size_contd_subst_tvar_in_contd_mono;
    try erewrite iu_size_subst_mono; eauto.
Qed.

Lemma exp_size_wl_subst_tvar_in_aworklist_mono : forall Γ Γ' X A,
  a_mono_typ Γ' A ->
  exp_size_wl (subst_tvar_in_aworklist A X Γ) = exp_size_wl Γ.
(* Proof.
  intros Γ.
  induction Γ; intros; simpl in *;
    try erewrite exp_size_work_subst_tvar_in_work_mono; eauto.
Qed.  *)
Admitted.

(* Lemma exp_size_wl_aworklist_subst : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  exp_size_wl Γ = exp_size_wl Γ1 + exp_size_wl Γ2.
Admitted. *)

Lemma judge_size_wl_awl_app : forall Γ1 Γ2,
  judge_size_wl (awl_app Γ1 Γ2) = judge_size_wl Γ1 + judge_size_wl Γ2.
Proof.
  intros Γ1.
  induction Γ1; simpl; auto;
    try solve [intros; rewrite IHΓ1; simpl; lia].
Qed.

Lemma judge_size_conts_subst_tvar_in_conts : forall X A c,
  judge_size_conts (subst_tvar_in_conts A X c) = judge_size_conts c
with judge_size_contd_subst_tvar_in_contd : forall X A c,
  judge_size_contd (subst_tvar_in_contd A X c) = judge_size_contd c.
Proof.
  intros X A c.
  induction c; simpl; eauto.
  intros X A c.
  induction c; simpl; eauto.
  erewrite judge_size_conts_subst_tvar_in_conts; eauto.
Qed.

Lemma judge_size_work_subst_tvar_in_work : forall X A w,
  judge_size_work (subst_tvar_in_work A X w) = judge_size_work w.
Proof.
  intros X A w.
  induction w; intros; simpl;
    try erewrite judge_size_conts_subst_tvar_in_conts;
    try erewrite judge_size_contd_subst_tvar_in_contd; eauto.
Qed.

Lemma judge_size_wl_subst_tvar_in_aworklist : forall Γ X A,
  judge_size_wl (subst_tvar_in_aworklist A X Γ) = judge_size_wl Γ.
Proof.
  intros Γ.
  induction Γ; intros; simpl in *;
    try erewrite judge_size_work_subst_tvar_in_work; eauto.
Qed. 

Lemma judge_size_wl_aworklist_subst : forall Γ X A Γ1 Γ2,
  aworklist_subst Γ X A Γ1 Γ2 ->
  judge_size_wl Γ = judge_size_wl Γ1 + judge_size_wl Γ2.
Admitted.

(* Lemma measp_wl_aworklist_subst : forall Γ X A E Γ1 Γ2 n,
  aworklist_subst Γ X A E Γ1 Γ2 ->
  measp_wl Γ n ->
  measp_wl
    (awl_app (subst_tvar_in_aworklist A X Γ2)
      (awl_app (etvar_list_to_awl E) Γ1)) n.
Proof.
  intros Γ X A E Γ1 Γ2 n Hsubst Hmeas.
  induction Hsubst; simpl.
  (* rev? *)
Abort. *)

Lemma apply_conts_det : forall c A w1 w2,
  apply_conts c A w1 -> apply_conts c A w2 -> w1 = w2.
Proof.
  intros c A w1 w2 Happly1 Happly2.
  induction Happly1; dependent destruction Happly2; eauto.
Qed.

Lemma apply_contd_det : forall c A B w1 w2,
  apply_contd c A B w1 -> apply_contd c A B w2 -> w1 = w2.
Proof.
  intros c A B w1 w2 Happly1 Happly2.
  induction Happly1; dependent destruction Happly2; eauto.
Qed.

Lemma apply_conts_dec : forall c A,
  (exists w, apply_conts c A w) \/ ((exists w, apply_conts c A w) -> False).
Proof.
  intros c A.
  destruct c; eauto using apply_conts.
Qed.

Lemma apply_contd_dec : forall c A B,
  (exists w, apply_contd c A B w) \/ ((exists w, apply_contd c A B w) -> False).
Proof.
  intros c A B.
  destruct c; eauto using apply_contd.
Admitted.

Lemma apply_conts_exp_size : forall Γ c A w,
  apply_conts c A w -> exp_size_work Γ w = exp_size_conts Γ c.
Proof.
  intros Γ c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_contd_exp_size : forall Γ c A B w,
  apply_contd c A B w -> exp_size_work Γ w <= exp_size_contd Γ c.
Proof.
  intros Γ c A B w Happly.
  induction Happly; simpl; eauto; try lia.
  (* safe *)
Admitted.

Lemma apply_conts_judge_size : forall c A w,
  apply_conts c A w -> judge_size_work w = judge_size_conts c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_contd_judge_size : forall c A B w,
  apply_contd c A B w -> judge_size_work w = judge_size_contd c.
Proof.
  intros c A B w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_contd_infabs_depth : forall c A B w,
  apply_contd c A B w -> infabs_depth_work w = infabs_depth_contd c.
Proof.
  intros c A B w Happly.
  dependent destruction Happly; simpl; eauto.
Qed.

Lemma inftapp_depth_conts_tail_rec_le : forall c ans1 ans2,
  ans1 <= ans2 ->
  inftapp_depth_conts_tail_rec c ans1 <= inftapp_depth_conts_tail_rec c ans2
with inftapp_depth_contd_tail_rec_le : forall c ans1 ans2,
  ans1 <= ans2 ->
  inftapp_depth_contd_tail_rec c ans1 <= inftapp_depth_contd_tail_rec c ans2.
Proof.
  intros c.
  induction c; intros; simpl; eauto; try eapply IHc; try lia.
  assert (inftapp_depth A * ans1 <= inftapp_depth A * ans2).
  { eapply mult_le_compat; eauto. } lia.
  intros c.
  induction c; intros; simpl; eauto; try eapply IHc; try lia.
Qed.

Lemma inftapp_depth_conts_tail_rec_lt : forall c ans1 ans2,
  ans1 < ans2 ->
  inftapp_depth_conts_tail_rec c ans1 < inftapp_depth_conts_tail_rec c ans2
with inftapp_depth_contd_tail_rec_lt : forall c ans1 ans2,
  ans1 < ans2 ->
  inftapp_depth_contd_tail_rec c ans1 < inftapp_depth_contd_tail_rec c ans2.
Proof.
  intros c.
  induction c; intros; simpl; eauto; try eapply IHc; try lia.
  assert (inftapp_depth A * ans1 <= inftapp_depth A * ans2).
  { eapply mult_le_compat; eauto. lia. } lia.
  intros c.
  induction c; intros; simpl; eauto; try eapply IHc; try lia.
Qed.

Lemma apply_contd_inftapp_depth : forall c A B w,
  apply_contd c A B w -> inftapp_depth_work w <= inftapp_depth_contd_tail_rec c 0.
Proof.
  intros c A B w Happly.
  dependent destruction Happly; try solve [simpl; eauto].
Qed.

Lemma apply_conts_inftapp_depth_bot : forall c w,
  apply_conts c typ_bot w -> inftapp_depth_work w <= inftapp_depth_conts_tail_rec c 0.
Proof.
  intros c w Happly.
  dependent destruction Happly; simpl; eauto.
  simpl. eapply inftapp_depth_conts_tail_rec_le; lia.
Qed.

Lemma apply_contd_infabs_judge_size : forall c A B w,
  apply_contd c A B w -> infabs_judge_size_work w = infabs_judge_size_contd c.
Proof.
  intros c A B w Happly.
  induction Happly; simpl; eauto.
Qed. 

Lemma apply_conts_infabs_judge_size : forall c A w,
  apply_conts c A w -> infabs_judge_size_work w = infabs_judge_size_conts c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_contd_inftapp_judge_size : forall c A B w,
  apply_contd c A B w -> inftapp_judge_size_work w = inftapp_judge_size_contd c.
Proof.
  intros c A B w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_conts_inftapp_judge_size : forall c A w,
  apply_conts c A w -> inftapp_judge_size_work w = inftapp_judge_size_conts c.
Proof.
  intros c A w Happly.
  induction Happly; simpl; eauto.
Qed.

Lemma apply_conts_inftapp_depth : forall c A w,
  apply_conts c A w -> inftapp_depth_work w <= inftapp_depth_conts_tail_rec c (inftapp_depth A).
Proof.
  intros c A w Happly.
  induction Happly; simpl;
    try eapply inftapp_depth_conts_tail_rec_le;
    try eapply inftapp_depth_contd_tail_rec_le; try lia.
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

Lemma a_wf_wl_apply_contd : forall Γ w A B cd,
  apply_contd cd A B w ->
  a_wf_wl (work_applyd cd A B ⫤ᵃ Γ) ->
  a_wf_wl (w ⫤ᵃ Γ).
Proof with eauto.
  intros. induction H; destruct_a_wf_wl...
Qed.


Lemma a_wf_wl_binds_etvar_aworklist_subst_dec' : forall Γ1 Γ2 X A,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  (exists Γ'1 Γ'2, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2) \/ ~ (exists Γ'1 Γ'2, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2).
Proof with eauto.
  intros. generalize dependent Γ1. induction Γ2.
  - left. exists Γ1, aworklist_empty. simpl. constructor.
  - intros. dependent destruction H.
    apply IHΓ2 in H1. destruct H1.
    + destruct H1 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (x ~ᵃ A0;ᵃ Γ'2). simpl...
    + right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
      dependent destruction Hsubst. eauto.
  - intros. assert (X0 `in` ftvar_in_typ A \/ (~ X0 `in` ftvar_in_typ A)) by fsetdec. 
    dependent destruction H. 
    + apply IHΓ2 in H0. destruct H1.
      * right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
        dependent destruction Hsubst. contradiction. 
      * destruct H0. 
        -- destruct H0 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (X0 ~ᵃ □ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst. eauto.
    + apply IHΓ2 in H0. destruct H1.
      * right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
        dependent destruction Hsubst. contradiction.
      * destruct H0. 
        -- destruct H0 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (X0 ~ᵃ ■ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst. eauto.
    + destruct H1.
      * assert (⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X0 ~ᵃ ⬒ ;ᵃ Γ1)) by (eapply a_wf_wl_move_etvar_back; eauto).
        apply IHΓ2 in H2. destruct H2.
        -- destruct H2 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, Γ'2. simpl...
           constructor...  rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst.
           ++ rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X0.
           ++ contradiction.
           ++ apply worklist_split_etvar_det in x...
              destruct x; subst.
              eauto.
              assert (X ∉ union (dom (awl_to_aenv Γ1)) (dom (awl_to_aenv Γ2))) by (eapply a_wf_wl_tvar_notin_remaining; eauto)...
      * apply IHΓ2 in H0. destruct H0.
        -- left. destruct H0 as [Γ'1 [Γ'2 Hsubst]]. exists Γ'1, (X0 ~ᵃ ⬒ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst.
           ++ rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X0. 
           ++ eauto.
           ++ contradiction.
  - intros. dependent destruction H.
    apply IHΓ2 in H0. destruct H0.
    + destruct H0 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (w ⫤ᵃ Γ'2). simpl...
    + right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
      dependent destruction Hsubst. 
      assert ((∃ Γ'1 Γ'2 : aworklist, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2)) by eauto.
      contradiction.
Qed.

Lemma a_wf_wl_binds_etvar_aworklist_subst_dec : forall Γ X A,
  ⊢ᵃʷ Γ -> 
  binds X abind_etvar_empty (awl_to_aenv Γ) ->
  (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2) \/ ~ (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2).
Proof with eauto. 
  intros. apply aworklist_binds_split in H0... destruct H0 as [Γ1 [Γ2 Hsplit]]...
  subst. apply a_wf_wl_binds_etvar_aworklist_subst_dec'...
Qed.

Lemma aworklist_subst_no_etvar_false : forall Γ Γ1 Γ2 X A,
  ⊢ᵃʷ Γ ->
  (binds X abind_etvar_empty (awl_to_aenv Γ) -> False) ->
  aworklist_subst Γ X A Γ1 Γ2 -> False.
Proof with eauto.
  intros. dependent induction H1.
  - assert (binds X abind_etvar_empty (awl_to_aenv (X ~ᵃ ⬒ ;ᵃ Γ))).
    { simpl. constructor; auto. } auto.
  - apply IHaworklist_subst.
    + dependent destruction H...
    + intros. apply H0. simpl...
  - apply IHaworklist_subst.
    + dependent destruction H...
    + intros. apply H0. simpl...
  - apply IHaworklist_subst.
    + dependent destruction H...
    + intros. apply H0. simpl...  
  - apply IHaworklist_subst.
    + dependent destruction H...
    + intros. apply H0. simpl...  
    - apply IHaworklist_subst.
    + dependent destruction H...
    + intros. apply H0. simpl...
  - apply IHaworklist_subst.
    + eapply a_wf_wl_move_etvar_back; eauto. 
    + intros. apply H0. simpl...
      rewrite awl_to_aenv_app. simpl... 
Qed.


Lemma typ_eq_bool : forall (A1 A2:typ),
  sumbool (A1 = A2) (A1 <> A2).
Proof.
  intro A1. induction A1; intro A2; induction A2; eauto;
    try solve [right; unfold not; intros Hcontra; inversion Hcontra].
  - destruct (n == n0); auto.
    right. unfold not. intros. inversion H. contradiction. 
  - destruct (X == X0); subst. auto.
    right. unfold not. intros. inversion H. contradiction. 
  - pose proof (IHA1_1 A2_1).
    pose proof (IHA1_2 A2_2).
    destruct H; destruct H0; subst; eauto;  
      right; unfold not; intros Hcontra; inversion Hcontra; contradiction. 
  - pose proof (IHA1 A2). destruct H.
    + subst. auto.
    + right. unfold not. intros Hcontra. dependent destruction Hcontra. contradiction.
  - pose proof (IHA1_1 A2_1).
    pose proof (IHA1_2 A2_2).
    destruct H; destruct H0; subst; eauto;  
      right; unfold not; intros Hcontra; inversion Hcontra; contradiction.
  - pose proof (IHA1_1 A2_1).
    pose proof (IHA1_2 A2_2).
    destruct H; destruct H0; subst; eauto;  
      right; unfold not; intros Hcontra; inversion Hcontra; contradiction.  
Qed.

Lemma a_bind_eq_bool : forall (b1 b2:abind),
  sumbool (b1 = b2) (b1 <> b2).
Proof.
  intros. destruct b1; destruct b2; eauto;
    try solve [right; unfold not; intros Hcontra; inversion Hcontra].
  - pose proof (typ_eq_bool A A0).
    destruct H; subst; eauto;
      right; unfold not; intros Hcontra; inversion Hcontra; contradiction.
Qed.


Lemma a_wf_wl_aworklist_subst_dec : forall Γ X A,
  ⊢ᵃʷ Γ -> 
  (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2) \/ ~ (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2).
Proof.
  intros.
  assert (sumbool (binds X abind_etvar_empty (awl_to_aenv Γ)) (~ binds X abind_etvar_empty (awl_to_aenv Γ))). {
    apply binds_dec. apply a_bind_eq_bool.
  }
  destruct H0.
  - apply a_wf_wl_binds_etvar_aworklist_subst_dec; eauto.
  - right. unfold not. intros. destruct H0 as [Γ1 [Γ2 Hsubst]]. 
    eapply aworklist_subst_no_etvar_false; eauto.
Qed.

Lemma exp_size_wl_aworklist_subst' : forall Γ2 Γ X A Γ1 Γ1' Γ2',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (awl_to_aenv Γ) A ->
  exp_size_wl (subst_tvar_in_aworklist A X Γ2' ⧺ Γ1') = exp_size_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof.
  intros Γ2. induction Γ2; intros;
    dependent destruction H0; dependent destruction H; simpl in *; eauto;
    try solve [exfalso; eauto].
  - eapply worklist_split_etvar_det in x. destruct x. subst.
    eapply IHΓ2 in H1; eauto.
Admitted.

Lemma exp_size_wl_aworklist_subst : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷ Γ -> 
  aworklist_subst Γ X A Γ1 Γ2 -> a_mono_typ (awl_to_aenv Γ) A ->
  exp_size_wl (subst_tvar_in_aworklist A X Γ2 ⧺ Γ1) = exp_size_wl Γ.
Admitted.



Lemma decidablity_lemma : forall ne nj nt ntj na naj nm nw Γ m,
  ⊢ᵃʷ Γ ->
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
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction Hm. simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHnw; eauto; lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction H.
    + dependent destruction Hm.
      dependent destruction H; simpl in *.
      * assert (Jg: a_wl_red (work_applys cs typ_unit ⫤ᵃ Γ) \/
                  ~ a_wl_red (work_applys cs typ_unit ⫤ᵃ Γ)).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; auto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * assert (Jg: a_wl_red (work_applys cs A ⫤ᵃ Γ) \/
                  ~ a_wl_red (work_applys cs A ⫤ᵃ Γ)).
        { eapply IHne; eauto; simpl; try lia. admit. (* safe: wf *) }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply binds_unique with (b:= (abind_var_typ A0)) in H; auto. dependent destruction H.
        subst. apply Jg; auto.
      * right. intro Hcontra.
        dependent destruction Hcontra.
        admit. (* TODO *)
      * assert (Jg:   (work_infer e1 (conts_infabs (contd_infapp (exp_split_size (awl_to_aenv Γ) e1) e2 cs)) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                    ¬ (work_infer e1 (conts_infabs (contd_infapp (exp_split_size (awl_to_aenv Γ) e1) e2 cs)) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * destruct body5. admit.
        (* TODO *)
      * simpl in *.
        assert (Jg:   (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                    ¬ (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * simpl in *.
        assert (Jg:   (work_check e A ⫤ᵃ work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                    ¬ (work_check e A ⫤ᵃ work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { assert (exp_size (work_applys cs A ⫤ᵃ Γ) e = exp_size Γ e) by admit.
          eapply IHne; eauto; simpl; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
    + dependent destruction Hm. simpl in *.
      assert (He': exp_size Γ e >= 1) by apply exp_size_gt_0.
      assert (Jg:   (work_infer e (conts_sub A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                  ¬ (work_infer e (conts_sub A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHnj; eauto; simpl; try lia. }
      assert (Jg1: forall A1 A2, A = typ_union A1 A2 ->
                (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
        eapply IHne; eauto; simpl; try lia. }
      assert (Jg2: forall A1 A2, A = typ_union A1 A2 ->
                (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
        eapply IHne; eauto; simpl; try lia. }
      assert (Jg': forall A1 A2, A = typ_intersection A1 A2 ->
                 (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅
            \/ ¬ (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ ).
      { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
        assert (exp_size (work_check e A1 ⫤ᵃ Γ) e = exp_size Γ e) by admit.
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
        -- inst_cofinites_by (L `union` (ftvar_in_typ T) `union` (ftvar_in_aworklist Γ)).
           assert (Jgt:   (work_check (e ^ᵉₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                        ¬ (work_check (e ^ᵉₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia. admit. (* safe: wf *)
             assert (Hexp: exp_size (x ~ᵃ typ_bot;ᵃ Γ) (e ^ᵉₑ exp_var_f x) = exp_size Γ e) by admit. (* should be fine *)
             lia. }
           destruct Jgt as [Jgt | Jgt].
           ++ left. eapply a_wl_red__chk_abstop with (L := L `union` (ftvar_in_typ T) `union` (ftvar_in_aworklist Γ)).
              intros x' Hnin. admit. (* TODO: rename var *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** apply Jg; auto.
              ** admit. (* TODO: rename var  *) 
        -- right. intro Hcontra. dependent destruction Hcontra.
           ++ eapply Jg; eauto.
           ++ admit. (* safe: wf *)
        -- right. intro Hcontra. dependent destruction Hcontra.
           ++ eapply Jg; eauto.
           ++ eapply abind_etvar_stvar_false; eauto.
        -- right. intro Hcontra. dependent destruction Hcontra; eauto.
           admit. (* TODO *)
        -- pick fresh x.
           assert (JgArr:   (work_check (e ^ᵉₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                          ¬ (work_check (e ^ᵉₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia. admit. (* safe: wf *)
             assert (Hexp: exp_size (x ~ᵃ A1;ᵃ Γ) (e ^ᵉₑ exp_var_f x) = exp_size Γ e) by admit. (* should be fine *)
             rewrite Hexp. lia. } 
           destruct JgArr as [JgArr | JgArr]; auto.
           ++ left. eapply a_wl_red__chk_absarrow with (L := union L (union (ftvar_in_typ T) (union (ftvar_in_typ A1) (ftvar_in_typ A2)))); eauto.
              intros x' Hnin.              
              admit. (* TODO: rename var *)
           ++ right. intro Hcontra. dependent destruction Hcontra.
              ** apply Jg; auto.
              ** admit. (* TODO: rename var *) 
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
        dependent destruction H1; simpl in *;
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
      * assert (Jg:   (work_infabs (typ_arrow typ_top typ_bot) cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                    ¬ (work_infabs (typ_arrow typ_top typ_bot) cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
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
      * destruct (apply_contd_dec cd A1 A2) as [[w Happly] | Happly];
          try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
                     eapply Happly; eauto].
        assert (Jg: a_wl_red (aworklist_conswork Γ w) \/ 
                    ~ a_wl_red (aworklist_conswork Γ w)).
        { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
          admit. (* safe: wf *)
          eapply IHnaj; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          eapply apply_contd_exp_size with (Γ := Γ) in Happly; lia.
          eapply apply_contd_judge_size in Happly; lia.
          eapply apply_contd_inftapp_depth in Happly; lia.
          admit. (* TODO *)
          eapply apply_contd_infabs_depth in Happly; lia.
          admit. (* TODO *) }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        dependent destruction Hcontra.
        eapply apply_contd_det in Happly; eauto.
        subst. eauto.
      * pick fresh X. inst_cofinites_with X.
        assert (Jg: a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) cd)) \/
                    ~ a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_etvar_empty) (work_infabs (open_typ_wrt_typ A (typ_var_f X)) cd))).
        { assert (Heq: infabs_depth (open_typ_wrt_typ A (typ_var_f X)) = infabs_depth A) by admit. (* should be fine *)
          eapply IHna; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          admit. (* TODO *) }
        destruct Jg as [Jg | Jg]; eauto.
        -- left. inst_cofinites_for a_wl_red__infabs_all.
           intros X' Hnin. 
           apply a_wl_red_rename_tvar with (X:=X) (X':=X') in Jg.
           ++ simpl in Jg.
              unfold eq_dec in Jg.
              destruct (EqDec_eq_of_X X X) in Jg.
              ** rewrite rename_tvar_in_aworklist_fresh_eq in Jg; auto.
                 rewrite subst_tvar_in_contd_fresh_eq in Jg; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in Jg; auto.
              ** contradiction.
            ++ admit.
            ++ admit. (* wf *)
            ++ simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- right. intro Hcontra.
           dependent destruction Hcontra.
           pick fresh X1.
           inst_cofinites_with X1.
           apply a_wl_red_rename_tvar with (X:=X1) (X':=X) in H2; auto.
           ++ simpl in H2.
              unfold eq_dec in H2.
              destruct (EqDec_eq_of_X X1 X1) in H2.
              ** rewrite rename_tvar_in_aworklist_fresh_eq in H2; auto.
                  rewrite subst_tvar_in_contd_fresh_eq in H2; auto.
                  rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H2; auto.
              ** contradiction.
            ++ admit. (* wf *)  
            ++ simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
      * assert (Jg: a_wl_red (aworklist_conswork Γ (work_infabs A1  (  (contd_infabsunion A2 cd)  ) )) \/
                  ~ a_wl_red (aworklist_conswork Γ (work_infabs A1  (  (contd_infabsunion A2 cd)  ) ))).
        { eapply IHna; eauto; simpl in *; try lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * assert (Jg1: a_wl_red (aworklist_conswork Γ (work_infabs A1 cd)) \/
                   ~ a_wl_red (aworklist_conswork Γ (work_infabs A1 cd))).
        { eapply IHna; eauto; simpl in *; try lia. }
        assert (Jg2: a_wl_red (aworklist_conswork Γ (work_infabs A2 cd)) \/
                   ~ a_wl_red (aworklist_conswork Γ (work_infabs A2 cd))).
        { eapply IHna; eauto; simpl in *; try lia. }
        destruct Jg1 as [Jg1 | Jg1]; eauto.
        destruct Jg2 as [Jg2 | Jg2]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg1; auto. apply Jg2; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      assert (Jg:  (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                 ¬ (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHnaj; eauto; simpl in *; try lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra. 
      dependent destruction Hcontra. eauto.
    + dependent destruction H; try solve [right; intro Hcontra; dependent destruction Hcontra].
      assert (Jg:  (work_applys cs B ⫤ᵃ work_check e A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                 ¬ (work_applys cs B ⫤ᵃ work_check e A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHnj; eauto; simpl in *; try lia. admit. admit. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra. eauto.
    + simpl in *. dependent destruction Hm. dependent destruction H2.
      dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      * destruct (apply_conts_dec cs typ_bot) as [[w Happly] | Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: a_wl_red (aworklist_conswork Γ w) \/
                  ~ a_wl_red (aworklist_conswork Γ w)).
        { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
          admit. (* safe: wf *)
          eapply IHntj; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          eapply apply_conts_exp_size with (Γ := Γ) in Happly; lia.
          eapply apply_conts_judge_size in Happly; lia.
          (* eapply apply_conts_inftapp_depth_bot in Happly. *)
          admit. (* TODO *)
          eapply apply_conts_inftapp_judge_size in Happly; lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        dependent destruction Hcontra.
        eapply apply_conts_det in Happly; eauto.
        subst. eauto.
      * destruct (apply_conts_dec cs (open_typ_wrt_typ A A2)) as [[w Happly] | Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
          admit. (* safe: wf *)
          eapply IHntj; eauto; simpl in *; try lia.
          admit. (* safe: wf *)
          eapply apply_conts_exp_size with (Γ := Γ) in Happly; lia.
          eapply apply_conts_judge_size in Happly; lia.
          eapply apply_conts_inftapp_depth in Happly.
          assert (Hfact: inftapp_depth (open_typ_wrt_typ A A2) < (1 + inftapp_depth A) * (1 + inftapp_depth A2))
            by eapply inftapp_depth_open_typ_wrt_typ.
          assert (Hfact': inftapp_depth_work w <= inftapp_depth_conts_tail_rec cs ((1 + inftapp_depth A) * (1 + inftapp_depth A2))).
          { eapply le_trans; eauto. eapply inftapp_depth_conts_tail_rec_le. lia. }
          assert (Hfact'': inftapp_depth_conts_tail_rec cs ((1 + inftapp_depth A) * (1 + inftapp_depth A2)) <= inftapp_depth_conts_tail_rec cs
          (S
             (inftapp_depth A +
              S
                (inftapp_depth A +
                 inftapp_depth A2 * S (inftapp_depth A))))).
          { eapply inftapp_depth_conts_tail_rec_le; eauto; lia. }
          lia.
          eapply apply_conts_inftapp_judge_size in Happly; lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        dependent destruction Hcontra.
        eapply apply_conts_det in Happly; eauto.
        subst. eauto.
      * assert (Jg:   (work_inftapp A1 A2 (conts_inftappunion A0 A2 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                    ¬ (work_inftapp A1 A2 (conts_inftappunion A0 A2 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHnt; eauto; simpl in *; try lia.
          assert (inftapp_depth_conts_tail_rec cs
          (inftapp_depth A0 * S (S (inftapp_depth A2)) + 1 +
           (inftapp_depth A1 +
            (inftapp_depth A1 + inftapp_depth A2 * inftapp_depth A1)))
            < inftapp_depth_conts_tail_rec cs
            (S
               (inftapp_depth A1 + inftapp_depth A0 +
                S
                  (inftapp_depth A1 + inftapp_depth A0 +
                   inftapp_depth A2 *
                   S (inftapp_depth A1 + inftapp_depth A0))))).
          { eapply inftapp_depth_conts_tail_rec_lt; eauto; try lia. }
          lia. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg; auto.
      * assert (Jg1: (work_inftapp A1 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (work_inftapp A1 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHnt; eauto; simpl in *; try lia.
          assert (inftapp_depth_conts_tail_rec cs
          (inftapp_depth A1 +
           (inftapp_depth A1 + inftapp_depth A2 * inftapp_depth A1))
                    <  inftapp_depth_conts_tail_rec cs
                    (S
                       (inftapp_depth A1 + inftapp_depth A0 +
                        S
                          (inftapp_depth A1 + inftapp_depth A0 +
                           inftapp_depth A2 *
                           S (inftapp_depth A1 + inftapp_depth A0))))).
          { eapply inftapp_depth_conts_tail_rec_lt; eauto; try lia. }
          lia. }
        assert (Jg2: (work_inftapp A0 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (work_inftapp A0 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHnt; eauto; simpl in *; try lia.
          assert (inftapp_depth_conts_tail_rec cs
          (inftapp_depth A0 +
           (inftapp_depth A0 + inftapp_depth A2 * inftapp_depth A0))
                    < inftapp_depth_conts_tail_rec cs
                    (S
                       (inftapp_depth A1 + inftapp_depth A0 +
                        S
                          (inftapp_depth A1 + inftapp_depth A0 +
                           inftapp_depth A2 *
                           S (inftapp_depth A1 + inftapp_depth A0))))).
          { eapply inftapp_depth_conts_tail_rec_lt; eauto; try lia. }
          lia. }
        destruct Jg1 as [Jg1 | Jg1]; eauto.
        destruct Jg2 as [Jg2 | Jg2]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra.
        apply Jg1; auto. apply Jg2; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H3.
      assert (Jg:  (work_inftapp A2 B (conts_unioninftapp A1 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                 ¬ (work_inftapp A2 B (conts_unioninftapp A1 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHntj; eauto; simpl; try lia.
        assert (inftapp_depth_conts_tail_rec cs
        (S
           (inftapp_depth A1 +
            (inftapp_depth A2 +
             (inftapp_depth A2 + inftapp_depth B * inftapp_depth A2))))
             <= inftapp_depth_conts_tail_rec cs
             (inftapp_depth A1 +
              inftapp_depth A2 * S (S (inftapp_depth B)) + 1)).
          { eapply inftapp_depth_conts_tail_rec_le; eauto; try lia. }
        lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + simpl in *. dependent destruction Hm. dependent destruction H2.
      destruct (apply_conts_dec cs (typ_union A1 A2)) as [[w Happly] | Happly];
      try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
        eapply Happly; eauto].
      assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { destruct (measp_wl_total (aworklist_conswork Γ w)) as [m Hm'].
        admit. (* safe: wf *)
        eapply IHntj; eauto; simpl in *; try lia.
        admit. (* safe: wf *)
        eapply apply_conts_exp_size with (Γ := Γ) in Happly; lia.
        eapply apply_conts_judge_size in Happly; lia.
        eapply apply_conts_inftapp_depth in Happly.
        assert (inftapp_depth_conts_tail_rec cs
        (inftapp_depth (typ_union A1 A2)) <= inftapp_depth_conts_tail_rec cs
        (S (inftapp_depth A1 + inftapp_depth A2))). 
        { eapply inftapp_depth_conts_tail_rec_le; eauto; lia. }
        lia.
        eapply apply_conts_inftapp_judge_size in Happly; lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      dependent destruction Hcontra.
      eapply apply_conts_det in Happly; eauto.
      subst. eauto.
    + simpl in *. dependent destruction Hm. dependent destruction H2.
      dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra];
      dependent destruction H1;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      destruct (apply_contd_dec cd ( (typ_intersection A1 A2) )   ( (typ_union B1 B2) ) ) as [[w Happly] | Happly];
      try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
        eapply Happly; eauto].
      assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { destruct (measp_wl_total (w ⫤ᵃ Γ)) as [m Hm'].
        admit. (* safe: wf *)
        eapply IHnaj; eauto; simpl in *; try lia.
        admit. (* safe: wf *)
        eapply apply_contd_exp_size with (Γ := Γ) in Happly; lia.
        eapply apply_contd_judge_size in Happly; lia.
        (* eapply apply_contd_inftapp_all_size_arr in Happly; lia. *)
        eapply apply_contd_inftapp_depth in Happly; lia.
        eapply apply_contd_inftapp_judge_size in Happly; lia.
        eapply apply_contd_infabs_depth in Happly; lia.
        eapply apply_contd_infabs_judge_size in Happly; lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      dependent destruction Hcontra.
      eapply apply_contd_det in Happly; eauto.
      subst. eauto.
    + simpl in *. dependent destruction Hm. dependent destruction H1.
      dependent destruction H1. dependent destruction H3.
      assert (Hw': weight A >= 1) by apply weight_gt_0.
      assert (Hw'0: weight A0 >= 1) by apply weight_gt_0.
      assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
      { eapply IHnw; eauto; simpl; try lia. }
      assert (JgInter1: forall A1 A2, A0 = typ_intersection A1 A2 ->
          (work_sub A A2 ⫤ᵃ work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ¬ (work_sub A A2 ⫤ᵃ work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
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
        assert (Heq: iu_size (typ_all A1) = iu_size (A1 ^ᵗ X)) by admit. (* safe *)
        eapply IHnw with (m := (3 * n0 + all_size (A1 ^ᵗ X)) * (1 + iu_size A0) +
                                (3 * m0 + all_size A0) * (1 + iu_size (A1 ^ᵗ X)) + S n); eauto; try lia.
        admit. (* safe: wf *)
        eapply measp_wl_conswork; eauto.
        assert (Heq': all_size (typ_all A1) = all_size (A1 ^ᵗ X) + 1) by admit. (* safe *)
        rewrite Heq in Hlt. rewrite Heq' in Hlt. lia.
        assert (Heq': weight (A1 ^ᵗ X) = weight A1) by admit. (* safe *)
        assert (Hgt: weight A0 >= 1) by apply weight_gt_0.
        simpl in *. rewrite <- Heq. rewrite Heq'. lia. }
      assert (JgInst1: forall (Γ1 Γ2:aworklist) (X:typvar),
                A = typ_var_f X ->
                binds X abind_etvar_empty (awl_to_aenv Γ) ->
                a_mono_typ (awl_to_aenv Γ) A0 ->
                aworklist_subst Γ X A0 Γ1 Γ2 ->
                (subst_tvar_in_aworklist A0 X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅ \/
              ~ (subst_tvar_in_aworklist A0 X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅).
      { intros Γ1 Γ2 X Heq Hbin Hmono Hsub. subst.
        eapply IHnm; eauto; simpl in *; try lia.
        admit. (* safe: wf *)
        erewrite exp_size_wl_aworklist_subst; eauto.
        admit. (* TODO: should be fine *)
        admit. (* TODO: should be fine *)
        admit. (* TODO: should be fine *)
        admit. (* TODO: should be fine *)
        admit. (* TODO: should be fine *)
        admit. admit. (* TODO: should be fine *)
      } 
      assert (JgInst2: forall (Γ1 Γ2:aworklist) (X:typvar),
                A0 = typ_var_f X ->
                binds X abind_etvar_empty (awl_to_aenv Γ) ->
                a_mono_typ (awl_to_aenv Γ) A ->
                aworklist_subst Γ X A Γ1 Γ2 ->
                (subst_tvar_in_aworklist A X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅ \/
              ~ (subst_tvar_in_aworklist A X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅) by admit.
      (* { intros E Γ1 Γ2 X Heq Hbin Hmono Hsub. subst.
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
      } *)
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
        -- destruct (a_wf_wl_aworklist_subst_dec Γ X typ_unit) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
           ++ edestruct JgInst2 as [JgInst2' | JgInst2']; eauto.
              right. intro Hcontra. dependent destruction Hcontra.
              assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
              { eapply aworklist_subst_det; eauto. }
              destruct Heq as [Heq1 Heq2]. subst. eauto.
           ++ right. intro Hcontra. dependent destruction Hcontra.
              eapply Hsubst; eauto.
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
      * dependent destruction H0; try unify_binds;
          try solve [destruct Jg as [Jg | Jg]; eauto;
            right; intro Hcontra; dependent destruction Hcontra; try unify_binds;
            eapply Jg; eauto].
        -- destruct (eq_dec X X0) as [Heq | Hneq]; subst.
           ++ destruct Jg as [Jg | Jg]; eauto.
              right; intro Hcontra; dependent destruction Hcontra; try unify_binds.
           ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
        -- destruct (eq_dec X X0) as [Heq | Hneq]; subst; try unify_binds. 
           destruct (a_wf_wl_aworklist_subst_dec Γ X0 (` X)) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
           ++ edestruct JgInst2 as [JgInst2' | JgInst2']; eauto.
              right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
              assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
              { eapply aworklist_subst_det; eauto. }
              destruct Heq as [Heq1 Heq2]. subst. eauto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           eapply JgInter1'; eauto.
      * dependent destruction H0; try unify_binds;
          try solve [destruct Jg as [Jg | Jg]; eauto;
            right; intro Hcontra; dependent destruction Hcontra; try unify_binds;
            eapply Jg; eauto].
        -- destruct (eq_dec X X0) as [Heq | Hneq]; subst.
           ++ destruct Jg as [Jg | Jg]; eauto.
              right; intro Hcontra; dependent destruction Hcontra; try unify_binds.
           ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
        -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           dependent destruction H6; try unify_binds.
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra; try unify_binds. eauto.
      * dependent destruction H0.
        -- destruct (a_wf_wl_aworklist_subst_dec Γ X typ_unit) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
           ++ edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
              right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
              assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
              { eapply aworklist_subst_det; eauto. }
              destruct Heq as [Heq1 Heq2]. subst. eauto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
        -- right; intro Hcontra; dependent destruction Hcontra; try unify_binds.
           dependent destruction H5.
        -- destruct Jg as [Jg | Jg]; eauto.
           right; intro Hcontra; dependent destruction Hcontra; try unify_binds; eauto.
           dependent destruction H5.
        -- destruct (eq_dec X X0) as [Heq | Hneq]; subst; try unify_binds. 
           destruct (a_wf_wl_aworklist_subst_dec Γ X (` X0)) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
           ++ edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
              right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
              assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
              { eapply aworklist_subst_det; eauto. }
              destruct Heq as [Heq1 Heq2]. subst. eauto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
        -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           dependent destruction H6; try unify_binds.
        -- destruct (eq_dec X X0) as [Heq | Hneq]; subst; try unify_binds.
           ++ destruct Jg as [Jg | Jg]; eauto.
              right; intro Hcontra; dependent destruction Hcontra;
                try unify_binds; simpl in *; eauto.
           ++ destruct (a_wf_wl_aworklist_subst_dec Γ X (` X0)) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
              ** edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
                 destruct (a_wf_wl_aworklist_subst_dec Γ X0 (` X)) as [[Γ1' [Γ2' Hsubst']] | Hsubst']; eauto.
                 --- edestruct JgInst2 as [JgInst2' | JgInst2']; eauto.
                     right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
                     +++ assert (Heq: Γ1' = Γ3 /\ Γ2' = Γ4).
                         { eapply aworklist_subst_det; eauto. }
                         destruct Heq as [Heq1 Heq2]. subst. eauto.
                     +++ assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
                         { eapply aworklist_subst_det; eauto. }
                         destruct Heq as [Heq1 Heq2]. subst. eauto.
                 --- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
                     assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
                     { eapply aworklist_subst_det; eauto. }
                     destruct Heq as [Heq1 Heq2]. subst. eauto.
              ** destruct (a_wf_wl_aworklist_subst_dec Γ X0 (` X)) as [[Γ1' [Γ2' Hsubst']] | Hsubst']; eauto.
                 --- edestruct JgInst2 as [JgInst2' | JgInst2']; eauto.
                     right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
                     assert (Heq: Γ1' = Γ1 /\ Γ2' = Γ2).
                     { eapply aworklist_subst_det; eauto. }
                     destruct Heq as [Heq1 Heq2]. subst. eauto.
                 --- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
        -- assert (FV: X ∉ ftvar_in_typ (typ_arrow A1 A2) \/ not (X ∉ ftvar_in_typ (typ_arrow A1 A2))) by fsetdec.
           destruct FV as [FV | FV]; eauto.
           destruct (a_mono_typ_dec Γ (typ_arrow A1 A2)); eauto.
           ++ destruct (a_wf_wl_aworklist_subst_dec Γ X (typ_arrow A1 A2)) as [[Γ1' [Γ2' Hsubst']] | Hsubst']; eauto.
              ** edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
                 right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
                 assert (Heq: Γ1' = Γ1 /\ Γ2' = Γ2).
                 { eapply aworklist_subst_det; eauto. }
                 destruct Heq as [Heq1 Heq2]. subst. eauto.
              ** right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           ++ pick fresh X1. pick fresh X2.
              destruct (a_wf_wl_aworklist_subst_dec (aworklist_conswork (aworklist_constvar (aworklist_constvar Γ X1 abind_etvar_empty) X2 abind_etvar_empty) (work_sub (typ_var_f X) (typ_arrow A1 A2))) X (typ_arrow (typ_var_f X1) (typ_var_f X2))) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
              admit. (* wf *)
              ** dependent destruction Hsubst. simpl in *.
                 assert (JgArr1: (work_sub (typ_arrow ` X1 ` X2) (typ_arrow A1 A2) ⫤ᵃ subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅ \/
                               ~ (work_sub (typ_arrow ` X1 ` X2) (typ_arrow A1 A2) ⫤ᵃ subst_tvar_in_aworklist (typ_arrow ` X1 ` X2) X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅).
                 { admit. }          
                 dependent destruction JgArr1; eauto.
                 left. eapply a_wl_red__sub_arrow1; eauto.
                 intro Hsin. eapply sin_in in Hsin. eauto.
                 intros. dependent destruction H8. simpl.
                 admit. admit. (* TODO *)
              ** admit. (* TODO *)
           ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
              admit. (* TODO *)
        -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           dependent destruction H7; try unify_binds.
        -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
           edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
           right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           dependent destruction H5. 
           eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
        -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
           right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
           dependent destruction H5. eauto.
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
        -- admit. (* arrow case *)
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
            assert (Hs2: exists ns2, split_size (work_sub A0 A1 ⫤ᵃ Γ) A2 ns2) by admit.
            assert (Hs3: exists ns3, split_size (work_sub A0 A1 ⫤ᵃ Γ) A3 ns3) by admit.
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
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 unfold eq_dec in JgAlll'.
                 destruct (EqDec_eq_of_X X X) in JgAlll'.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
                 --- contradiction.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra.
              pick fresh X1.
              inst_cofinites_with X1.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X) in H8; auto.
              ** simpl in H8.
                 unfold eq_dec in H8.
                 destruct (EqDec_eq_of_X X1 X1) in H8.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in H8; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H8; auto.
                 --- contradiction.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 unfold eq_dec in JgAlll'.
                 destruct (EqDec_eq_of_X X X) in JgAlll'.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
                 --- contradiction.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra.
              pick fresh X1.
              inst_cofinites_with X1.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X) in H8; auto.
              ** simpl in H8.
                 unfold eq_dec in H8.
                 destruct (EqDec_eq_of_X X1 X1) in H8.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in H8; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H8; auto.
                 --- contradiction.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- destruct Jg as [Jg | Jg]; eauto.
           pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 unfold eq_dec in JgAlll'.
                 destruct (EqDec_eq_of_X X X) in JgAlll'.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
                 --- contradiction.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra; eauto.
              pick fresh X1.
              inst_cofinites_with X1.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X) in H8; auto.
              ** simpl in H8.
                 unfold eq_dec in H8.
                 destruct (EqDec_eq_of_X X1 X1) in H8.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in H8; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H8; auto.
                 --- contradiction.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- pick fresh X1. inst_cofinites_with X1.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 destruct_eq_atom.
                 rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H7].
              pick fresh X1'.
              inst_cofinites_with X1'.
              apply a_wl_red_rename_tvar with (X:=X1') (X':=X1) in H9; auto.
              ** simpl in H9.
                 destruct_eq_atom.
                 rewrite rename_tvar_in_aworklist_fresh_eq in H9; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H9; auto.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- pick fresh X1. inst_cofinites_with X1.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 destruct_eq_atom.
                 rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H7].
              pick fresh X1'.
              inst_cofinites_with X1'.
              apply a_wl_red_rename_tvar with (X:=X1') (X':=X1) in H9; auto.
              ** simpl in H9.
                 destruct_eq_atom.
                 rewrite rename_tvar_in_aworklist_fresh_eq in H9; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H9; auto.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- pick fresh X1. inst_cofinites_with X1.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 destruct_eq_atom.
                 rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H7].
              pick fresh X1'.
              inst_cofinites_with X1'.
              apply a_wl_red_rename_tvar with (X:=X1') (X':=X1) in H9; auto.
              ** simpl in H9.
                 destruct_eq_atom.
                 rewrite rename_tvar_in_aworklist_fresh_eq in H9; auto.
                 rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H9; auto.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- pick fresh X. inst_cofinites_with X.
           edestruct JgAlll as [JgAlll' | JgAlll']; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
              intros X' Hnin.
              apply a_wl_red_rename_tvar with (X:=X) (X':=X') in JgAlll'.
              ** simpl in JgAlll'.
                 unfold eq_dec in JgAlll'.
                 destruct (EqDec_eq_of_X X X) in JgAlll'.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
                     rewrite subst_tvar_in_typ_fresh_eq in JgAlll'; auto.
                     rewrite subst_tvar_in_typ_fresh_eq in JgAlll'; auto.
                 --- contradiction.
              ** admit.
              ** admit. (* wf *)
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra; eauto.
              pick fresh X1.
              inst_cofinites_with X1.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X) in H8; auto.
              ** simpl in H8.
                 unfold eq_dec in H8.
                 destruct (EqDec_eq_of_X X1 X1) in H8.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in H8; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H8; auto.
                     rewrite subst_tvar_in_typ_fresh_eq in H8; auto.
                     rewrite subst_tvar_in_typ_fresh_eq in H8; auto.
                 --- contradiction.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
        -- dependent destruction H3. dependent destruction H5.
           pick fresh X. inst_cofinites_with X.
           assert (Heq: all_size A = all_size (A ^ᵗ X)) by admit. (* safe *)
           assert (Heq0: all_size A0 = all_size (A0 ^ᵗ X)) by admit. (* safe *)
           assert (Heq': iu_size A = iu_size (A ^ᵗ X)) by admit. (* safe *)
           assert (Heq0': iu_size A0 = iu_size (A0 ^ᵗ X)) by admit. (* safe *)
           assert (Heq'': weight A = weight (A ^ᵗ X)) by admit. (* safe *)
           assert (Heq0'': weight A0 = weight (A0 ^ᵗ X)) by admit. (* safe *)
           assert (JgAll: a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ A0 (typ_var_f X) ) )) \/
                        ~ a_wl_red (aworklist_conswork (aworklist_constvar Γ X abind_stvar_empty) (work_sub  ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ A0 (typ_var_f X) ) ))).
           { eapply IHnw with (m := (3 * n1 + all_size (A ^ᵗ X)) * iu_size (A0 ^ᵗ X) + (3 * n3 + all_size (A0 ^ᵗ X)) * iu_size (A ^ᵗ X) + n); eauto; simpl in *; try lia.
             admit. (* safe: wf *)
             eapply measp_wl_conswork; eauto; try lia. 
             admit.
             }
           destruct JgAll as [JgAll | JgAll]; eauto.
           ++ left. inst_cofinites_for a_wl_red__sub_all; eauto.
              intros X' Hnin. 
              apply a_wl_red_rename_tvar with (X:=X) (X':=X') in JgAll.
              ** simpl in JgAll.
                 unfold eq_dec in JgAll.
                 destruct (EqDec_eq_of_X X X) in JgAll.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in JgAll; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAll; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in JgAll; auto.
                 --- contradiction.
              ** admit.
              ** admit. (* wf *)
              ** simpl.
                 rewrite ftvar_in_typ_open_typ_wrt_typ_upper.
                 rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
           ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H7].
              pick fresh X1.
              inst_cofinites_with X1.
              apply a_wl_red_rename_tvar with (X:=X1) (X':=X) in H7; auto.
              ** simpl in H7.
                 unfold eq_dec in H7.
                 destruct (EqDec_eq_of_X X1 X1) in H7.
                 --- rewrite rename_tvar_in_aworklist_fresh_eq in H7; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H7; auto.
                     rewrite subst_tvar_in_typ_open_typ_wrt_typ_tvar2 in H7; auto.
                 --- contradiction.
              ** admit. (* wf *)  
              ** simpl. rewrite ftvar_in_typ_open_typ_wrt_typ_upper.
                 rewrite ftvar_in_typ_open_typ_wrt_typ_upper. auto.
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
    edestruct (apply_conts_dec cs A) as [[w Happly] | Happly].
    * eapply apply_conts_exp_size with (Γ := Γ) in Happly as Hes.
      eapply apply_conts_judge_size in Happly as Hjs.
      destruct (measp_wl_total (aworklist_conswork Γ w)) as [m' Hms].
      eapply a_wf_wl_apply_conts; eauto.
      assert (JgApply: a_wl_red (aworklist_conswork Γ w) \/
                     ~ a_wl_red (aworklist_conswork Γ w)).
      { eapply IHnj with (m := m'); simpl; eauto; try lia.
        eapply a_wf_wl_apply_conts; eauto. }
      destruct JgApply as [JgApply | JgApply]; eauto.
      right. intro Hcontra. dependent destruction Hcontra.
      eapply apply_conts_det in Happly; eauto. subst. eapply JgApply; eauto.
    * right; intro Hcontra; dependent destruction Hcontra;
      eapply Happly; eauto.
  + simpl in *.
    edestruct (apply_contd_dec cd A B) as [[w Happly] | Happly].
    * eapply apply_contd_exp_size with (Γ := Γ) in Happly as Hes.
      eapply apply_contd_judge_size in Happly as Hjs.
      destruct (measp_wl_total (aworklist_conswork Γ w)) as [m' Hms].
      eapply a_wf_wl_apply_contd; eauto.
      assert (JgApply: a_wl_red (aworklist_conswork Γ w) \/
                     ~ a_wl_red (aworklist_conswork Γ w)).
      { eapply IHnj with (m := m'); simpl; eauto; try lia.
        eapply a_wf_wl_apply_contd; eauto. }
      destruct JgApply as [JgApply | JgApply]; eauto.
      right. intro Hcontra. dependent destruction Hcontra.
      eapply apply_contd_det in Happly; eauto. subst. eapply JgApply; eauto.
    * right; intro Hcontra; dependent destruction Hcontra;
      eapply Happly; eauto.
Admitted.
