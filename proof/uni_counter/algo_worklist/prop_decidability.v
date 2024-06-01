Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Coq.micromega.Lia.

Require Import uni_counter.notations.
Require Import uni_counter.prop_basic.
Require Import uni_counter.decl_worklist.prop_equiv.
Require Import uni_counter.algo_worklist.def_extra.
Require Import uni_counter.algo_worklist.prop_basic.
Require Import uni_counter.algo_worklist.prop_rename.
Require Import uni_counter.algo_worklist.prop_soundness.
Require Import uni_counter.algo_worklist.prop_completeness.
Require Import uni_counter.algo_worklist.transfer.
Require Import uni_counter.ltac_utils.

Inductive exp_size : aenv -> exp -> nat -> Prop :=
  | exp_size__unit : forall Σ,
      exp_size Σ exp_unit 1
  | exp_size__var_f : forall Σ x,
      exp_size Σ (exp_var_f x) 1
  | exp_size__abs : forall L Σ e n,
      (forall x, x \notin  L ->
        exp_size (x ~ (abind_var_typ typ_bot) ++ Σ)
                      (open_exp_wrt_exp e (exp_var_f x)) n) ->
      exp_size Σ (exp_abs e) (1 + n)
  | exp_size__app : forall Σ e1 e2 n1 n2 m,
      exp_size Σ e1 n1 ->
      exp_size Σ e2 n2 ->
      a_exp_split_size Σ e1 m ->
      exp_size Σ (exp_app e1 e2) (1 + n1 + n2 * m)
  | exp_size__tabs : forall L Σ e A n,
      (forall X, X \notin  L ->
        exp_size (X ~ abind_tvar_empty ++ Σ) (open_exp_wrt_typ e (typ_var_f X)) n) ->
      exp_size Σ (exp_tabs (exp_anno e A)) (2 + n * (1 + iu_size A))
  | exp_size__tapp : forall Σ e A n,
      exp_size Σ e n ->
      exp_size Σ (exp_tapp e A) (1 + n)
  | exp_size__anno : forall Σ e A n,
      exp_size Σ e n ->
      exp_size Σ (exp_anno e A) (1 + n * (1 + iu_size A)).

Hint Constructors exp_size : core.

(* Lemma a_exp_split_size_total : forall Σ e,
  Σ ᵉ⊢ᵃ e -> exists n, a_exp_split_size Σ e n. *)

Lemma exp_size_total : forall Σ e,
  Σ ᵉ⊢ᵃ e -> exists n, exp_size Σ e n.
Proof.
  intros * Hwf.
  induction Hwf; eauto.
  - pick fresh x. inst_cofinites_with x.
    destruct H1 as [n]. exists (1 + n).
    eapply exp_size__abs. intros.
    admit. (* exp_size rename *)
  - destruct IHHwf1 as [n1]. destruct IHHwf2 as [n2].
    eapply a_exp_split_size_total in Hwf1.
    exists (1 + n1 + n2 * m). eauto.
  - destruct IHa as [n]. exists (2 + n * (1 + iu_size A)). eauto.
  - destruct IHa as [n]. exists (1 + n). eauto.
  - destruct IHa as [n]. exists (1 + n * (1 + iu_size A)). eauto.
Qed.


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
  | aworklist_cons_var Γ' _ _ => exp_size_wl Γ'
  | aworklist_cons_work Γ' w => exp_size_work Γ' w + exp_size_wl Γ'
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
  | aworklist_cons_var Γ' _ _ => judge_size_wl Γ'
  | aworklist_cons_work Γ' w => judge_size_work w + judge_size_wl Γ'
  end.

Fixpoint split_depth_rec (Σ : aenv) (A:typ) (n:nat) : nat :=
  match A with
  | typ_var_f X => match lookup_tvar_bind Σ X with
                   | Some abind_stvar_empty => n
                   | _ => 0
                   end
  | typ_var_b _ => n
  | typ_top => n
  | typ_bot => n
  | typ_arrow A1 A2 => split_depth_rec Σ A1 (S n) + split_depth_rec Σ A2 (S n)
  | typ_all A => n + split_depth_rec Σ A n
  | typ_intersection A1 A2 => n + split_depth_rec Σ A1 n + split_depth_rec Σ A2 n
  | typ_union A1 A2 => n + split_depth_rec Σ A1 n + split_depth_rec Σ A2 n
  | _ => 0
  end.

Definition split_depth (Σ : aenv) (A : typ) : nat := split_depth_rec Σ A 1.

Definition split_depth_work (Σ : aenv) (w : work) : nat :=
  match w with
  | work_sub A1 A2 => split_depth Σ A1 * (1 + iu_size A2) + split_depth Σ A2 * (1 + iu_size A1)
  | _ => 0
  end.

Fixpoint split_depth_wl (Γ : aworklist) : nat :=
  match Γ with
  | aworklist_empty => 0
  | aworklist_cons_var Γ' _ _ => split_depth_wl Γ'
  | aworklist_cons_work Γ' w => split_depth_work (awl_to_aenv Γ) w + split_depth_wl Γ'
  end.

Lemma split_depth_rec_mono : forall Σ A n,
  ⊢ᵃ Σ -> a_mono_typ Σ A -> split_depth_rec Σ A n = 0.
Proof.
  intros Σ A n Hwf Hmono. generalize dependent n.
  induction A; simpl; eauto; intros; try solve [inversion Hmono].
  - dependent destruction Hmono;
      apply binds_lookup_tvar_bind in H; eauto;
      rewrite H; auto. 
  - dependent destruction Hmono.
    specialize (IHA1 Hmono1 (S n)). specialize (IHA2 Hmono2 (S n)). lia.
Qed.

Lemma split_depth_mono : forall Σ A,
  ⊢ᵃ Σ -> a_mono_typ Σ A -> split_depth Σ A = 0.
Proof.
  intros. unfold split_depth. eapply split_depth_rec_mono; eauto.
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
  | aworklist_cons_var Γ' _ _ => 1 + weight_wl Γ'
  | aworklist_cons_work Γ' w => weight_work w + weight_wl Γ'
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
  | aworklist_cons_var Γ' _ _ => infabs_depth_wl Γ'
  | aworklist_cons_work Γ' w => infabs_depth_work w + infabs_depth_wl Γ'
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
  | aworklist_cons_var Γ' _ _ => inftapp_depth_wl Γ'
  | aworklist_cons_work Γ' w => inftapp_depth_work w + inftapp_depth_wl Γ'
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
  | aworklist_cons_var Γ' _ _ => infabs_judge_size_wl Γ'
  | aworklist_cons_work Γ' w => infabs_judge_size_work w + infabs_judge_size_wl Γ'
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
  | aworklist_cons_var Γ' _ _ => inftapp_judge_size_wl Γ'
  | aworklist_cons_work Γ' w => inftapp_judge_size_work w + inftapp_judge_size_wl Γ'
  end.

Lemma iuv_size_mono : forall Σ A,
  Σ ᵗ⊢ᵃₘ A -> iuv_size A = 0.
Proof.
  intros Σ A Hmono.
  induction Hmono; simpl; eauto; try lia.
Qed.

Lemma iuv_size_subst_mono : forall Σ A X A0,
  Σ ᵗ⊢ᵃₘ A ->
  iuv_size (subst_typ_in_typ A X A0) = iuv_size A0.
Proof.
  intros Σ A X A0 Hmono.
  induction A0; simpl; auto.
  destruct (eq_dec X0 X); subst; simpl; eauto.
  eapply iuv_size_mono; eauto.
Qed.

Lemma exp_split_size_subst_typ_in_exp_mono : forall n Σ A X e,
  size_exp e < n ->
  Σ ᵗ⊢ᵃₘ A -> exp_split_size Σ ({A ᵉ/ₜ X} e) = exp_split_size Σ e.
Proof.
  intro n. induction n; try lia.
  intros Σ A X e Hsize Hmono.
  destruct e; simpl in *; eauto.
  - erewrite IHn; eauto; try lia.
  - erewrite IHn; eauto; try lia.
    erewrite IHn; eauto; try lia.
  - destruct body5. simpl in *.
    erewrite IHn; eauto; try lia.
    erewrite iuv_size_subst_mono; eauto.
  - erewrite IHn; eauto; try lia.
    erewrite iuv_size_subst_mono; eauto.
  - erewrite IHn; eauto; try lia.
    erewrite iuv_size_subst_mono; eauto.
Qed.

Lemma exp_size_subst_typ_in_exp_mono : forall Γ A X e,
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  exp_size Γ ({A ᵉ/ₜ X} e) = exp_size Γ e
with body_size_subst_typ_in_body_mono : forall Γ A X b,
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  body_size Γ ({A ᵇ/ₜ X} b) = body_size Γ b.
Proof.
  - intros Γ A X e Hmono.
    induction e; simpl; eauto.
    erewrite IHe1. erewrite exp_split_size_subst_typ_in_exp_mono; eauto.
    erewrite IHe. erewrite iu_size_subst_mono; eauto.
  - intros. destruct b. simpl.
    erewrite iu_size_subst_mono; eauto. 
Qed.

Lemma exp_size_conts_subst_typ_in_conts_mono : forall Γ X A c,
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  exp_size_conts Γ ({A ᶜˢ/ₜ X} c) = exp_size_conts Γ c
with exp_size_contd_subst_typ_in_contd_mono : forall Γ X A c,
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  exp_size_contd Γ ({A ᶜᵈ/ₜ X} c) = exp_size_contd Γ c.
Proof.
  intros Γ X A c Hmono.
  induction c; simpl; eauto.
  intros Γ X A c Hmono.
  induction c; simpl; eauto.
  erewrite exp_size_subst_typ_in_exp_mono; eauto.
Qed.

Lemma exp_size_work_subst_typ_in_work_mono : forall Γ X A w,
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  exp_size_work Γ ({A ʷ/ₜ X} w) = exp_size_work Γ w.
Proof.
  intros Γ X A w Hmono.
  induction w; intros; simpl;
    try erewrite exp_size_subst_typ_in_exp_mono;
    try erewrite exp_size_conts_subst_typ_in_conts_mono;
    try erewrite exp_size_contd_subst_typ_in_contd_mono;
    try erewrite iu_size_subst_mono; eauto.
Qed.

Lemma judge_size_wl_awl_app : forall Γ1 Γ2,
  judge_size_wl (awl_app Γ1 Γ2) = judge_size_wl Γ1 + judge_size_wl Γ2.
Proof.
  intros Γ1.
  induction Γ1; simpl; auto;
    try solve [intros; rewrite IHΓ1; simpl; lia].
Qed.

Lemma judge_size_conts_subst_typ_in_conts : forall X A c,
  judge_size_conts (subst_typ_in_conts A X c) = judge_size_conts c
with judge_size_contd_subst_typ_in_contd : forall X A c,
  judge_size_contd (subst_typ_in_contd A X c) = judge_size_contd c.
Proof.
  intros X A c.
  induction c; simpl; eauto.
  intros X A c.
  induction c; simpl; eauto.
  erewrite judge_size_conts_subst_typ_in_conts; eauto.
Qed.

Lemma judge_size_work_subst_typ_in_work : forall X A w,
  judge_size_work (subst_typ_in_work A X w) = judge_size_work w.
Proof.
  intros X A w.
  induction w; intros; simpl;
    try erewrite judge_size_conts_subst_typ_in_conts;
    try erewrite judge_size_contd_subst_typ_in_contd; eauto.
Qed.

Lemma judge_size_wl_subst_typ_in_aworklist : forall Γ X A,
  judge_size_wl (subst_typ_in_aworklist A X Γ) = judge_size_wl Γ.
Proof.
  intros Γ.
  induction Γ; intros; simpl in *;
    try erewrite judge_size_work_subst_typ_in_work; eauto.
Qed. 

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
  destruct (le_lt_dec (iu_size A) n); eauto.
  right. intros [w Happly]. dependent destruction Happly. lia.
Qed.

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
  assert (exp_size Γ e * S (iu_size A) <= exp_size Γ e * S n).
  { eapply mult_le_compat; eauto. lia. } lia.
Qed.

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

Lemma a_wf_twl_binds_etvar_aworklist_subst_dec' : forall Γ1 Γ2 X A,
  ⊢ᵃʷₜ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  (exists Γ'1 Γ'2, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2) \/ ~ (exists Γ'1 Γ'2, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2).
Proof with eauto.
  intros. generalize dependent Γ1. induction Γ2.
  - left. exists Γ1, aworklist_empty. simpl. constructor.
  - intros. assert (X0 `in` ftvar_in_typ A \/ (~ X0 `in` ftvar_in_typ A)) by fsetdec. 
    dependent destruction H.
    + apply IHΓ2 in H1. destruct H1.
      * destruct H1 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (X0 ~ᵃ A0;ᵃ Γ'2). simpl...
      * right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
        dependent destruction Hsubst. eauto.
    + apply IHΓ2 in H0. destruct H1.
      * right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
        dependent destruction Hsubst. contradiction. 
      * destruct H0. 
        -- destruct H0 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (X0 ~ᵃ □ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst. eauto.
    + destruct H1.
      * assert (⊢ᵃʷₜ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X0 ~ᵃ ⬒ ;ᵃ Γ1)) by (eapply a_wf_twl_move_etvar_back; eauto).
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
              assert (X ∉ union (dom (awl_to_aenv Γ1)) (dom (awl_to_aenv Γ2))) by (eapply a_wf_twl_avar_notin_remaining; eauto)...
      * apply IHΓ2 in H0. destruct H0.
        -- left. destruct H0 as [Γ'1 [Γ'2 Hsubst]]. exists Γ'1, (X0 ~ᵃ ⬒ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst.
           ++ rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X0. 
           ++ eauto.
           ++ contradiction.
  - intros. dependent destruction H.
    apply IHΓ2 in H1. destruct H1.
    + destruct H1 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (w ⫤ᵃ Γ'2). simpl...
    + right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
      dependent destruction Hsubst. 
      assert ((exists Γ'1 Γ'2 : aworklist, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2)) by eauto.
      contradiction.
Qed.

Lemma a_wf_wl_binds_etvar_aworklist_subst_dec' : forall Γ1 Γ2 X A,
  ⊢ᵃʷₛ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  (exists Γ'1 Γ'2, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2) \/ ~ (exists Γ'1 Γ'2, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2).
Proof with eauto.
  intros. generalize dependent Γ1. induction Γ2.
  - left. exists Γ1, aworklist_empty. simpl. constructor.
  - intros. assert (X0 `in` ftvar_in_typ A \/ (~ X0 `in` ftvar_in_typ A)) by fsetdec. 
    dependent destruction H.
    + eapply a_wf_twl_binds_etvar_aworklist_subst_dec'...
    + apply IHΓ2 in H0. destruct H1.
      * right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
        dependent destruction Hsubst. contradiction. 
      * destruct H0. 
        -- destruct H0 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (X0 ~ᵃ ■ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst. eauto.
    + destruct H1.
      * assert (⊢ᵃʷₛ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ X0 ~ᵃ ⬒ ;ᵃ Γ1)) by (eapply a_wf_wl_move_etvar_back; eauto).
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
              assert (X ∉ union (dom (awl_to_aenv Γ1)) (dom (awl_to_aenv Γ2))) by (eapply a_wf_wl_avar_notin_remaining; eauto)...
      * apply IHΓ2 in H0. destruct H0.
        -- left. destruct H0 as [Γ'1 [Γ'2 Hsubst]]. exists Γ'1, (X0 ~ᵃ ⬒ ;ᵃ Γ'2). simpl...
           constructor... rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X.
        -- right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
           dependent destruction Hsubst.
           ++ rewrite awl_to_aenv_app in H. simpl in H. unfold not. intros. subst. solve_notin_eq X0. 
           ++ eauto.
           ++ contradiction.
  - intros. dependent destruction H.
    eapply a_wf_twl_binds_etvar_aworklist_subst_dec'...
    apply IHΓ2 in H1. destruct H1.
    + destruct H1 as [Γ'1 [Γ'2 Hsubst]]. left. exists Γ'1, (work_sub A0 B ⫤ᵃ Γ'2). simpl...
    + right. unfold not. intros Hcontra. destruct Hcontra as [Γ'1 [Γ'2 Hsubst]].
      dependent destruction Hsubst. 
      assert ((exists Γ'1 Γ'2 : aworklist, aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ'1 Γ'2)) by eauto.
      contradiction.
Qed.

Lemma a_wf_wl_binds_etvar_aworklist_subst_dec : forall Γ X A,
  ⊢ᵃʷₛ Γ -> X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2) \/ ~ (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2).
Proof with eauto. 
  intros. apply awl_split_etvar in H0... destruct H0 as [Γ1 [Γ2 Hsplit]]...
  subst. apply a_wf_wl_binds_etvar_aworklist_subst_dec'...
Qed.

Lemma a_wf_twl_aworklist_subst_no_etvar_false : forall Γ Γ1 Γ2 X A,
  ⊢ᵃʷₜ Γ ->
  (X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ -> False) ->
  aworklist_subst Γ X A Γ1 Γ2 -> 
  False.
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
    + eapply a_wf_twl_move_etvar_back; eauto. 
    + intros. apply H0. simpl...
      rewrite awl_to_aenv_app. simpl...
Qed.

Lemma a_wf_wl_aworklist_subst_no_etvar_false : forall Γ Γ1 Γ2 X A,
  ⊢ᵃʷₛ Γ ->
  (X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ -> False) ->
  aworklist_subst Γ X A Γ1 Γ2 -> False.
Proof with eauto.
  intros. dependent induction H1.
  - assert (binds X abind_etvar_empty (awl_to_aenv (X ~ᵃ ⬒ ;ᵃ Γ))).
    { simpl. constructor; auto. } auto.
  - dependent destruction H.
    eapply a_wf_twl_aworklist_subst_no_etvar_false...
  - dependent destruction H.
    eapply a_wf_twl_aworklist_subst_no_etvar_false...
  - dependent destruction H.
    eapply a_wf_twl_aworklist_subst_no_etvar_false...
    apply IHaworklist_subst...
    intros. apply H1. simpl... 
  - dependent destruction H.
    eapply a_wf_twl_aworklist_subst_no_etvar_false...
    apply IHaworklist_subst...
  - dependent destruction H.
    eapply a_wf_twl_aworklist_subst_no_etvar_false...
    apply IHaworklist_subst...
    intros. apply H1. simpl...
  - dependent destruction H.
    eapply a_wf_twl_aworklist_subst_no_etvar_false...
    apply IHaworklist_subst.
    + eapply a_wf_wl_move_etvar_back; eauto. 
    + intros. apply H1. simpl...
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
  ⊢ᵃʷₛ Γ -> 
  (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2) \/ ~ (exists Γ1 Γ2, aworklist_subst Γ X A Γ1 Γ2).
Proof.
  intros.
  assert (sumbool (binds X abind_etvar_empty (awl_to_aenv Γ)) (~ binds X abind_etvar_empty (awl_to_aenv Γ))). {
    apply binds_dec. apply a_bind_eq_bool.
  }
  destruct H0.
  - apply a_wf_wl_binds_etvar_aworklist_subst_dec; eauto.
  - right. unfold not. intros. destruct H0 as [Γ1 [Γ2 Hsubst]]. 
    eapply a_wf_wl_aworklist_subst_no_etvar_false; eauto.
Qed.

(*

Lemma exp_size_wl_aworklist_subst' : forall Γ2 Γ X A Γ1 Γ1' Γ2',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (awl_to_aenv Γ) A ->
  (* ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ *)
  exp_size_wl (subst_typ_in_aworklist A X Γ2' ⧺ Γ1') = exp_size_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof.
  intros Γ2. induction Γ2; intros;
    dependent destruction H0; dependent destruction H; simpl in *; eauto;
    try solve [exfalso; eauto].
  - eapply worklist_split_etvar_det in x. destruct x. subst.
    eapply IHΓ2 in H1; eauto. admit. admit. admit.
Admitted.

Lemma exp_size_wl_aworklist_subst : forall Γ X A Γ1 Γ2,
  ⊢ᵃʷ Γ -> 
  aworklist_subst Γ X A Γ1 Γ2 -> a_mono_typ (awl_to_aenv Γ) A ->
  exp_size_wl (subst_typ_in_aworklist A X Γ2 ⧺ Γ1) = exp_size_wl Γ.
Admitted.

Lemma lookup_tvar_bind_etvar : forall Γ2 Γ1 X X0,
  X ≠ X0 ->
  lookup_tvar_bind (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) X = lookup_tvar_bind (⌊ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) X.
Proof.
  intros Γ2. induction Γ2; simpl; intros; eauto.
  - destruct (X == X0); subst; auto; try contradiction.
  - destruct (X == x); subst; auto.
  - destruct (X0 == X); subst; auto.
Qed.


Lemma split_depth_rec_etvar : forall A Γ1 Γ2 X n,
  ⊢ᵃʷ (Γ2 ⧺ Γ1) ->
  X ∉ ftvar_in_typ A ->
  X ∉ dom (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) ->
  split_depth_rec (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) A n = split_depth_rec (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) A n.
Proof.
  intros A. induction A; intros Γ1 Γ2 X0 n0 Hwf Hnotin1 Hnotin2; eauto.
  - destruct (X == X0); subst.
    eapply notin_singleton_1 in Hnotin1. contradiction.
    simpl. erewrite lookup_tvar_bind_etvar; eauto.
  - simpl in *.
    specialize (IHA1 Γ1 Γ2 X0 (S n0) Hwf).
    specialize (IHA2 Γ1 Γ2 X0 (S n0) Hwf). auto.
  - simpl in *.
    specialize (IHA Γ1 Γ2 X0 n0 Hwf). auto.
  - simpl in *.
    specialize (IHA1 Γ1 Γ2 X0 n0 Hwf).
    specialize (IHA2 Γ1 Γ2 X0 n0 Hwf). auto.
  - simpl in *.
    specialize (IHA1 Γ1 Γ2 X0 n0 Hwf).
    specialize (IHA2 Γ1 Γ2 X0 n0 Hwf). auto.
Qed.

Lemma split_depth_etvar : forall A Γ1 Γ2 X,
  ⊢ᵃʷ (Γ2 ⧺ Γ1) ->
  X ∉ ftvar_in_typ A ->
  X ∉ dom (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) ->
  split_depth (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) A = split_depth (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) A.
Proof.
  unfold split_depth. simpl. intros. erewrite split_depth_rec_etvar; eauto.
Qed.

Lemma split_depth_work_etvar : forall Γ1 Γ2 X w,
  ⊢ᵃʷ (Γ2 ⧺ Γ1) ->
  X ∉ ftvar_in_work w ->
  X ∉ dom (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) ->
  split_depth_work (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) w = split_depth_work (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) w.
Proof.
  intros Γ1 Γ2 X w. dependent destruction w; simpl; auto.
  intros Hwf Hnotin1 Hnotin2.
  erewrite <- split_depth_etvar; eauto.
  erewrite <- split_depth_etvar; eauto.
Qed.

Lemma split_depth_wl_etvar : forall Γ1 Γ2 X,
  ⊢ᵃʷ (Γ2 ⧺ Γ1) ->
  X ∉ dom (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) ->
  split_depth_wl (Γ2 ⧺ Γ1) = split_depth_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof.
  intros Γ1 Γ2.
  generalize dependent Γ1.
  induction Γ2; simpl; intros; try solve [dependent destruction H; auto].
  dependent destruction H.
  assert (X ∉ ftvar_in_work w) by admit.
  erewrite <- split_depth_work_etvar; eauto. 
Admitted.


Lemma split_depth_wl_aworklist_subst : forall Γ2 X A Γ1 Γ1' Γ2',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) A ->
  X ∉ ftvar_in_typ A ->
  split_depth_wl (subst_typ_in_aworklist A X Γ2' ⧺ Γ1') = split_depth_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1).
Proof.
  intros Γ2. induction Γ2; intros * Hwf Hsubst Hmono Hnotin; simpl in *.
  - eapply a_mono_typ_strengthen_cons in Hmono; eauto.
    dependent destruction Hsubst; simpl; eauto; try contradiction.
  - erewrite IHΓ2; eauto. admit. admit. admit.
  - dependent destruction Hsubst; simpl; destruct_a_wf_wl; eauto.
    + eapply a_mono_typ_strengthen_cons in Hmono; eauto.
    + eapply a_mono_typ_strengthen_cons in Hmono; eauto.
    + eapply a_mono_typ_strengthen_cons in Hmono; eauto.
    + assert (⊢ᵃʷ (Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ1)) by admit.
      eapply worklist_split_etvar_det in x. destruct x. subst.
      eapply IHΓ2 with (A := A) in H2; eauto. admit. admit. admit.
  - dependent destruction Hsubst; simpl; destruct_a_wf_wl; eauto.
    admit.
Admitted.

(* Lemma split_depth_rec_aworklist_subst : forall Γ2 Γ X A B Γ1 Γ1' Γ2',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  X ∉ ftvar_in_typ B ->
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (awl_to_aenv Γ) A ->
  split_depth (⌊ subst_typ_in_aworklist A X Γ2' ⧺ Γ1' ⌋ᵃ) B = split_depth (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) B.
Proof.
  intros Γ2. induction Γ2; intros Γ X0 A B Γ1 Γ1' Γ2' Hwf Hnotin Hsubst Hmono;
    dependent destruction Hsubst; dependent destruction Hwf; simpl in *; eauto;
    try solve [exfalso; eauto].
  admit.
    dependent destruction H0; dependent destruction H; simpl in *; eauto;
    try solve [exfalso; eauto].

Lemma split_depth_work_aworklist_subst : forall Γ2 Γ X A Γ1 Γ1' Γ2',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (awl_to_aenv Γ) A ->
  split_depth_work (subst_typ_in_aworklist A X Γ2' ⧺ Γ1') = split_depth_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1). *)

(* Lemma split_depth_rec_non_mono_lt : forall A Γ1 Γ2 n m,
  ⊢ᵃʷ Γ -> a_mono_typ (awl_to_aenv Γ) A ->
  split_depth_rec (⌊ Γ ⌋ᵃ) A n < split_depth_rec (⌊ Γ ⌋ᵃ) A m. *)

Lemma split_depth_rec_non_mono_non_zero : forall A Γ n,
  ⊢ᵃʷ Γ -> a_wf_typ (awl_to_aenv Γ) A ->
  (a_mono_typ (awl_to_aenv Γ) A -> False) -> n > 0 ->
  split_depth_rec (⌊ Γ ⌋ᵃ) A n > 0.
Proof.
  intros A Γ n Hwf Hwf1 Hmono.
  generalize dependent n.
  dependent induction Hwf1; simpl; intros n Hgt; eauto; try solve [exfalso; eauto]; try lia.
  - erewrite lookup_tvar_bind_binds in H; eauto.
    destruct (lookup_tvar_bind (⌊ Γ ⌋ᵃ) X); inversion H; eauto.
  - destruct (a_mono_typ_dec Γ A1); destruct (a_mono_typ_dec Γ A2); eauto.
    + exfalso. eauto.
    + eapply IHHwf1_2 with (n := S n) in H0; eauto. lia.
    + eapply IHHwf1_1 with (n := S n) in H; eauto. lia.
    + eapply IHHwf1_1 with (n := S n) in H; eauto. lia.
Qed.

Lemma split_depth_rec_non_zero_non_mono : forall A Γ n,
  ⊢ᵃʷ Γ -> split_depth_rec (⌊ Γ ⌋ᵃ) A n > 0 ->
  a_mono_typ (awl_to_aenv Γ) A -> False.
Proof.
  intros A. induction A; simpl; intros Γ n0 Hwf Hgt Hmono;
    try solve [inversion Hgt; inversion Hmono].
  - destruct (lookup_tvar_bind (⌊ Γ ⌋ᵃ) X) eqn:Heq.
    destruct a; try solve [inversion Hgt; exfalso; eauto]; eauto.
    rewrite <- lookup_tvar_bind_binds in Heq; eauto.
    dependent destruction Hmono; try unify_binds. inversion Hgt.
  - specialize (IHA1 Γ (S n0) Hwf). specialize (IHA2 Γ (S n0) Hwf).
    dependent destruction Hmono.
    destruct (split_depth_rec (⌊ Γ ⌋ᵃ) A1 (S n0)) eqn:Heq1;
    destruct (split_depth_rec (⌊ Γ ⌋ᵃ) A2 (S n0)) eqn:Heq2; eauto.
    eapply IHA1; eauto. lia. eapply IHA2; eauto. lia.
Qed.

Lemma split_depth_rec_non_mono_lt_ : forall A Γ n m,
  ⊢ᵃʷ Γ -> split_depth_rec (⌊ Γ ⌋ᵃ) A n > 0 -> n < m ->
  split_depth_rec (⌊ Γ ⌋ᵃ) A n < split_depth_rec (⌊ Γ ⌋ᵃ) A m.
Proof.
  intros A. induction A; simpl; intros Γ n0 m Hwf Hgt Hlt; eauto.
  - destruct (lookup_tvar_bind (⌊ Γ ⌋ᵃ) X) eqn:Heq.
    destruct a; try solve [exfalso; eauto]; eauto. inversion Hgt.
  - destruct (split_depth_rec (⌊ Γ ⌋ᵃ) A1 (S n0)) eqn:Heq1.
    destruct (split_depth_rec (⌊ Γ ⌋ᵃ) A2 (S n0)) eqn:Heq2.
    + inversion Hgt.
    + specialize (IHA2 Γ (S n0) (S m) Hwf). lia.
    + specialize (IHA1 Γ (S n0) (S m) Hwf).
      specialize (IHA2 Γ (S n0) (S m) Hwf). lia.
  - specialize (IHA Γ n0 m Hwf). lia.
  - specialize (IHA1 Γ n0 m Hwf).
    specialize (IHA2 Γ n0 m Hwf). lia.
  - specialize (IHA1 Γ n0 m Hwf).
    specialize (IHA2 Γ n0 m Hwf). lia.
Qed.

Lemma split_depth_rec_non_mono_lt : forall A Γ n m,
  ⊢ᵃʷ Γ -> ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A -> (a_mono_typ (awl_to_aenv Γ) A -> False) ->
  n > 0 -> n < m ->
  split_depth_rec (⌊ Γ ⌋ᵃ) A n < split_depth_rec (⌊ Γ ⌋ᵃ) A m.
Proof.
  intros.
  eapply split_depth_rec_non_mono_lt_; eauto.
  eapply split_depth_rec_non_mono_non_zero; eauto.
Qed.

Lemma split_depth_rec_aworklist_subst_ : forall B Γ2 X A Γ1 Γ1' Γ2' n,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) A ->
  X ∉ ftvar_in_typ B ->
  split_depth_rec (⌊ subst_typ_in_aworklist A X Γ2' ⧺ Γ1' ⌋ᵃ) B n = split_depth_rec (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) B n.
Proof.
  intros B. induction B; intros * Hwf Hsubst Hmono Hnotin; unfold split_depth; simpl in *; eauto.
  - admit.
Admitted.

Lemma split_depth_rec_subst : forall B Γ2 X A Γ1 n,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> a_mono_typ (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) A ->
  split_depth_rec (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) B n = split_depth_rec (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) ({A /ᵗ X} B) n.
Proof.
  intros B. induction B; intros * Hwf Hmono; unfold split_depth; simpl in *; eauto.
  - admit.
Admitted.

Lemma split_depth_rec_aworklist_subst : forall B Γ2 X A Γ1 Γ1' Γ2' n,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) -> 
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' -> a_mono_typ (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) A ->
  X ∉ ftvar_in_typ A ->
  split_depth_rec (⌊ subst_typ_in_aworklist A X Γ2' ⧺ Γ1' ⌋ᵃ) ({A /ᵗ X} B) n = split_depth_rec (⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) B n.
Proof.
  intros.
  erewrite split_depth_rec_subst; eauto. erewrite split_depth_rec_aworklist_subst_; eauto.
  eapply subst_typ_in_typ_fresh_same; eauto.
Qed.  

*)

Lemma exp_size_weaken_work : forall Γ e w,
  ⊢ᵃʷₛ Γ -> exp_size (w ⫤ᵃ Γ) e = exp_size Γ e
with body_size_weaken_work : forall Γ b w,
  ⊢ᵃʷₛ Γ -> body_size (w ⫤ᵃ Γ) b = body_size Γ b.
Proof.
  intros Γ e w Hwf. dependent destruction e; simpl; auto.
  intros Γ e w Hwf. dependent destruction e; simpl; auto.
Qed.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

Corollary rename_var_a_wf_exp_cons : forall Γ x y e A,
  x ~ (abind_var_typ A) ++ ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e  ->
  y ~ (abind_var_typ A) ++ ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ {exp_var_f y ᵉ/ₑ x} e.
Admitted.

Lemma decidablity_lemma : forall ne nj nt ntj na naj nm nw Γ,
  ⊢ᵃʷₛ Γ ->
  exp_size_wl Γ < ne ->
  judge_size_wl Γ < nj ->
  inftapp_depth_wl Γ < nt ->
  inftapp_judge_size_wl Γ < ntj ->
  infabs_depth_wl Γ < na ->
  infabs_judge_size_wl Γ < naj ->
  split_depth_wl Γ < nm ->
  weight_wl Γ < nw ->
  Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros ne; induction ne;
  intros nj; induction nj;
  intros nt; induction nt;
  intros ntj; induction ntj;
  intros na; induction na;
  intros naj; induction naj;
  intros nm; induction nm;
  intros nw; induction nw; try lia.
  intros Γ Hwf He Hj Ht Htj Ha Haj Hm Hw.
  dependent destruction Hwf; auto.
  - rename H into Hwf. dependent destruction Hwf; auto.
    + simpl in *.
      assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
      { eapply IHnw; eauto. lia. }
      destruct Jg as [Jg | Jg]; auto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + simpl in *.
      assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
      { eapply IHnw; eauto. lia. }
      destruct Jg as [Jg | Jg]; auto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + simpl in *.
      assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
      { eapply IHnw; eauto. lia. }
      destruct Jg as [Jg | Jg]; auto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + dependent destruction H.
      * dependent destruction H; simpl in *.
        -- assert (Jg: (work_applys cs typ_unit ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_applys cs typ_unit ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia. }
           destruct Jg as [Jg | Jg]; auto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- assert (Jg: (work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia.
             eapply a_wf_wl_a_wf_bind_typ in H; eauto. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply binds_unique with (b:= (abind_var_typ A0)) in H; auto. dependent destruction H.
           subst. apply Jg; auto.
        -- pick fresh x. inst_cofinites_with x.
           pick fresh X1. pick fresh X2.
           assert (Jg: (work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1 ;ᵃ work_applys cs (typ_arrow ` X1 ` X2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1 ;ᵃ work_applys cs (typ_arrow ` X1 ` X2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia.
             constructor; auto. constructor; simpl; auto. constructor; simpl; auto.
             eapply a_wf_exp_weaken_etvar_twice with (T := T); eauto.
             constructor; simpl; auto. constructor; simpl; auto.
             constructor; auto. apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.
             admit. }
           admit.
        -- assert (Jg: (work_infer e1 (conts_infabs (contd_infapp (exp_split_size (⌊ Γ ⌋ᵃ) e1) e2 cs)) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infer e1 (conts_infabs (contd_infapp (exp_split_size (⌊ Γ ⌋ᵃ) e1) e2 cs)) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia. constructor; auto. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- destruct body5. pick fresh X.
           assert (Jg: (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia. admit. admit. }
           admit.
        -- assert (Jg: (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHne; eauto; simpl; try lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- assert (Jg: (work_check e A ⫤ᵃ work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check e A ⫤ᵃ work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (exp_size (work_applys cs A ⫤ᵃ Γ) e = exp_size Γ e) by (eapply exp_size_weaken_work; eauto).
             eapply IHne; eauto; simpl; try lia. constructor; auto. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
      * simpl in *.
        assert (He': exp_size Γ e > 0) by apply exp_size_gt_0.
        assert (Jg: (work_infer e (conts_sub A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                  ~ (work_infer e (conts_sub A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHnj; eauto; simpl; try lia. }
        assert (Jg1: forall A1 A2, A = typ_union A1 A2 ->
                       (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
          eapply IHne; eauto; simpl; try lia. }
        assert (Jg2: forall A1 A2, A = typ_union A1 A2 ->
                       (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
          eapply IHne; eauto; simpl; try lia. }
        assert (Jg': forall A1 A2, A = typ_intersection A1 A2 ->
                       (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ ).
        { intros A1 A2 Heq. subst. dependent destruction H0. simpl in *.
          assert (exp_size (work_check e A1 ⫤ᵃ Γ) e = exp_size Γ e) by (eapply exp_size_weaken_work; eauto).
          eapply IHne; eauto; simpl; try lia. constructor; auto. }
        destruct Jg as [Jg | Jg]; eauto.
        dependent destruction H; simpl in *.
        -- dependent destruction H0; simpl in *;
             try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
           ++ specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
              specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
              right. intro Hcontra. dependent destruction Hcontra.
              apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
           ++ specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
              right. intro Hcontra. dependent destruction Hcontra.
              apply Jg; auto. apply Jg'; auto.
        -- dependent destruction H0; simpl in *;
             try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
           ++ specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
              specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
              right. intro Hcontra. dependent destruction Hcontra.
              apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
           ++ specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
              right. intro Hcontra. dependent destruction Hcontra.
              apply Jg; auto. apply Jg'; auto.
        -- dependent destruction H1; simpl in *;
             try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
           ++ pick fresh x.
              assert (Jgt: (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                         ~ (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ) ⟶ᵃʷ⁎⋅).
              { eapply IHne; eauto; simpl; try lia.
                constructor; auto. constructor; auto. constructor; auto.
                admit.
                assert (Hexp: exp_size (x ~ᵃ typ_bot;ᵃ Γ) (e ᵉ^^ₑ exp_var_f x) = exp_size Γ e) by admit. (* should be fine *)
                lia. }
              destruct Jgt as [Jgt | Jgt].
              ** left. inst_cofinites_for a_wl_red__chk_abstop; eauto.
                 intros x' Hnin.
                 apply rename_var_in_a_wf_wwl_a_wl_red with (x:=x) (y:=x') in Jgt; auto.
                 --- simpl in Jgt. destruct_eq_atom.
                     rewrite rename_var_in_aworklist_fresh_eq in Jgt; auto.
                     rewrite subst_exp_in_exp_open_exp_wrt_exp in Jgt; auto.
                     simpl in Jgt. destruct_eq_atom.
                     rewrite subst_exp_in_exp_fresh_eq in Jgt; auto.
                 --- apply a_wf_wl_a_wf_wwl.
                     constructor; auto. constructor; auto. constructor; auto.
                     simpl. apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
              ** right. intro Hcontra. dependent destruction Hcontra. apply Jg; auto.
                 pick fresh x1. inst_cofinites_with x1.
                 apply rename_var_in_a_wf_wwl_a_wl_red with (x:=x1) (y:=x) in H1; auto.
                 --- simpl in H1. destruct_eq_atom.
                     rewrite rename_var_in_aworklist_fresh_eq in H1; auto.
                     rewrite subst_exp_in_exp_open_exp_wrt_exp in H1; auto.
                     simpl in H1. destruct_eq_atom.
                     rewrite subst_exp_in_exp_fresh_eq in H1; auto.
                 --- apply a_wf_wl_a_wf_wwl.
                     constructor; auto. constructor; auto. constructor; auto.
                     simpl. apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
           ++ right. intro Hcontra. dependent destruction Hcontra.
              eapply Jg; eauto. unify_binds.
           ++ right. intro Hcontra. dependent destruction Hcontra.
              eapply Jg; eauto. unify_binds.
           ++ admit.
           ++ pick fresh x. inst_cofinites_with x.
              assert (JgArr: (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                           ~ (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅).
              { eapply IHne; eauto; simpl; try lia.
                constructor; auto. constructor; auto. constructor; auto.
                admit. admit.
                assert (Hexp: exp_size (x ~ᵃ A1;ᵃ Γ) (e ᵉ^^ₑ exp_var_f x) = exp_size Γ e) by admit. (* should be fine *)
                rewrite Hexp. lia. } 
              destruct JgArr as [JgArr | JgArr]; auto.
              ** left. inst_cofinites_for a_wl_red__chk_absarrow; eauto.
                 intros x' Hnin.
                 apply rename_var_in_a_wf_wwl_a_wl_red with (x:=x) (y:=x') in JgArr; auto.
                 --- simpl in JgArr. destruct_eq_atom.
                     rewrite rename_var_in_aworklist_fresh_eq in JgArr; auto.
                     rewrite subst_exp_in_exp_open_exp_wrt_exp in JgArr; auto.
                     simpl in JgArr. destruct_eq_atom.
                     rewrite subst_exp_in_exp_fresh_eq in JgArr; auto.
                 --- apply a_wf_wl_a_wf_wwl.
                     constructor; auto. constructor; auto. constructor; auto.
                     simpl. apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
                     apply a_wf_typ_weaken_cons; auto.
              ** right. intro Hcontra. dependent destruction Hcontra. apply Jg; auto.
                 pick fresh x1. inst_cofinites_with x1.
                 apply rename_var_in_a_wf_wwl_a_wl_red with (x:=x1) (y:=x) in H1; auto.
                 --- simpl in H1. destruct_eq_atom.
                     rewrite rename_var_in_aworklist_fresh_eq in H1; auto.
                     rewrite subst_exp_in_exp_open_exp_wrt_exp in H1; auto.
                     simpl in H1. destruct_eq_atom.
                     rewrite subst_exp_in_exp_fresh_eq in H1; auto.
                 --- apply a_wf_wl_a_wf_wwl.
                     constructor; auto. constructor; auto. constructor; auto.
                     simpl. apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
                     admit.
                     apply a_wf_typ_weaken_cons; auto.
        ++ specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        ++ specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      -- dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        ** specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        ** specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      -- destruct body5.
        dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        ** specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        ** specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      -- dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        ** specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        ** specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      -- dependent destruction H1; simpl in *;
          try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
        ** specialize (Jg1 A1 A2). destruct Jg1 as [Jg1 | Jg1]; eauto.
           specialize (Jg2 A1 A2). destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg1; auto. apply Jg2; auto.
        ** specialize (Jg' A1 A2). destruct Jg' as [Jg' | Jg']; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           apply Jg; auto. apply Jg'; auto.
      * simpl in *. dependent destruction H;
          try solve [right; intro Hcontra; dependent destruction Hcontra].
        -- assert (Jg:   (work_infabs (typ_arrow typ_top typ_bot) cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                       ~ (work_infabs (typ_arrow typ_top typ_bot) cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
          { eapply IHna; eauto; simpl in *; try lia. }
          destruct Jg as [Jg | Jg]; eauto.
          right. intro Hcontra.
          dependent destruction Hcontra.
          apply Jg; auto.
        -- right. intro Hcontra.
           dependent destruction Hcontra. unify_binds.
        -- right. intro Hcontra.
           dependent destruction Hcontra. unify_binds.
        -- admit. (* TODO *)
      -- destruct (apply_contd_dec cd A1 A2) as [[w Happly] | Happly];
          try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
                     eapply Happly; eauto].
         assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnaj; eauto; simpl in *; try lia.
           eapply a_wf_wl_apply_contd; eauto.
           eapply apply_contd_exp_size with (Γ := Γ) in Happly; lia.
           eapply apply_contd_judge_size in Happly; lia.
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
      -- pick fresh X. inst_cofinites_with X.
         assert (Jg: (work_infabs (A ᵗ^ₜ X) cd ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                   ~ (work_infabs (A ᵗ^ₜ X) cd ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { assert (Heq: infabs_depth (open_typ_wrt_typ A (typ_var_f X)) = infabs_depth A) by admit. (* should be fine *)
           eapply IHna; eauto; simpl in *; try lia.
           constructor; simpl; auto. constructor; simpl; auto. constructor; simpl; auto.
           eapply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
           eapply a_wf_contd_weaken_cons; auto.
           admit. (* TODO *) }
         destruct Jg as [Jg | Jg]; eauto.
         ++ left. inst_cofinites_for a_wl_red__infabs_all.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X') in Jg.
            ** simpl in Jg. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in Jg; auto.
               rewrite subst_typ_in_contd_fresh_eq in Jg; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in Jg; auto.
            ** unfold not. intros. subst. solve_notin_eq X'.
            ** eapply a_wf_wl_a_wf_wwl.
               constructor; simpl; auto. constructor; simpl; auto. constructor; simpl; auto.
               eapply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
               eapply a_wf_contd_weaken_cons; auto.
            ** simpl. auto.
         ++ right. intro Hcontra.
            dependent destruction Hcontra.
            pick fresh X1. inst_cofinites_with X1.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_contd_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
            ** eapply a_wf_wl_a_wf_wwl.
               constructor; simpl; auto. constructor; auto. admit.
      -- assert (Jg: (work_infabs A1 (contd_infabsunion A2 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                   ~ (work_infabs A1 (contd_infabsunion A2 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHna; eauto; simpl in *; try lia. }
         destruct Jg as [Jg | Jg]; eauto.
         right. intro Hcontra.
         dependent destruction Hcontra.
         apply Jg; auto.
      -- assert (Jg1: (work_infabs A1 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                    ~ (work_infabs A1 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHna; eauto; simpl in *; try lia. }
         assert (Jg2: (work_infabs A2 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                    ~ (work_infabs A2 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHna; eauto; simpl in *; try lia. }
         destruct Jg1 as [Jg1 | Jg1]; eauto.
         destruct Jg2 as [Jg2 | Jg2]; eauto.
         right. intro Hcontra.
         dependent destruction Hcontra.
         apply Jg1; auto. apply Jg2; auto.
    * simpl in *. dependent destruction H;
      try solve [right; intro Hcontra; dependent destruction Hcontra].
      assert (Jg:  (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                 ~ (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHnaj; eauto; simpl in *; try lia. constructor; auto. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra. 
      dependent destruction Hcontra. eauto.
    * dependent destruction H; try solve [right; intro Hcontra; dependent destruction Hcontra].
      assert (Jg:  (work_applys cs B ⫤ᵃ work_check e A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                 ~ (work_applys cs B ⫤ᵃ work_check e A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHnj; eauto; simpl in *; try lia. constructor; auto. admit. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra. eauto.
    * simpl in *. dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      -- destruct (apply_conts_dec cs typ_bot) as [[w Happly] | Happly];
         try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
           eapply Happly; eauto].
         assert (Jg: a_wl_red (aworklist_cons_work Γ w) \/
                   ~ a_wl_red (aworklist_cons_work Γ w)).
         { eapply IHntj; eauto; simpl in *; try lia.
           eapply a_wf_wl_apply_conts; eauto.
           eapply apply_conts_exp_size with (Γ := Γ) in Happly; lia.
           eapply apply_conts_judge_size in Happly; lia.
           admit. (* TODO *)
           eapply apply_conts_inftapp_judge_size in Happly; lia. }
         destruct Jg as [Jg | Jg]; eauto.
         right. intro Hcontra.
         dependent destruction Hcontra.
         dependent destruction Hcontra.
         eapply apply_conts_det in Happly; eauto.
         subst. eauto.
      -- destruct (apply_conts_dec cs (open_typ_wrt_typ A A2)) as [[w Happly] | Happly];
         try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
           eapply Happly; eauto].
         assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHntj; eauto; simpl in *; try lia.
           eapply a_wf_wl_apply_conts; eauto.
           constructor; auto. constructor; auto.
           eapply a_wf_typ_all_open; eauto.
           eapply apply_conts_exp_size with (Γ := Γ) in Happly; lia.
           eapply apply_conts_judge_size in Happly; lia.
           eapply apply_conts_inftapp_depth in Happly.
           assert (Hfact: inftapp_depth (open_typ_wrt_typ A A2) < (1 + inftapp_depth A) * (1 + inftapp_depth A2))
             by eapply inftapp_depth_open_typ_wrt_typ.
           assert (Hfact': inftapp_depth_work w <= inftapp_depth_conts_tail_rec cs ((1 + inftapp_depth A) * (1 + inftapp_depth A2))).
           { eapply le_trans; eauto. eapply inftapp_depth_conts_tail_rec_le. lia. }
           assert (Hfact'': inftapp_depth_conts_tail_rec cs ((1 + inftapp_depth A) * (1 + inftapp_depth A2)) <= inftapp_depth_conts_tail_rec cs (S (inftapp_depth A + S (inftapp_depth A + inftapp_depth A2 * S (inftapp_depth A))))).
           { eapply inftapp_depth_conts_tail_rec_le; eauto; lia. }
           lia.
           eapply apply_conts_inftapp_judge_size in Happly; lia. }
         destruct Jg as [Jg | Jg]; eauto.
         right. intro Hcontra.
         dependent destruction Hcontra.
         dependent destruction Hcontra.
         eapply apply_conts_det in Happly; eauto.
         subst. eauto.
      -- assert (Jg: (work_inftapp A1 A2 (conts_inftappunion A0 A2 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                   ~ (work_inftapp A1 A2 (conts_inftappunion A0 A2 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnt; eauto; simpl in *; try lia.
           assert (inftapp_depth_conts_tail_rec cs
                    (inftapp_depth A0 * S (S (inftapp_depth A2)) + 1 +
                      (inftapp_depth A1 + (inftapp_depth A1 + inftapp_depth A2 * inftapp_depth A1)))
                  < inftapp_depth_conts_tail_rec cs
                    (S (inftapp_depth A1 + inftapp_depth A0 +
                       S (inftapp_depth A1 + inftapp_depth A0 +
                         inftapp_depth A2 * S (inftapp_depth A1 + inftapp_depth A0))))).
           { eapply inftapp_depth_conts_tail_rec_lt; eauto; try lia. }
           lia. }
         destruct Jg as [Jg | Jg]; eauto.
         right. intro Hcontra.
         dependent destruction Hcontra.
         apply Jg; auto.
      -- assert (Jg1: (work_inftapp A1 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_inftapp A1 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnt; eauto; simpl in *; try lia.
           assert (inftapp_depth_conts_tail_rec cs
                    (inftapp_depth A1 +
                      (inftapp_depth A1 + inftapp_depth A2 * inftapp_depth A1))
                  < inftapp_depth_conts_tail_rec cs
                    (S (inftapp_depth A1 + inftapp_depth A0 +
                        S (inftapp_depth A1 + inftapp_depth A0 +
                           inftapp_depth A2 * S (inftapp_depth A1 + inftapp_depth A0))))).
           { eapply inftapp_depth_conts_tail_rec_lt; eauto; try lia. }
           lia. }
         assert (Jg2: (work_inftapp A0 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_inftapp A0 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnt; eauto; simpl in *; try lia.
           assert (inftapp_depth_conts_tail_rec cs
                    (inftapp_depth A0 +
                      (inftapp_depth A0 + inftapp_depth A2 * inftapp_depth A0))
                  < inftapp_depth_conts_tail_rec cs
                    (S (inftapp_depth A1 + inftapp_depth A0 +
                        S (inftapp_depth A1 + inftapp_depth A0 +
                           inftapp_depth A2 * S (inftapp_depth A1 + inftapp_depth A0))))).
           { eapply inftapp_depth_conts_tail_rec_lt; eauto; try lia. }
           lia. }
         destruct Jg1 as [Jg1 | Jg1]; eauto.
         destruct Jg2 as [Jg2 | Jg2]; eauto.
         right. intro Hcontra.
         dependent destruction Hcontra.
         apply Jg1; auto. apply Jg2; auto.
    * simpl in *.
      assert (Jg:  (work_inftapp A2 B (conts_unioninftapp A1 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                 ~ (work_inftapp A2 B (conts_unioninftapp A1 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHntj; eauto; simpl; try lia.
        assert (inftapp_depth_conts_tail_rec cs
                 (S (inftapp_depth A1 + (inftapp_depth A2 + (inftapp_depth A2 + inftapp_depth B * inftapp_depth A2))))
            <= inftapp_depth_conts_tail_rec cs
                 (inftapp_depth A1 + inftapp_depth A2 * S (S (inftapp_depth B)) + 1)).
        { eapply inftapp_depth_conts_tail_rec_le; eauto; try lia. }
        lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    * simpl in *.
      destruct (apply_conts_dec cs (typ_union A1 A2)) as [[w Happly] | Happly];
      try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
        eapply Happly; eauto].
      assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHntj; eauto; simpl in *; try lia.
        eapply a_wf_wl_apply_conts; eauto.
        eapply apply_conts_exp_size with (Γ := Γ) in Happly; lia.
        eapply apply_conts_judge_size in Happly; lia.
        eapply apply_conts_inftapp_depth in Happly.
        assert (inftapp_depth_conts_tail_rec cs (inftapp_depth (typ_union A1 A2))
             <= inftapp_depth_conts_tail_rec cs (S (inftapp_depth A1 + inftapp_depth A2))). 
        { eapply inftapp_depth_conts_tail_rec_le; eauto; lia. }
        lia.
        eapply apply_conts_inftapp_judge_size in Happly; lia. }
      destruct Jg as [Jg | Jg]; eauto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      dependent destruction Hcontra.
      eapply apply_conts_det in Happly; eauto.
      subst. eauto.
    * simpl in *. dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra];
      dependent destruction H1;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
      destruct (apply_contd_dec cd ( (typ_intersection A1 A2) )   ( (typ_union B1 B2) ) ) as [[w Happly] | Happly];
      try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
        eapply Happly; eauto].
      assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
      { eapply IHnaj; eauto; simpl in *; try lia.
        eapply a_wf_wl_apply_contd; eauto. constructor; auto.
        eapply apply_contd_exp_size with (Γ := Γ) in Happly; lia.
        eapply apply_contd_judge_size in Happly; lia.
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
    * exfalso. apply H1. eauto.
    * simpl in *. edestruct (apply_conts_dec cs A) as [[w Happly] | Happly].
      -- eapply apply_conts_exp_size with (Γ := Γ) in Happly as Hes.
         eapply apply_conts_judge_size in Happly as Hjs.
         assert (JgApply: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnj; simpl; eauto; try lia.
           eapply a_wf_wl_apply_conts; eauto. }
         destruct JgApply as [JgApply | JgApply]; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         eapply apply_conts_det in Happly; eauto. subst. eapply JgApply; eauto.
      -- right; intro Hcontra; dependent destruction Hcontra;
         eapply Happly; eauto.
    * simpl in *. edestruct (apply_contd_dec cd A B) as [[w Happly] | Happly].
      -- eapply apply_contd_exp_size with (Γ := Γ) in Happly as Hes.
         eapply apply_contd_judge_size in Happly as Hjs.
         assert (JgApply: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnj; simpl; eauto; try lia.
           eapply a_wf_wl_apply_contd; eauto. }
         destruct JgApply as [JgApply | JgApply]; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         eapply apply_contd_det in Happly; eauto. subst. eapply JgApply; eauto.
      -- right; intro Hcontra; dependent destruction Hcontra;
         eapply Happly; eauto.
  - simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHnw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - simpl in *.
    assert (HwA: weight A >= 1) by apply weight_gt_0.
    assert (HwB: weight B >= 1) by apply weight_gt_0.
    assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
    { eapply IHnw; eauto; simpl; try lia. }
    assert (JgInter1: forall A1 A2, B = typ_intersection A1 A2 ->
        (work_sub A A2 ⫤ᵃ work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A A2 ⫤ᵃ work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHnw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H0. apply a_wf_wl__conswork_sub; auto. }
    assert (JgInter2: forall A1 A2, A = typ_intersection A1 A2 ->
        (work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHnw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H. apply a_wf_wl__conswork_sub; auto. }
    assert (JgInter3: forall A1 A2, A = typ_intersection A1 A2 ->
        (work_sub A2 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A2 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHnw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H. apply a_wf_wl__conswork_sub; auto. }
    assert (JgUnion1: forall A1 A2, B = typ_union A1 A2 ->
        (work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHnw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H0. apply a_wf_wl__conswork_sub; auto. }
    assert (JgUnion2: forall A1 A2, B = typ_union A1 A2 ->
        (work_sub A A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHnw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H0. apply a_wf_wl__conswork_sub; auto. }
    assert (JgUnion3: forall A1 A2, A = typ_union A1 A2 ->
        (work_sub A2 B ⫤ᵃ work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A2 B ⫤ᵃ work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHnw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H. apply a_wf_wl__conswork_sub; auto. }
    assert (JgAlll: forall A1 X L, A = typ_all A1 ->
              neq_all B ->
              neq_intersection B ->
              neq_union B ->
              X \notin  L `union` (dom (⌊ Γ ⌋ᵃ)) ->
              (work_sub (A1 ᵗ^ₜ X) B ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
            ~ (work_sub (A1 ᵗ^ₜ X) B ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 X L Heq HneqAll HneqInter HneqUnion Hnin. subst.
      eapply IHnm; eauto; simpl in *; try lia.
      apply a_wf_wl__conswork_sub; auto.
      apply a_wf_typ_all_open; auto.
      apply a_wf_typ_weaken_cons; auto. simpl. auto.
      apply a_wf_typ_weaken_cons; auto.
      assert (HspA1: split_depth ((X, ⬒) :: ⌊ Γ ⌋ᵃ) (A1 ᵗ^ₜ X) <= split_depth (⌊ Γ ⌋ᵃ) A1) by admit.
      assert (HspB: split_depth ((X, ⬒) :: ⌊ Γ ⌋ᵃ) B <= split_depth (⌊ Γ ⌋ᵃ) B) by admit.
      eapply mult_le_compat_r with (p := S (iu_size B)) in HspA1.
      eapply mult_le_compat_r with (p := S (iu_size A1)) in HspB.
      assert (Heq: iu_size A1 = iu_size (A1 ᵗ^ₜ X)) by admit. (* safe *)
      rewrite <- Heq.
      simpl in *. unfold split_depth in *. simpl in *.
      admit. (* oh my lia *) }
    assert (JgInst1: forall (Γ1 Γ2:aworklist) (X:typvar),
              A = typ_var_f X ->
              binds X abind_etvar_empty (awl_to_aenv Γ) ->
              a_mono_typ (awl_to_aenv Γ) B ->
              aworklist_subst Γ X B Γ1 Γ2 ->
              (subst_typ_in_aworklist B X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅ \/
            ~ (subst_typ_in_aworklist B X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅).
    { intros Γ1 Γ2 X Heq Hbin Hmono Hsub. subst.
      eapply IHnw; eauto; simpl in *; try lia.
      admit. admit. admit. admit. admit. admit.
      admit. admit. admit.
      (* admit. (* safe: wf *)
      admit. (* erewrite exp_size_wl_aworklist_subst; eauto. *)
      admit. (* TODO: should be fine *)
      admit. (* TODO: should be fine *)
      admit. (* TODO: should be fine *)
      admit. (* TODO: should be fine *)
      admit. (* TODO: should be fine *)
      eapply aworklist_binds_split in Hbin as Hbin'; eauto.
      destruct Hbin' as [Γ1' [Γ2' Hbin']]. subst.
      erewrite split_depth_wl_aworklist_subst; eauto. lia. admit.
      admit. TODO: should be fine *)
    } 
    assert (JgInst2: forall (Γ1 Γ2:aworklist) (X:typvar),
              B = typ_var_f X ->
              binds X abind_etvar_empty (awl_to_aenv Γ) ->
              a_mono_typ (awl_to_aenv Γ) A ->
              aworklist_subst Γ X A Γ1 Γ2 ->
              (subst_typ_in_aworklist A X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅ \/
            ~ (subst_typ_in_aworklist A X Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅) by admit.
    (* { intros E Γ1 Γ2 X Heq Hbin Hmono Hsub. subst.
      eapply IHnw.
      admit. (* safe: wf *)
      - rewrite exp_size_wl_awl_app.
        rewrite exp_size_wl_awl_app.
        rewrite exp_size_wl_etvar_list.
        erewrite exp_size_wl_subst_typ_in_aworklist_mono; eauto. simpl.
        eapply exp_size_wl_aworklist_subst in Hsub as Heq. lia.
      - rewrite judge_size_wl_awl_app.
        rewrite judge_size_wl_awl_app.
        rewrite judge_size_wl_etvar_list.
        erewrite judge_size_wl_subst_typ_in_aworklist; eauto. simpl.
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
      -- right. intro Hcontra. dependent destruction Hcontra. unify_binds.
      -- right. intro Hcontra. dependent destruction Hcontra. unify_binds.
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
          eapply Jg; eauto; dependent destruction H1].
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
          dependent destruction H1].
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
         dependent destruction H2; try unify_binds.
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
         dependent destruction H1.
      -- destruct Jg as [Jg | Jg]; eauto.
         right; intro Hcontra; dependent destruction Hcontra; try unify_binds; eauto.
         dependent destruction H1.
      -- destruct (eq_dec X X0) as [Heq | Hneq]; subst; try unify_binds. 
         destruct (a_wf_wl_aworklist_subst_dec Γ X (` X0)) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
         ++ edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
            right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
            assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
            { eapply aworklist_subst_det; eauto. }
            destruct Heq as [Heq1 Heq2]. subst. eauto.
         ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
      -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H2; try unify_binds.
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
      -- destruct (a_mono_typ_dec Γ (typ_arrow A1 A2)); auto. apply a_wf_wl_a_wf_wwl; auto.
         ++ assert (FV: X ∉ ftvar_in_typ (typ_arrow A1 A2) \/ not (X ∉ ftvar_in_typ (typ_arrow A1 A2))) by fsetdec.
            destruct FV as [FV | FV]; try solve [right; intro Hcontra; dependent destruction Hcontra; try unify_binds].
            destruct (a_wf_wl_aworklist_subst_dec Γ X (typ_arrow A1 A2)) as [[Γ1' [Γ2' Hsubst']] | Hsubst']; eauto.
            ** edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
               right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
               assert (Heq: Γ1' = Γ1 /\ Γ2' = Γ2).
               { eapply aworklist_subst_det; eauto. }
               destruct Heq as [Heq1 Heq2]. subst. eauto.
            ** right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         ++ pick fresh X1. pick fresh X2.
            eapply awl_split_etvar in H as Hbin; eauto.
            destruct Hbin as [Γ1 [Γ2 Hbin]]. subst.
            assert (Hsubst: aworklist_subst (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X
                                            (typ_arrow ` X1 ` X2) (X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) (work_sub ` X (typ_arrow A1 A2) ⫤ᵃ Γ2)).
            { eapply a_ws1__work_stay. eapply worklist_subst_fresh_etvar_total with (Γ1 := Γ1) (Γ2 := Γ2); eauto. }
            assert (JgArr1: (work_sub ` X2 (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A2) ⫤ᵃ work_sub (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A1) ` X1 ⫤ᵃ subst_typ_in_aworklist (typ_arrow ` X1 ` X2) X Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) ⟶ᵃʷ⁎⋅ \/
                          ~ (work_sub ` X2 (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A2) ⫤ᵃ work_sub (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A1) ` X1 ⫤ᵃ subst_typ_in_aworklist (typ_arrow ` X1 ` X2) X Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) ⟶ᵃʷ⁎⋅).
            { eapply IHnm; simpl in *; eauto.
              admit. admit. admit. admit. admit. admit. admit. admit.
            }          
            admit. (* TODO: renaming stuff *)
      -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H3; try unify_binds.
      -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
         edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
         right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H1. 
         eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H1. eauto.
    * dependent destruction H1;
        try solve [right; intro Hcontra;
          dependent destruction Hcontra];
        try solve [destruct Jg as [Jg | Jg]; eauto;
          right; intro Hcontra; dependent destruction Hcontra;
          eapply Jg; eauto].
      -- right. intro Hcontra. dependent destruction Hcontra; unify_binds.
      -- right. intro Hcontra. dependent destruction Hcontra; unify_binds.
      -- admit. (* arrow case *)
      -- assert (JgArr: (work_sub A2 A3 ⫤ᵃ work_sub A0 A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                      ~ (work_sub A2 A3 ⫤ᵃ work_sub A0 A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHnw; eauto.
           simpl in *. unfold split_depth in *. simpl in *.
           assert (split_depth_rec (⌊ Γ ⌋ᵃ) A2 1 * S (iu_size A3) +
            split_depth_rec (⌊ Γ ⌋ᵃ) A3 1 * S (iu_size A2) +
            (split_depth_rec (⌊ Γ ⌋ᵃ) A0 1 * S (iu_size A1) +
            split_depth_rec (⌊ Γ ⌋ᵃ) A1 1 * S (iu_size A0) + 
            split_depth_wl Γ) <= (split_depth_rec (⌊ Γ ⌋ᵃ) A1 1 + split_depth_rec (⌊ Γ ⌋ᵃ) A2 1) *
            S (iu_size A0 + iu_size A3) +
            (split_depth_rec (⌊ Γ ⌋ᵃ) A0 1 + split_depth_rec (⌊ Γ ⌋ᵃ) A3 1) *
            S (iu_size A1 + iu_size A2) + split_depth_wl Γ) by lia.
            admit.
           simpl in *. lia. }
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
         destruct JgAlll with (X:=X) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; auto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; auto.
            pick fresh X1. inst_cofinites_with X1.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
      -- pick fresh X. inst_cofinites_with X.
         destruct JgAlll with (X:=X) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; auto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; auto.
            pick fresh X1. inst_cofinites_with X1.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
      -- pick fresh X. inst_cofinites_with X.
         destruct JgAlll with (X:=X) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; auto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; auto.
            pick fresh X1. inst_cofinites_with X1.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
      -- pick fresh X1. inst_cofinites_with X1.
         destruct JgAlll with (X:=X1) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; auto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
               simpl. auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H3].
            pick fresh X1'. inst_cofinites_with X1'.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H5; auto.
            ** simpl in H5. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H5; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H5; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X1); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               simpl. auto.
      -- pick fresh X1. inst_cofinites_with X1.
         destruct JgAlll with (X:=X1) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; auto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
               simpl. auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H3].
            pick fresh X1'. inst_cofinites_with X1'.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H5; auto.
            ** simpl in H5. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H5; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H5; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X1); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               simpl. auto.
      -- pick fresh X1. inst_cofinites_with X1.
         destruct JgAlll with (X:=X1) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; auto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
               simpl. auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H3].
            pick fresh X1'. inst_cofinites_with X1'.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H5; auto.
            ** simpl in H5. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H5; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H5; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X1); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               simpl. auto.
      -- pick fresh X. inst_cofinites_with X.
         destruct JgAlll with (X:=X) (A1:=A) (L:=L) as [JgAlll' | JgAlll']; eauto.
         ++ left. inst_cofinites_for a_wl_red__sub_alll; eauto.
            intros X' Hnin.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X') in JgAlll'; auto.
            ** simpl in JgAlll'. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAlll'; auto.
               rewrite subst_typ_in_typ_fresh_eq in JgAlll'; auto.
               rewrite subst_typ_in_typ_fresh_eq in JgAlll'; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
               apply a_wf_typ_weaken_cons; auto.
         ++ right. intro Hcontra. dependent destruction Hcontra; auto.
            pick fresh X1. inst_cofinites_with X1.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
               rewrite subst_typ_in_typ_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_fresh_eq in H4; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               apply a_wf_typ_weaken_cons; auto.
      --  pick fresh X. inst_cofinites_with X.
          assert (JgAll: (work_sub (A ᵗ^ₜ X) (A0 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                       ~ (work_sub (A ᵗ^ₜ X) (A0 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
          { eapply IHnw; eauto; simpl in *; try lia.
            admit. (* safe: wf *) 
            admit. admit. }
          destruct JgAll as [JgAll | JgAll]; eauto.
          ++ left. inst_cofinites_for a_wl_red__sub_all; eauto.
             intros X' Hnin. 
             apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X') in JgAll; auto.
             ** simpl in JgAll. destruct_eq_atom.
                rewrite rename_tvar_in_aworklist_fresh_eq in JgAll; auto.
                rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAll; auto.
                rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in JgAll; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_stvar with (Σ2 := nil). simpl. auto.
               apply a_wf_typ_tvar_stvar with (Σ2 := nil). simpl. auto.
          ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H3].
             pick fresh X1. inst_cofinites_with X1.
             apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_stvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               apply a_wf_typ_tvar_stvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
      -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
         edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         ++ dependent destruction H3.
         ++ eapply JgUnion1'; eauto.
         ++ eapply JgUnion2'; eauto.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         right. intro Hcontra. dependent destruction Hcontra.
         ++ dependent destruction H2.
         ++ eapply JgInter1'; eauto.
  * dependent destruction H1;
      try solve [edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto;
                  right; intro Hcontra; dependent destruction Hcontra;
                  eapply JgUnion3'; eauto; try dependent destruction H3].
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
        dependent destruction H3].
    -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
       edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       eapply JgInter2'; eauto. eapply JgInter3'; eauto.
       eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
    -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       eapply JgInter1'; eauto. eapply JgInter2'; eauto. eapply JgInter3'; eauto.
Admitted.
