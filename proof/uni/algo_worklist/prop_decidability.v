Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import Coq.micromega.Lia.

Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.def_extra.
Require Import uni.algo_worklist.prop_basic.
Require Import uni.algo_worklist.prop_rename.
Require Import uni.algo_worklist.transfer.
Require Import uni.ltac_utils.

#[local] Hint Extern 1 ((exists _, _) -> False) => try solve_false : core.

Inductive nbind : Set := 
 | nbind_tvar_empty : nbind
 | nbind_stvar_empty : nbind
 | nbind_etvar_empty : nbind
 | nbind_var_typ (n:nat).

Definition nenv : Set := list (atom*nbind).

Inductive n_wf_exp : nenv -> exp -> Prop :=
  | n_wf_exp__unit : forall Ξ,
      n_wf_exp Ξ exp_unit
  | n_wf_exp__var_f : forall Ξ x n,
      binds x (nbind_var_typ n) Ξ ->
      n_wf_exp Ξ (exp_var_f x)
  | n_wf_exp__abs : forall Ξ L e,
      (forall x, x \notin L ->
        n_wf_exp (x ~ (nbind_var_typ 0) ++ Ξ) (open_exp_wrt_exp e (exp_var_f x)) )->
      n_wf_exp Ξ (exp_abs e)
  | n_wf_exp__app : forall Ξ e1 e2,
      n_wf_exp Ξ e1 ->
      n_wf_exp Ξ e2 ->
      n_wf_exp Ξ (exp_app e1 e2)
  | n_wf_exp__tabs : forall Ξ L e A,
      (forall X, X \notin L ->
        n_wf_exp (X ~ nbind_tvar_empty ++ Ξ) (exp_anno (open_exp_wrt_typ e (typ_var_f X)) (open_typ_wrt_typ A (typ_var_f X)))) ->
      n_wf_exp Ξ (exp_tabs (exp_anno e A))
  | n_wf_exp__tapp : forall Ξ e A,
      n_wf_exp Ξ e ->
      lc_typ A ->
      n_wf_exp Ξ (exp_tapp e A)
  | n_wf_exp__anno : forall Ξ e A,
      n_wf_exp Ξ e ->
      lc_typ A ->
      n_wf_exp Ξ (exp_anno e A).

Inductive n_wf_conts : nenv -> conts -> Prop :=
  | n_wf_conts__infabs : forall Ξ cd,
      n_wf_contd Ξ cd ->
      n_wf_conts Ξ (conts_infabs cd)
  | n_wf_conts__inftapp : forall Ξ B cs,
      lc_typ B ->
      n_wf_conts Ξ cs ->
      n_wf_conts Ξ (conts_inftapp B cs)
  | n_wf_conts__inftappunion : forall Ξ A B cs,
      lc_typ A ->
      lc_typ B ->
      n_wf_conts Ξ cs ->
      n_wf_conts Ξ (conts_inftappunion A B cs)
  | n_wf_conts__unioninftapp : forall Ξ A cs,
      lc_typ A ->
      n_wf_conts Ξ cs ->
      n_wf_conts Ξ (conts_unioninftapp A cs)
  | n_wf_conts__sub : forall Ξ A,
      lc_typ A ->
      n_wf_conts Ξ (conts_sub A)
with n_wf_contd : nenv -> contd -> Prop :=
  | n_wf_contd__infabsunion : forall Ξ A cd,
      lc_typ A ->
      n_wf_contd Ξ cd ->
      n_wf_contd Ξ (contd_infabsunion A cd)
  | n_wf_contd__infapp : forall Ξ e cs,
      n_wf_exp Ξ e ->
      n_wf_conts Ξ cs ->
      n_wf_contd Ξ (contd_infapp e cs)
  | n_wf_contd__unioninfabs : forall Ξ A B cd,
      lc_typ A ->
      lc_typ B ->
      n_wf_contd Ξ cd ->
      n_wf_contd Ξ (contd_unioninfabs A B cd).

Inductive n_wf_work : nenv -> work -> Prop :=
  | n_wf_work__infer : forall Ξ e cs,
      n_wf_exp Ξ e ->
      n_wf_conts Ξ cs ->
      n_wf_work Ξ (work_infer e cs)
  | n_wf_work__check : forall Ξ e A,
      n_wf_exp Ξ e ->
      lc_typ A ->
      n_wf_work Ξ (work_check e A)
  | n_wf_work__infabs : forall Ξ A cd,
      lc_typ A ->
      n_wf_contd Ξ cd ->
      n_wf_work Ξ (work_infabs A cd)
  | n_wf_work__infabsunion : forall Ξ B1 C1 A2 cd,
      lc_typ B1 ->
      lc_typ A2 ->
      n_wf_contd Ξ cd ->
      n_wf_work Ξ (work_infabsunion B1 C1 A2 cd)
  | n_wf_work__infapp : forall Ξ A B e cs,
      lc_typ A ->
      lc_typ B ->
      n_wf_exp Ξ e ->
      n_wf_conts Ξ cs ->
      n_wf_work Ξ (work_infapp A B e cs)
  | n_wf_work__inftapp : forall Ξ A B cs,
      lc_typ A ->
      lc_typ B ->
      n_wf_conts Ξ cs ->
      n_wf_work Ξ (work_inftapp A B cs)
  | n_wf_work__sub : forall Ξ A1 A2,
      lc_typ A1 ->
      lc_typ A2 ->
      n_wf_work Ξ (work_sub A1 A2)
  | n_wf_work__inftappunion : forall Ξ A1 A2 B cs,
      lc_typ A1 ->
      lc_typ A2 ->
      lc_typ B ->
      n_wf_conts Ξ cs ->
      n_wf_work Ξ (work_inftappunion A1 A2 B cs)
  | n_wf_work__unioninftapp : forall Ξ A1 A2 cs,
      lc_typ A1 ->
      lc_typ A2 ->
      n_wf_conts Ξ cs ->
      n_wf_work Ξ (work_unioninftapp A1 A2 cs)
  | n_wf_work__unioninfabs : forall Ξ A1 A2 B1 B2 cd,
      lc_typ A1 ->
      lc_typ A2 ->
      lc_typ B1 ->
      lc_typ B2 ->
      n_wf_contd Ξ cd ->
      n_wf_work Ξ (work_unioninfabs A1 B1 A2 B2 cd)
  | n_wf_work__applys : forall Ξ cs A,
      lc_typ A ->
      n_wf_conts Ξ cs ->
      n_wf_work Ξ (work_applys cs A)
  | n_wf_work__applyd : forall Ξ cd A B,
      lc_typ A ->
      lc_typ B ->
      n_wf_contd Ξ cd ->
      n_wf_work Ξ (work_applyd cd A B).

Inductive num_occurs_in_typ : atom -> typ -> nat -> Prop :=
  | num_occurs_in_typ__unit : forall X,
      num_occurs_in_typ X typ_unit 0
  | num_occurs_in_typ__bot : forall X,
      num_occurs_in_typ X typ_bot 0
  | num_occurs_in_typ__top : forall X,
      num_occurs_in_typ X typ_top 0
  | num_occurs_in_typ__tvar_same : forall X,
      num_occurs_in_typ X (typ_var_f X) 1
  | num_occurs_in_typ__tvar_diff : forall X Y,
      X <> Y ->
      num_occurs_in_typ X (typ_var_f Y) 0
  | num_occurs_in_typ__arrow : forall X A1 A2 n1 n2,
      num_occurs_in_typ X A1 n1 ->
      num_occurs_in_typ X A2 n2 ->
      num_occurs_in_typ X (typ_arrow A1 A2) (n1 + n2)
  | num_occurs_in_typ__all : forall L X A n,
      (forall Y,
        Y \notin L ->
        num_occurs_in_typ X (open_typ_wrt_typ A (typ_var_f Y)) n) ->
      num_occurs_in_typ X (typ_all A) n
  | num_occurs_in_typ__union : forall X A1 A2 n1 n2,
      num_occurs_in_typ X A1 n1 ->
      num_occurs_in_typ X A2 n2 ->
      num_occurs_in_typ X (typ_union A1 A2) (n1 + n2)
  | num_occurs_in_typ__intersection : forall X A1 A2 n1 n2,
      num_occurs_in_typ X A1 n1 ->
      num_occurs_in_typ X A2 n2 ->
      num_occurs_in_typ X (typ_intersection A1 A2) (n1 + n2).

Inductive n_iuv_size : typ -> nat -> Prop :=
  | n_iuv_size__unit :
      n_iuv_size typ_unit 0
  | n_iuv_size__bot :
      n_iuv_size typ_bot 0
  | n_iuv_size__top :
      n_iuv_size typ_top 0
  | n_iuv_size__tvar : forall X,
      n_iuv_size (typ_var_f X) 0
  | n_iuv_size__arrow : forall A1 A2 n1 n2 n,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      n = n1 + n2 ->
      n_iuv_size (typ_arrow A1 A2) n
  | n_iuv_size__all : forall L A n m k,
      (forall X,
        X \notin L ->
        n_iuv_size (open_typ_wrt_typ A (typ_var_f X)) n) ->
      (forall X,
        X \notin L ->
        num_occurs_in_typ X (open_typ_wrt_typ A (typ_var_f X)) m) ->
      k = n + m ->
      n_iuv_size (typ_all A) k
  | n_iuv_size__union : forall A1 A2 n1 n2 n,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      n = 2 + n1 + n2 ->
      n_iuv_size (typ_union A1 A2) n
  | n_iuv_size__intersection : forall A1 A2 n1 n2 n,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      n = 2 + n1 + n2 ->
      n_iuv_size (typ_intersection A1 A2) n.

Inductive exp_split_size : nenv -> exp -> nat -> Prop :=
  | exp_split_size__unit : forall Ξ,
      exp_split_size Ξ exp_unit 0
  | exp_split_size__var_f : forall Ξ x n,
      binds x (nbind_var_typ n) Ξ ->
      exp_split_size Ξ (exp_var_f x) n
  | exp_split_size__abs : forall L Ξ e n,
      (forall x, x \notin  L ->
        exp_split_size (x ~ (nbind_var_typ 0) ++ Ξ)
                       (open_exp_wrt_exp e (exp_var_f x)) n) ->
      exp_split_size Ξ (exp_abs e) n
  | exp_split_size__app : forall Ξ e1 e2 n1 n2 m,
      exp_split_size Ξ e1 n1 ->
      exp_split_size Ξ e2 n2 ->
      m = 1 + 2 * n1 + n2 ->
      exp_split_size Ξ (exp_app e1 e2) m
  | exp_split_size__tabs : forall L Ξ e A n m k,
      (forall X, X \notin  L ->
        exp_split_size (X ~ nbind_tvar_empty ++ Ξ)
                       (open_exp_wrt_typ e (typ_var_f X)) n) ->
      (forall X, X \notin  L ->
        n_iuv_size (open_typ_wrt_typ A (typ_var_f X)) m) ->
      k = (1 + n) * (2 + m) ->
      exp_split_size Ξ (exp_tabs (exp_anno e A)) k
  | exp_split_size__tapp : forall Ξ e A n m k,
      exp_split_size Ξ e n ->
      n_iuv_size A m ->
      k = (1 + n) * (2 + m) ->
      exp_split_size Ξ (exp_tapp e A) k
  | exp_split_size__anno : forall Ξ e A n m k,
      exp_split_size Ξ e n ->
      n_iuv_size A m ->
      k = (1 + n) * (2 + m) ->
      exp_split_size Ξ (exp_anno e A) k.

Inductive exp_size : nenv -> exp -> nat -> nat -> Prop :=
  | exp_size__unit : forall Ξ n,
      exp_size Ξ exp_unit n (S n)
  | exp_size__var_f : forall Ξ x n,
      exp_size Ξ (exp_var_f x) n (S n)
  | exp_size__abs : forall L Ξ e n m k,
      (forall x, x \notin  L ->
        exp_size ((x ~ (nbind_var_typ n)) ++ Ξ)
                 (open_exp_wrt_exp e (exp_var_f x)) n m) ->
      k = 1 + n + m ->
      exp_size Ξ (exp_abs e) n k
  | exp_size__app : forall Ξ e1 e2 n m1 m2 s k,
      exp_split_size Ξ e1 s ->
      exp_size Ξ e1 n m1 ->
      exp_size Ξ e2 (s * n + s + n) m2 ->
      k = 1 + m1 + m2 + s * m2 ->
      exp_size Ξ (exp_app e1 e2) n k
  | exp_size__tabs : forall L Ξ e A n m a k,
      (forall X, X \notin  L ->
        n_iuv_size (open_typ_wrt_typ A (typ_var_f X)) a) ->
      (forall X, X \notin  L ->
        exp_size (X ~ nbind_tvar_empty ++ Ξ)
                 (open_exp_wrt_typ e (typ_var_f X)) a m) ->
      k = 1 + m * n + m + n ->
      exp_size Ξ (exp_tabs (exp_anno e A)) n k
  | exp_size__tapp : forall Ξ e A n m a k,
      n_iuv_size A a ->
      exp_size Ξ e (a * n + a + n) m ->
      k = 1 + m * n + m + n ->
      exp_size Ξ (exp_tapp e A) n k
  | exp_size__anno : forall Ξ e A n m a k,
      n_iuv_size A a ->
      exp_size Ξ e a m ->
      k = 1 + m * n + m + n ->
      exp_size Ξ (exp_anno e A) n k.

Inductive exp_size_conts : nenv -> conts -> nat -> nat -> Prop :=
  | exp_size_conts__infabs : forall Ξ cd n m,
      exp_size_contd Ξ cd n m ->
      exp_size_conts Ξ (conts_infabs cd ) n m
  | exp_size_conts__inftapp : forall Ξ B cs n m b,
      n_iuv_size B b ->
      exp_size_conts Ξ cs ((2 + b) * n) m ->
      exp_size_conts Ξ (conts_inftapp B cs) n m
  | exp_size_conts__inftappunion : forall Ξ A B cs n m a b,
      n_iuv_size A a ->
      n_iuv_size B b ->
      exp_size_conts Ξ cs (2 + a * (2 + b) + n) m ->
      exp_size_conts Ξ (conts_inftappunion A B cs) n m
  | exp_size_conts__unioninftapp : forall Ξ A cs n m a,
      n_iuv_size A a ->
      exp_size_conts Ξ cs (2 + a + n) m ->
      exp_size_conts Ξ (conts_unioninftapp A cs) n m
  | exp_size_conts__sub : forall Ξ A n,
      exp_size_conts Ξ (conts_sub A) n 0
with exp_size_contd : nenv -> contd -> nat -> nat -> Prop :=
  | exp_size_contd__infabsunion : forall Ξ A cd n m a,
      n_iuv_size A a ->
      exp_size_contd Ξ cd (1 + n + a) m ->
      exp_size_contd Ξ (contd_infabsunion A cd) n m
  | exp_size_contd__infapp : forall Ξ n e cs ne ncs k,
      exp_size Ξ e n ne ->
      exp_size_conts Ξ cs n ncs ->
      k = ne + ne * n + ncs ->
      exp_size_contd Ξ (contd_infapp e cs) n k
  | exp_size_contd__unioninfabs : forall Ξ A B cd n m a,
      n_iuv_size A a ->
      exp_size_contd Ξ cd (1 + a + n) m ->
      exp_size_contd Ξ (contd_unioninfabs A B cd) n m.

Inductive exp_size_work : nenv -> work -> nat -> Prop :=
  | exp_size_work__infer : forall Ξ e cs n s m k,
      exp_size Ξ e 0 n ->
      exp_split_size Ξ e s ->
      exp_size_conts Ξ cs s m ->
      k = n + m ->
      exp_size_work Ξ (work_infer e cs) k
  | exp_size_work__check : forall Ξ e A n m,
      n_iuv_size A n ->
      exp_size Ξ e n m ->
      exp_size_work Ξ (work_check e A) m
  | exp_size_work__infabs : forall Ξ A cd n m,
      n_iuv_size A n ->
      exp_size_contd Ξ cd n m ->
      exp_size_work Ξ (work_infabs A cd) m
  | exp_size_work__infabsunion : forall Ξ B1 C1 A2 cd n1 n2 m,
      n_iuv_size B1 n1 ->
      n_iuv_size A2 n2 ->
      exp_size_contd Ξ cd (1 + n1 + n2) m ->
      exp_size_work Ξ (work_infabsunion B1 C1 A2 cd) m
  | exp_size_work__infapp : forall Ξ A B e cs a b n m k,
      n_iuv_size A a ->
      n_iuv_size B b ->
      exp_size Ξ e (a + b) m ->
      exp_size_conts Ξ cs (a + b) n ->
      k = m + m * a + n ->
      exp_size_work Ξ (work_infapp A B e cs) k
  | exp_size_work__inftapp : forall Ξ A B cs n1 n2 n,
      n_iuv_size A n1 ->
      n_iuv_size B n2 ->
      exp_size_conts Ξ cs ((2 + n2) * n1) n ->
      exp_size_work Ξ (work_inftapp A B cs) n
  | exp_size_work__sub : forall Ξ A1 A2,
      exp_size_work Ξ (work_sub A1 A2) 0
  | exp_size_work__inftappunion : forall Ξ A1 A2 B cs n1 n2 n m,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      n_iuv_size B n ->
      exp_size_conts Ξ cs (2 + n2 * (2 + n) + n1) m ->
      exp_size_work Ξ (work_inftappunion A1 A2 B cs) m
  | exp_size_work__unioninftapp : forall Ξ A1 A2 cs n1 n2 m,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      exp_size_conts Ξ cs (2 + n1 + n2) m ->
      exp_size_work Ξ (work_unioninftapp A1 A2 cs) m
  | exp_size_work__unioninfabs : forall Ξ A1 A2 B1 B2 cd n1 n2 m,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      exp_size_contd Ξ cd (1 + n1 + n2) m ->
      exp_size_work Ξ (work_unioninfabs A1 B1 A2 B2 cd) m
  | exp_size_work__applys : forall Ξ cs A n m,
      n_iuv_size A n ->
      exp_size_conts Ξ cs n m ->
      exp_size_work Ξ (work_applys cs A) m
  | exp_size_work__applyd : forall Ξ cd A B n m,
      n_iuv_size A n ->
      exp_size_contd Ξ cd n m ->
      exp_size_work Ξ (work_applyd cd A B) m.

Inductive abind_to_nbind : nenv -> abind -> nbind -> Prop :=
  | abind_to_nbind__tvar_empty : forall Ξ,
      abind_to_nbind Ξ abind_tvar_empty nbind_tvar_empty
  | abind_to_nbind__stvar_empty : forall Ξ,
      abind_to_nbind Ξ abind_stvar_empty nbind_stvar_empty
  | abind_to_nbind__etvar_empty : forall Ξ,
      abind_to_nbind Ξ abind_etvar_empty nbind_etvar_empty
  | abind_to_nbind__var_typ : forall Ξ A n,
      n_iuv_size A n ->
      abind_to_nbind Ξ (abind_var_typ A) (nbind_var_typ n).

Inductive awl_to_nenv : aworklist -> nenv -> Prop :=
  | awl_to_nenv__empty :
      awl_to_nenv aworklist_empty nil
  | awl_to_nenv__cons_var : forall Γ Ξ x b b',
      awl_to_nenv Γ Ξ ->  
      abind_to_nbind Ξ b b' ->
      awl_to_nenv (aworklist_cons_var Γ x b) ((x, b') :: Ξ)
  | awl_to_nenv__cons_work : forall Γ Ξ w,
      awl_to_nenv Γ Ξ ->
      awl_to_nenv (aworklist_cons_work Γ w) Ξ.

Inductive exp_size_wl : aworklist -> nat -> Prop :=
  | exp_size_wl__empty : exp_size_wl aworklist_empty 0
  | exp_size_wl__cons_var : forall Γ x B n,
      exp_size_wl Γ n ->
      exp_size_wl (aworklist_cons_var Γ x B) n
  | exp_size_wl__cons_work : forall Γ Ξ w n m k,
      awl_to_nenv Γ Ξ ->
      exp_size_work Ξ w m ->
      exp_size_wl Γ n ->
      k = m + n ->
      exp_size_wl (aworklist_cons_work Γ w) k.
  
Hint Constructors n_iuv_size exp_split_size exp_size exp_size_conts exp_size_contd exp_size_work exp_size_wl abind_to_nbind awl_to_nenv : core.

Lemma num_occurs_in_typ_det : forall X A n n',
  num_occurs_in_typ X A n -> num_occurs_in_typ X A n' -> n = n'.
Proof.
  intros X A n n' Hoccurs. generalize dependent n'.
  induction Hoccurs; intros n' Hoccurs'; dependent destruction Hoccurs'; eauto;
    try solve [exfalso; eauto].
  pick fresh Y. inst_cofinites_with Y.
  eapply H0 in H1; eauto.
Qed.

Lemma n_iuv_size_det : forall A n n',
  n_iuv_size A n -> n_iuv_size A n' -> n = n'.
Proof.
  intros A n n' Hsize. generalize dependent n'.
  induction Hsize; intros n' Hsize'; dependent destruction Hsize'; eauto.
  - eapply IHHsize1 in Hsize'1.
    eapply IHHsize2 in Hsize'2. lia.
  - pick fresh X. inst_cofinites_with X.
    eapply H0 in H3. eapply num_occurs_in_typ_det in H1; eauto. lia.
  - eapply IHHsize1 in Hsize'1.
    eapply IHHsize2 in Hsize'2. lia.
  - eapply IHHsize1 in Hsize'1.
    eapply IHHsize2 in Hsize'2. lia.
Qed.

Lemma exp_split_size_det : forall Ξ e n n',
  uniq Ξ -> exp_split_size Ξ e n -> exp_split_size Ξ e n' -> n = n'.
Proof.
  intros Ξ e n n' Huniq Hsize. generalize dependent n'.
  induction Hsize; intros n' Hsize'; dependent destruction Hsize'; eauto.
  - unify_binds. eauto.
  - remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
    eapply H0 in H1; eauto.
  - eapply IHHsize1 in Hsize'1; eauto.
    eapply IHHsize2 in Hsize'2; eauto. lia.
  - remember (dom Ξ). pick fresh X. subst. inst_cofinites_with X.
    eapply H0 in H3; eauto. eapply n_iuv_size_det in H1; eauto.
  - eapply IHHsize in Hsize'; eauto. eapply n_iuv_size_det in H; eauto. lia.
  - eapply IHHsize in Hsize'; eauto. eapply n_iuv_size_det in H; eauto. lia.
Qed.

Lemma exp_size_det : forall Ξ e n m m',
  uniq Ξ -> exp_size Ξ e n m -> exp_size Ξ e n m' -> m = m'.
Proof.
  intros Ξ e n m m' Huniq Hsize. generalize dependent m'.
  induction Hsize; intros m' Hsize'; dependent destruction Hsize'; eauto.
  - remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
    eapply H0 in H2; eauto.
  - eapply exp_split_size_det in H; eauto. subst.
    eapply IHHsize1 in Hsize'1; eauto.
    eapply IHHsize2 in Hsize'2; eauto.
  - remember (dom Ξ). pick fresh X. subst. inst_cofinites_with X.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply H1 in H4; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply IHHsize in Hsize'; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply IHHsize in Hsize'; eauto.
Qed.

Lemma exp_size_conts_det : forall Ξ cs n m m',
  exp_size_conts Ξ cs n m -> uniq Ξ -> exp_size_conts Ξ cs n m' -> m = m'
with exp_size_contd_det : forall Ξ cd n m m',
  exp_size_contd Ξ cd n m -> uniq Ξ -> exp_size_contd Ξ cd n m' -> m = m'.
Proof.
  - clear exp_size_conts_det. intros Ξ cs n m m' Hsize Huniq Hsize'. generalize dependent m'. generalize dependent n.
    induction cs; intros; dependent destruction Hsize; dependent destruction Hsize'; auto.
    + eapply exp_size_contd_det in H; eauto.
    + apply n_iuv_size_det with (n := b) in H0; auto. subst.
      apply IHcs in Hsize'; auto.
    + apply n_iuv_size_det with (n := a) in H1; auto.
      apply n_iuv_size_det with (n := b) in H2; auto. subst.
      apply IHcs in Hsize'; auto.
    + apply n_iuv_size_det with (n := a) in H0; auto. subst.
      apply IHcs in Hsize'; auto.
  - clear exp_size_contd_det. intros Ξ cd n m m' Hsize Huniq Hsize'. generalize dependent m'. generalize dependent n.
    induction cd; intros; dependent destruction Hsize; dependent destruction Hsize'; auto.
    + apply n_iuv_size_det with (n := a) in H0; auto. subst.
      apply IHcd in Hsize'; auto.
    + apply exp_size_det with (m := ne) in H1; auto. subst.
      apply exp_size_conts_det with (m := ncs) in H2; auto.
    + apply n_iuv_size_det with (n := a) in H0; auto. subst.
      eapply IHcd in Hsize'; eauto.
Qed.

Lemma exp_size_work_det : forall Ξ w n n',
  uniq Ξ -> exp_size_work Ξ w n -> exp_size_work Ξ w n' -> n = n'.
Proof.
  intros Ξ w n n' Huniq Hsize. generalize dependent n'.
  induction Hsize; intros n' Hsize'; dependent destruction Hsize'; eauto.
  - eapply exp_size_det in H; eauto.
    eapply exp_split_size_det in H0; eauto. subst.
    eapply exp_size_conts_det in H5; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_det in H0; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_contd_det in H0; eauto.
  - eapply n_iuv_size_det in H; eauto.
    eapply n_iuv_size_det in H0; eauto. subst.
    eapply exp_size_contd_det in H4; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply n_iuv_size_det in H0; eauto. subst.
    eapply exp_size_det in H1; eauto. subst.
    eapply exp_size_conts_det in H2; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply n_iuv_size_det in H0; eauto. subst.
    eapply exp_size_conts_det in H1; eauto.
  - eapply n_iuv_size_det in H; eauto.
    eapply n_iuv_size_det in H0; eauto.
    eapply n_iuv_size_det in H1; eauto. subst.
    eapply exp_size_conts_det in H2; eauto.
  - eapply n_iuv_size_det in H; eauto.
    eapply n_iuv_size_det in H0; eauto. subst.
    eapply exp_size_conts_det in H1; eauto.
  - eapply n_iuv_size_det in H; eauto.
    eapply n_iuv_size_det in H0; eauto. subst.
    eapply exp_size_contd_det in H4; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_conts_det in H2; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_contd_det in H2; eauto.
Qed.

Lemma abind_to_nbind_det : forall Ξ b b' b'',
  abind_to_nbind Ξ b b' -> abind_to_nbind Ξ b b'' -> b' = b''.
Proof.
  intros Ξ b b' b'' Hbind. generalize dependent b''.
  induction Hbind; intros b'' Hbind'; dependent destruction Hbind'; eauto.
  eapply n_iuv_size_det in H; eauto.
Qed.

Lemma awl_to_nenv_det : forall Γ Ξ Ξ',
  awl_to_nenv Γ Ξ -> awl_to_nenv Γ Ξ' -> Ξ = Ξ'.
Proof.
  intros Γ Ξ Ξ' Henv. generalize dependent Ξ'.
  induction Henv; intros Ξ' Henv'; dependent destruction Henv'; eauto.
  eapply IHHenv in Henv'; eauto. subst.
  eapply abind_to_nbind_det in H; eauto. subst. auto.
Qed.

Lemma exp_size_wl_det : forall Γ Ξ n n',
  awl_to_nenv Γ Ξ -> 
  uniq Ξ ->
  exp_size_wl Γ n -> 
  exp_size_wl Γ n' -> 
  n = n'.
Proof.
  intros * Ha2n Huniq Hsize. generalize dependent n'. generalize dependent Ξ.
  induction Hsize; intros * Ha2n Huniq * Hsize';
    dependent destruction Ha2n; dependent destruction Hsize'; eauto.
  - dependent destruction Huniq. eapply IHHsize in Hsize'; eauto.
  - eapply awl_to_nenv_det in H; eauto. subst.
    eapply awl_to_nenv_det in Ha2n; eauto. subst.
    eapply exp_size_work_det in H0; eauto. 
Qed.

Lemma num_occurs_in_typ_rename_tvar : forall X Y A n,
  Y `notin` ftvar_in_typ A ->
  num_occurs_in_typ X A n -> num_occurs_in_typ Y (subst_typ_in_typ (typ_var_f Y) X A) n.
Proof.
  intros. induction H0; simpl in *; try destruct_eq_atom;
  eauto using num_occurs_in_typ.
  - inst_cofinites_for num_occurs_in_typ__all; eauto.
    intros. rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
    eapply H1; eauto.
    rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
Qed.

Lemma num_occurs_in_typ_rename_tvar_neq : forall A X X0 Y n,
  num_occurs_in_typ X A n ->
  X <> Y ->
  X0 <> X ->
  num_occurs_in_typ X ({`X0 ᵗ/ₜ Y} A) n.
Proof with eauto 6 using num_occurs_in_typ.
  intros. induction H; simpl; destruct_eq_atom; eauto...
  - inst_cofinites_for num_occurs_in_typ__all. intros. inst_cofinites_with Y0. 
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2...
Qed.

Lemma num_occurs_in_typ_total : forall X A,
  lc_typ A -> exists n, num_occurs_in_typ X A n.
Proof.
  intros. induction H; destruct_conj; eauto using num_occurs_in_typ.
  - destruct (X == X0); subst; eauto using num_occurs_in_typ.
  - pick fresh X0. specialize (H0 X0).
    destruct H0 as [n].
    exists n.
    inst_cofinites_for num_occurs_in_typ__all. intros.
    erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
    eapply num_occurs_in_typ_rename_tvar_neq; eauto.
Qed.

Lemma n_iuv_size_rename : forall A X Y n,
  n_iuv_size A n -> n_iuv_size ({`Y ᵗ/ₜ X} A) n.
Proof.
  intros. induction H; simpl in *; eauto using n_iuv_size.
  - simpl. destruct_eq_atom; eauto.
  - pick fresh X0.
    inst_cofinites_with X0 (keep). 
    inst_cofinites_for n_iuv_size__all n:=n, m:=m; eauto; intros.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
    + rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
      apply num_occurs_in_typ_rename_tvar_neq; eauto.
Qed.

Lemma n_iuv_size_total : forall A,
  lc_typ A -> exists n, n_iuv_size A n.
Proof.
  intros. induction H; destruct_conj; eauto using n_iuv_size. 
  - pick fresh X. 
    specialize (H0 X).
    specialize (H X).
    destruct H0 as [n].
    apply num_occurs_in_typ_total with (X:=X) in H.
    destruct H as [m].
    exists (n + m). inst_cofinites_for n_iuv_size__all n:=n,m:=m; eauto.
    + intros.
      erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
      eapply n_iuv_size_rename; eauto.    
    + intros. erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
      eapply num_occurs_in_typ_rename_tvar; eauto.
      rewrite ftvar_in_typ_open_typ_wrt_typ_upper; auto.
Qed.

Lemma awl_to_nenv_total : forall Γ,
  ⊢ᵃʷ Γ ->
  exists Ξ, awl_to_nenv Γ Ξ.
Proof.
  intros. induction H; simpl in *; try solve [destruct_conj; eauto using awl_to_nenv].
  - apply a_wf_typ_lc in H0. apply n_iuv_size_total in H0.
    destruct H0 as [n].
    destruct IHa_wf_wwl as [Ξ]. 
    exists (x ~ nbind_var_typ n ++ Ξ).
    simpl. eauto using awl_to_nenv.
Qed.

Lemma exp_split_size_rename_var : forall Ξ1 Ξ2 e x y n m,
  uniq (Ξ2 ++ (x , (nbind_var_typ m)) :: Ξ1) ->
  y `notin` dom (Ξ2 ++ (x , (nbind_var_typ m)) :: Ξ1) ->
  exp_split_size (Ξ2 ++ (x , (nbind_var_typ m)) :: Ξ1) e n -> 
  exp_split_size (Ξ2 ++ (y , (nbind_var_typ m)) :: Ξ1) (subst_exp_in_exp (exp_var_f y) x e) n.
Proof with eauto using exp_split_size.
  intros. dependent induction H1; simpl in *...
  - destruct_eq_atom.
    + assert (binds x (nbind_var_typ m) (Ξ2 ++ (x, nbind_var_typ m) :: Ξ1)) by eauto. unify_binds...
    + apply binds_remove_mid in H1...
      econstructor... apply binds_weaken_mid...
  - remember (dom (Ξ2 ++ (x, nbind_var_typ m) :: Ξ1)). inst_cofinites_for exp_split_size__abs. subst. intros.
    replace (exp_var_f x0) with (subst_exp_in_exp (exp_var_f y) x (exp_var_f x0))...
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp...
    rewrite_env ((x0 ~ nbind_var_typ 0 ++ Ξ2) ++ (y ~ nbind_var_typ m) ++ Ξ1).
    eapply H2; eauto. simpl...
    simpl. destruct_eq_atom; eauto. 
  - remember (dom (Ξ2 ++ (x, nbind_var_typ m) :: Ξ1)). inst_cofinites_for exp_split_size__tabs n:=n,m:=m0; subst; eauto; intros.
    + inst_cofinites_with X. 
      rewrite <- subst_exp_in_exp_open_exp_wrt_typ; eauto.
      rewrite_env ((X ~ nbind_tvar_empty ++ Ξ2) ++ (y ~ nbind_var_typ m) ++ Ξ1).
      eapply H4; eauto. simpl...
Qed.

Lemma exp_split_size_rename_var_cons : forall Ξ e x y n m,
  uniq (x ~ (nbind_var_typ m) ++ Ξ) ->
  y `notin` dom (x ~ (nbind_var_typ m) ++ Ξ) ->
  exp_split_size (x ~ (nbind_var_typ m) ++ Ξ) e n -> 
  exp_split_size (y ~ (nbind_var_typ m) ++ Ξ) (subst_exp_in_exp (exp_var_f y) x e) n.
Proof.
  intros. rewrite_env (nil ++ y ~ (nbind_var_typ m) ++ Ξ).
  eapply exp_split_size_rename_var; eauto.
Qed.

Lemma exp_split_size_rename_tvar : forall Ξ1 Ξ2 e X Y n,
  uniq (Ξ2 ++ (X , nbind_tvar_empty) :: Ξ1) ->
  Y `notin` dom (Ξ2 ++ (X , nbind_tvar_empty) :: Ξ1) ->
  exp_split_size (Ξ2 ++ (X , nbind_tvar_empty) :: Ξ1) e n -> 
  exp_split_size (Ξ2 ++ (Y , nbind_tvar_empty) :: Ξ1) (subst_typ_in_exp (typ_var_f Y) X e) n.
Proof with eauto using exp_split_size.
  intros. dependent induction H1; simpl in *...
  - apply binds_remove_mid_diff_bind in H1.
    econstructor.
    apply binds_weaken_mid...
    solve_false.
  - remember (dom (Ξ2 ++ (X, nbind_tvar_empty) :: Ξ1)). inst_cofinites_for exp_split_size__abs. subst. 
    intros. inst_cofinites_with x.
    replace (exp_var_f x) with (subst_typ_in_exp (typ_var_f Y) X (exp_var_f x))...
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp...
    rewrite_env ((x ~ nbind_var_typ 0 ++ Ξ2) ++ (Y ~ nbind_tvar_empty) ++ Ξ1).
    eapply H2...
    simpl...
  - remember (dom (Ξ2 ++ (X, nbind_tvar_empty) :: Ξ1)). inst_cofinites_for exp_split_size__tabs n:=n,m:=m; subst; 
    intros; inst_cofinites_with x.
    + replace (`X0) with (subst_typ_in_typ (typ_var_f Y) X (`X0))...
      rewrite <- subst_typ_in_exp_open_exp_wrt_typ...
      rewrite_env ((X0 ~ nbind_tvar_empty  ++ Ξ2) ++ (Y ~ nbind_tvar_empty) ++ Ξ1).
      eapply H4...
      simpl...
      simpl. destruct_eq_atom; eauto.
    + erewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
      apply n_iuv_size_rename; eauto.
    + lia.
  - econstructor; eauto.
    + eapply n_iuv_size_rename...
    + lia.
  - econstructor; eauto.
    + eapply n_iuv_size_rename...
    + lia.
Qed.

Lemma exp_split_size_rename_tvar_cons : forall Ξ e X Y n,
  uniq (X ~ nbind_tvar_empty ++ Ξ) ->
  Y `notin` dom (X ~ nbind_tvar_empty ++ Ξ) ->
  exp_split_size (X ~ nbind_tvar_empty ++ Ξ) e n -> 
  exp_split_size (Y ~ nbind_tvar_empty ++ Ξ) (subst_typ_in_exp (typ_var_f Y) X e) n.
Proof.
  intros. rewrite_env (nil ++ Y ~ nbind_tvar_empty ++ Ξ).
  eapply exp_split_size_rename_tvar; eauto.
Qed.
    
Lemma exp_split_size_total : forall Ξ e,
  uniq Ξ ->
  n_wf_exp Ξ e ->
  exists n, exp_split_size Ξ e n.
Proof.
  intros. induction H0; try solve [destruct_conj; simpl in *; eauto using exp_split_size].
  - remember (dom Ξ). pick fresh x. inst_cofinites_with x (keep). 
    destruct H2 as [n0].
    + subst. constructor; eauto.
    + exists n0.
      inst_cofinites_for exp_split_size__abs; eauto. subst. intros.
      erewrite <- subst_exp_in_exp_open_exp_wrt_exp_var2; eauto.
      eapply exp_split_size_rename_var_cons; simpl in *; eauto...
  - apply IHn_wf_exp1 in H as Hn1.
    apply IHn_wf_exp2 in H as Hn2. destruct_conjs; eauto using exp_split_size.
  - remember (dom Ξ). pick fresh X. inst_cofinites_with X (keep).
    destruct H2 as [n].
    + subst. constructor; eauto.
    + dependent destruction H1. 
      eapply n_iuv_size_total in H0. 
      destruct H0 as [m].
      dependent destruction H4.
      exists ((1 + n) * (2 + m0)).
      inst_cofinites_for exp_split_size__tabs n:=n,m:=m0; eauto; intros.
      * subst. 
        replace (e ᵉ^^ₜ ` X0) with (subst_typ_in_exp (typ_var_f X0) X (e ᵉ^^ₜ `X))...
        eapply exp_split_size_rename_tvar_cons; simpl; eauto.
        -- rewrite subst_typ_in_exp_open_exp_wrt_typ; eauto.
           simpl. destruct_eq_atom; eauto.
           rewrite subst_typ_in_exp_fresh_eq; eauto.  
      * replace (A ᵗ^ₜ X0) with (subst_typ_in_typ (typ_var_f X0) X (A ᵗ^ₜ X))...
        apply n_iuv_size_rename; eauto.
        rewrite subst_typ_in_typ_open_typ_wrt_typ; eauto.
        simpl. destruct_eq_atom; eauto.
        rewrite subst_typ_in_typ_fresh_eq; eauto.
  - apply n_iuv_size_total in H1. 
    destruct H1 as [m].
    destruct IHn_wf_exp as [n]; auto.
    exists ((1 + n) * (2 + m)). eauto using exp_split_size.
  - apply n_iuv_size_total in H1. 
    destruct H1 as [m].
    destruct IHn_wf_exp as [n]; auto.
    exists ((1 + n) * (2 + m)). eauto using exp_split_size.
Qed.

Inductive equiv_nenv : nenv -> nenv -> Prop :=
  | eq_nenv_base : forall Ξ, equiv_nenv Ξ Ξ
  | eq_nenv__tvar : forall Ξ Ξ' X,
      equiv_nenv Ξ Ξ' ->
      equiv_nenv ((X, nbind_tvar_empty) :: Ξ) ((X, nbind_tvar_empty) :: Ξ')
  | eq_nenv__stvar : forall Ξ Ξ' X,
      equiv_nenv Ξ Ξ' ->
      equiv_nenv ((X, nbind_stvar_empty) :: Ξ) ((X, nbind_stvar_empty) :: Ξ')
  | eq_nenv__etvar : forall Ξ Ξ' X,
      equiv_nenv Ξ Ξ' ->
      equiv_nenv ((X, nbind_etvar_empty) :: Ξ) ((X, nbind_etvar_empty) :: Ξ')
  | eq_nenv__var : forall Ξ Ξ' x n n',
      equiv_nenv Ξ Ξ' ->
      equiv_nenv ((x, nbind_var_typ n) :: Ξ) ((x, nbind_var_typ n') :: Ξ').

Lemma equiv_nenv_binds_var : forall Ξ Ξ' x n,
  equiv_nenv Ξ Ξ' ->
  binds x (nbind_var_typ n) Ξ ->
  exists n', binds x (nbind_var_typ n') Ξ'.
Proof.
  intros. induction H; destruct_binds; destruct_conj; eauto.
  - apply IHequiv_nenv in H2. destruct_conj; eauto.
  - apply IHequiv_nenv in H2. destruct_conj; eauto.
  - apply IHequiv_nenv in H2. destruct_conj; eauto.
  - apply IHequiv_nenv in H2. destruct_conj; eauto.
Qed.

Lemma n_wf_exp_equiv_nenv : forall Ξ Ξ' e,
  n_wf_exp Ξ e -> equiv_nenv Ξ Ξ' -> n_wf_exp Ξ' e. 
Proof with eauto using equiv_nenv, n_wf_exp.
  intros * Hwf Heq. generalize dependent Ξ'. induction Hwf; eauto using n_wf_exp, equiv_nenv; simpl; intros...
  - eapply equiv_nenv_binds_var in H; eauto.
    destruct H as [n']... 
  - inst_cofinites_for n_wf_exp__abs.
    intros. inst_cofinites_with x.
    eapply H0; eauto... simpl...
  - inst_cofinites_for n_wf_exp__tabs.
    intros. inst_cofinites_with X.
    eapply H0; eauto... simpl...
Qed.

Lemma equiv_nenv_same_dom : forall Ξ Ξ',
  equiv_nenv Ξ Ξ' -> dom Ξ = dom Ξ'.
Proof.
  intros. induction H; simpl; try rewrite IHequiv_nenv; auto.
Qed.

Lemma uniq_equiv_nenv : forall Ξ Ξ',
  uniq Ξ -> equiv_nenv Ξ Ξ' -> uniq Ξ'. 
Proof.
  intros. induction H0; eauto using uniq; econstructor.
  - dependent destruction H. auto.
  - dependent destruction H. auto.  
    erewrite <- equiv_nenv_same_dom; eauto.
  - dependent destruction H. auto.
  - dependent destruction H. auto.  
    erewrite <- equiv_nenv_same_dom; eauto.
  - dependent destruction H. auto.
  - dependent destruction H. auto.  
    erewrite <- equiv_nenv_same_dom; eauto.
  - dependent destruction H. auto.
  - dependent destruction H. auto.  
    erewrite <- equiv_nenv_same_dom; eauto.
Qed.

Lemma exp_size_rename_tvar : forall Ξ1 Ξ2 e X Y n m,
  uniq (Ξ2 ++ (X , nbind_tvar_empty) :: Ξ1) ->
  Y `notin` dom (Ξ2 ++ (X , nbind_tvar_empty) :: Ξ1) ->
  exp_size (Ξ2 ++ (X , nbind_tvar_empty) :: Ξ1) e n m -> 
  exp_size (Ξ2 ++ (Y , nbind_tvar_empty) :: Ξ1) (subst_typ_in_exp (typ_var_f Y) X e) n m.
Proof.
  intros. dependent induction H1; simpl in *; eauto using exp_size.
  - remember ( dom (Ξ2 ++ (X, nbind_tvar_empty) :: Ξ1)). inst_cofinites_for exp_size__abs m:=m; eauto. intros. subst.
    subst. replace (exp_var_f x) with (subst_typ_in_exp (typ_var_f Y) X (exp_var_f x)); auto.
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp.
    rewrite_env ((x ~ nbind_var_typ n ++ Ξ2) ++ (Y ~ nbind_tvar_empty) ++ Ξ1).
    eapply H3; eauto. simpl...
    + constructor; eauto.
  - econstructor; eauto.
    apply exp_split_size_rename_tvar; eauto.  
  - remember ( dom (Ξ2 ++ (X, nbind_tvar_empty) :: Ξ1)). 
    inst_cofinites_for exp_size__tabs n:=n,m:=m,a:=a; eauto; intros; subst.
    + erewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
      apply n_iuv_size_rename; eauto.
    + erewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2; eauto.
      rewrite_env ((X0 ~ nbind_tvar_empty ++ Ξ2) ++ (Y ~ nbind_tvar_empty) ++ Ξ1).
      eapply H1; eauto. simpl...
      constructor; eauto. 
  - econstructor; eauto.
    apply n_iuv_size_rename; eauto.
  - econstructor; eauto.
    apply n_iuv_size_rename; eauto.
Qed.

Lemma exp_size_rename_tvar_cons : forall Ξ e X Y n m,
  uniq (X ~ nbind_tvar_empty ++ Ξ) ->
  Y `notin` dom (X ~ nbind_tvar_empty ++ Ξ) ->
  exp_size (X ~ nbind_tvar_empty ++ Ξ) e n m -> 
  exp_size (Y ~ nbind_tvar_empty ++ Ξ) (subst_typ_in_exp (typ_var_f Y) X e) n m.
Proof.
  intros. rewrite_env (nil ++ Y ~ nbind_tvar_empty ++ Ξ).
  eapply exp_size_rename_tvar; eauto.
Qed.

Lemma exp_size_rename_var : forall Ξ1 Ξ2 e x y n m p,
  uniq (Ξ2 ++ (x , (nbind_var_typ p)) :: Ξ1) ->
  y `notin` dom (Ξ2 ++ (x , (nbind_var_typ p)) :: Ξ1) ->
  exp_size (Ξ2 ++ (x , (nbind_var_typ p)) :: Ξ1) e n m -> 
  exp_size (Ξ2 ++ (y , (nbind_var_typ p)) :: Ξ1) (subst_exp_in_exp (exp_var_f y) x e) n m.
Proof.
  intros. dependent induction H1; simpl in *; eauto using exp_size.
  - destruct_eq_atom; eauto using exp_size.
  - remember (dom (Ξ2 ++ (x, nbind_var_typ p) :: Ξ1)).
    inst_cofinites_for exp_size__abs m:=m; eauto. intros.
    subst. inst_cofinites_with x0. subst.
    replace (exp_var_f x0) with (subst_exp_in_exp (exp_var_f y) x (exp_var_f x0))...
    erewrite <- subst_exp_in_exp_open_exp_wrt_exp; eauto.
    rewrite_env ((x0 ~ nbind_var_typ n ++ Ξ2) ++ (y ~ nbind_var_typ p) ++ Ξ1).
    eapply H3; eauto. simpl...
    + constructor; eauto.
    + simpl. destruct_eq_atom; eauto.
  - econstructor; eauto.
    apply exp_split_size_rename_var; eauto.
  - remember (dom (Ξ2 ++ (x, nbind_var_typ p) :: Ξ1)).
    inst_cofinites_for exp_size__tabs n:=n,m:=m,a:=a; eauto; intros; subst.
    + rewrite <- subst_exp_in_exp_open_exp_wrt_typ; eauto.
      rewrite_env ((X ~ nbind_tvar_empty ++ Ξ2) ++ (y ~ nbind_var_typ p) ++ Ξ1).
      eapply H1; eauto. simpl...
      constructor; auto.
Qed.

Lemma exp_size_rename_var_cons : forall Ξ e x y n m p,
  uniq (x ~ (nbind_var_typ p) ++ Ξ) ->
  y `notin` dom (x ~ (nbind_var_typ m) ++ Ξ) ->
  exp_size (x ~ (nbind_var_typ p) ++ Ξ) e n m -> 
  exp_size (y ~ (nbind_var_typ p) ++ Ξ) (subst_exp_in_exp (exp_var_f y) x e) n m.
Proof.
  intros. rewrite_env (nil ++ y ~ (nbind_var_typ p) ++ Ξ).
  eapply exp_size_rename_var; eauto.
Qed.

Lemma exp_size_total' : forall Ξ Ξ' e n,
  uniq Ξ ->
  n_wf_exp Ξ e ->
  equiv_nenv Ξ Ξ' ->
  exists m, exp_size Ξ' e n m.
Proof with eauto using exp_size.
  intros. generalize dependent n. generalize dependent Ξ'. induction H0; eauto using exp_size; intros.  
  - remember (dom Ξ). pick fresh x. inst_cofinites_with x (keep). subst.
    assert (uniq (x ~ nbind_var_typ 0 ++ Ξ) ) by auto.
    assert (equiv_nenv (x ~ nbind_var_typ 0 ++ Ξ) (x ~ nbind_var_typ n ++ Ξ')) by (simpl; eauto using equiv_nenv).
    specialize (H3 H5 (x ~ nbind_var_typ n ++ Ξ') H6 n). destruct H3 as [m].
    exists (1+n+m).  remember (dom Ξ). inst_cofinites_for exp_size__abs m:=m; eauto; intros; subst.
    replace (e ᵉ^^ₑ exp_var_f x0) with (subst_exp_in_exp (exp_var_f x0) x (e ᵉ^^ₑ exp_var_f x))...
    eapply exp_size_rename_var_cons; eauto; simpl.
    + constructor. eapply uniq_equiv_nenv with (Ξ:=Ξ); eauto.
      erewrite <- equiv_nenv_same_dom with (Ξ:=Ξ); eauto.
    + erewrite <- equiv_nenv_same_dom with (Ξ:=Ξ); eauto.
    + rewrite subst_exp_in_exp_open_exp_wrt_exp; eauto.
      simpl. destruct_eq_atom; eauto.
      rewrite subst_exp_in_exp_fresh_eq; eauto.
  - eapply n_wf_exp_equiv_nenv in H0_; eauto. 
    apply exp_split_size_total in H0_... destruct H0_ as [s].
    specialize (IHn_wf_exp1 H _ H1 n).
    specialize (IHn_wf_exp2 H _ H1 (s * n + s + n)).
    destruct IHn_wf_exp1 as [m1].
    destruct IHn_wf_exp2 as [m2].
    exists (1 + m1 + m2 + s * m2). 
    eapply exp_size__app; eauto.
    eapply uniq_equiv_nenv; eauto. 
  - remember (dom Ξ). pick fresh X. inst_cofinites_with X. subst.
    assert (uniq (X ~ nbind_tvar_empty ++ Ξ)) by auto.
    assert (equiv_nenv (X ~ nbind_tvar_empty ++ Ξ) (X ~ nbind_tvar_empty ++ Ξ')) by (simpl; eauto using equiv_nenv).
    specialize (H1 H3 (X ~ nbind_tvar_empty ++ Ξ') H4 n). destruct H1 as [m].
    dependent destruction H1.
    exists (1 + m * n + m + n). 
    remember (dom Ξ). inst_cofinites_for exp_size__tabs a:=a,m:=m; eauto; intros; subst.
    + erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
      eapply n_iuv_size_rename; eauto. 
    + replace (e ᵉ^^ₜ ` X0) with (subst_typ_in_exp (typ_var_f X0) X (e ᵉ^^ₜ `X))...
      eapply exp_size_rename_tvar_cons; eauto; simpl.
      * eapply uniq_equiv_nenv; eauto.
      * erewrite <- equiv_nenv_same_dom with (Ξ:=Ξ); eauto.
      * rewrite subst_typ_in_exp_open_exp_wrt_typ; eauto.
        simpl. destruct_eq_atom; eauto.
        rewrite subst_typ_in_exp_fresh_eq; eauto.
  - apply n_iuv_size_total in H1. destruct H1 as [n0].
    specialize (IHn_wf_exp H _ H2 (n0 * n + n0 + n)). destruct IHn_wf_exp as [m].
    exists (1 + m * n + m + n).
    econstructor; eauto.
  - apply n_iuv_size_total in H1. destruct H1 as [n0].
    specialize (IHn_wf_exp H _ H2 n0). destruct IHn_wf_exp as [m].
    exists (1 + m * n + m + n).
    eapply exp_size__anno; eauto.
Qed.

Lemma equiv_nenv_refl : forall Ξ,
  equiv_nenv Ξ Ξ.
Proof.
  intros. induction Ξ; eauto using equiv_nenv.  
Qed.

Lemma exp_size_total : forall Ξ e n,
  uniq Ξ ->
  n_wf_exp Ξ e ->  
  exists m, exp_size Ξ e n m.
Proof.
  intros. eapply exp_size_total' with (Ξ':=Ξ); eauto.
  apply equiv_nenv_refl.
Qed.


Lemma exp_size_conts_total : forall Ξ cs n,
  uniq Ξ ->
  n_wf_conts Ξ cs ->
  exists m, exp_size_conts Ξ cs n m
with exp_size_contd_total : forall Ξ cd n,
  uniq Ξ ->
  n_wf_contd Ξ cd ->
  exists m, exp_size_contd Ξ cd n m.
Proof with eauto  using exp_size_conts.
  - clear exp_size_conts_total. intros. generalize dependent n. induction H0; intros...
    + eapply exp_size_contd_total with (n:=n) in H0... destruct_conj; eauto.
    + apply n_iuv_size_total in H0. 
      destruct H0 as [b].
      specialize (IHn_wf_conts H ((2 + b) * n)). 
      destruct_conj; eauto.
    + apply n_iuv_size_total in H0. 
      destruct H0 as [a].
      apply n_iuv_size_total in H1.
      destruct H1 as [b].
      specialize (IHn_wf_conts H (2 + a * (2 + b) + n)). 
      destruct_conj; eauto.
    + apply n_iuv_size_total in H0. 
      destruct H0 as [a].
      specialize (IHn_wf_conts H (2 + a + n)). 
      destruct_conj; eauto. 
  - clear exp_size_contd_total. intros. generalize dependent n. induction H0; intros.
    + apply n_iuv_size_total in H0. 
      destruct H0 as [a].
      specialize (IHn_wf_contd H (1 + n + a)).
      destruct_conj; eauto.
    + eapply exp_size_total with (n:=n) in H as Hesz; eauto.
      eapply exp_size_conts_total with (n:=n) in H1; eauto.
      destruct_conj; eauto. 
    + apply n_iuv_size_total in H0. 
      destruct H0 as [a].
      specialize (IHn_wf_contd H (1 + a + n)).
      destruct_conj; eauto.
Qed.

Lemma exp_size_work_total : forall Ξ w,
  uniq Ξ ->
  n_wf_work Ξ w ->  
  exists n, exp_size_work Ξ w n.
Proof with eauto using exp_size_work.
  intros. induction H0...
  - apply exp_split_size_total in H0 as Hs...
    destruct Hs as [s].
    apply exp_size_conts_total with (n:=s) in H1 as Hc...
    destruct Hc as [m].
    apply exp_size_total with (n:=0) in H0...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H1. destruct H1 as [n].
    apply exp_size_total with (n:=n) in H0...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n].
    apply exp_size_contd_total with (n:=n) in H1...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply exp_size_contd_total with (n:=(1+n1+n2)) in H2...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0.
    destruct H0 as [a].
    apply n_iuv_size_total in H1.
    destruct H1 as [b].
    apply exp_size_total with (n:=a+b) in H2...
    apply exp_size_conts_total with (n:=a+b) in H3...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply exp_size_conts_total with (n:=((2+n2)*n1)) in H2...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply n_iuv_size_total in H2. destruct H2 as [n].
    apply exp_size_conts_total with (n:=(2+n2*(2+n)+n1)) in H3...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply exp_size_conts_total with (n:=(2+n1+n2)) in H2...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply exp_size_contd_total with (n:=(1+n1+n2)) in H4...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. 
    destruct H0 as [n].
    apply exp_size_conts_total with (n:=n) in H1...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. 
    destruct H0 as [n].
    apply exp_size_contd_total with (n:=n) in H2...
    destruct_conj; eauto.
Qed.

Lemma binds_var_typ_binds_var_num : forall Γ Ξ x A,
  ⊢ᵃʷ Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ -> 
  awl_to_nenv Γ Ξ ->
  exists n, binds x (nbind_var_typ n) Ξ.
Proof.
  intros. dependent induction H1; eauto; destruct_binds.
  - dependent destruction H2. exists n; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H4; destruct_conj; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H1; destruct_conj; eauto.
 Unshelve. inversion H0.
Qed.

Lemma a_wf_exp_n_wf_exp' : forall Γ Ξ Ξ' e,
  ⊢ᵃʷ Γ ->
  a_wf_exp (awl_to_aenv Γ) e -> 
  (awl_to_nenv Γ Ξ) -> 
  equiv_nenv Ξ Ξ' ->
  n_wf_exp Ξ' e.
Proof with eauto using n_wf_exp.
  intros * Hwfwl Hwf Htrans Heq. generalize dependent Ξ. generalize dependent Ξ'. dependent induction Hwf; intros; eauto 4 using n_wf_exp.
  - eapply binds_var_typ_binds_var_num in Htrans; eauto.
    destruct Htrans as [n]...
    eapply equiv_nenv_binds_var in H0; eauto.
    destruct_conj...
  - apply a_wf_typ_lc in H as Hlc. apply n_iuv_size_total in Hlc.
    destruct Hlc as [n].  
    inst_cofinites_for n_wf_exp__abs; eauto. intros. inst_cofinites_with x.
    eapply H1 with (Γ:= x ~ᵃ T ;ᵃ Γ) (Ξ:= (x , nbind_var_typ n) :: Ξ)...
    econstructor...
  - inst_cofinites_for n_wf_exp__tabs; eauto; intros; inst_cofinites_with X.
    + eapply H1 with (Γ:= X ~ᵃ □ ;ᵃ Γ); eauto...
      econstructor...
      econstructor...
Qed.

Lemma a_wf_exp_n_wf_exp : forall Γ Ξ e,
  ⊢ᵃʷ Γ ->
  a_wf_exp (awl_to_aenv Γ) e -> 
  (awl_to_nenv Γ Ξ) -> 
  n_wf_exp Ξ e.
Proof.
  intros. eapply a_wf_exp_n_wf_exp' with (Ξ':=Ξ); eauto.
  apply equiv_nenv_refl.
Qed.

Lemma a_wf_conts_n_wf_conts : forall Γ Ξ cs,
  ⊢ᵃʷ Γ -> a_wf_conts (awl_to_aenv Γ) cs -> (awl_to_nenv Γ Ξ) -> n_wf_conts Ξ cs
with a_wf_contd_n_wf_contd : forall Γ Ξ cd,
  ⊢ᵃʷ Γ -> a_wf_contd (awl_to_aenv Γ) cd -> (awl_to_nenv Γ Ξ) -> n_wf_contd Ξ cd.
Proof with eauto using n_wf_conts, n_wf_contd, a_wf_exp_n_wf_exp.
  - intros. clear a_wf_conts_n_wf_conts. dependent induction H0...
  - intros. clear a_wf_contd_n_wf_contd. dependent induction H0...
    + dependent destruction H1; eauto 6 using n_wf_contd.
Qed.

Lemma a_wf_work_n_wf_work : forall Γ Ξ w,
  ⊢ᵃʷ Γ ->
  a_wf_work (awl_to_aenv Γ) w -> 
  (awl_to_nenv Γ Ξ) -> 
  n_wf_work Ξ w.
Proof with eauto 7 using a_wf_conts_n_wf_conts, a_wf_contd_n_wf_contd, a_wf_exp_n_wf_exp, n_wf_work.
  intros * Hwfwl Hwf Htrans. dependent induction Hwf;  
    try solve [dependent destruction Htrans; eauto 7 using a_wf_conts_n_wf_conts, a_wf_contd_n_wf_contd, a_wf_exp_n_wf_exp, n_wf_work].
  - dependent destruction H...
  - dependent destruction H...
  - dependent destruction H...
    dependent destruction H1...
Qed.

Lemma awl_to_nenv_same_dom : forall Γ Ξ,
  awl_to_nenv Γ Ξ -> dom Ξ = dom (⌊ Γ ⌋ᵃ).
Proof.
  intros Γ Ξ Hnenv. dependent induction Hnenv; eauto.
  simpl. rewrite IHHnenv. reflexivity.
Qed.


Lemma awl_to_nenv_uniq : forall Γ Ξ,
  awl_to_nenv Γ Ξ -> uniq (⌊ Γ ⌋ᵃ) -> uniq Ξ.
Proof.
  intros Γ Ξ Hnenv Huniq. dependent induction Hnenv; eauto.
  dependent destruction Huniq.
  erewrite <- awl_to_nenv_same_dom in H0; eauto.
Qed.

Lemma exp_size_wl_total : forall Γ,
  ⊢ᵃʷ Γ ->
  exists n, exp_size_wl Γ n.
Proof.
  intros. induction H; eauto; try solve [destruct_conj; eauto using exp_size_wl].
  - apply awl_to_nenv_total in H0 as Hwfenv. destruct Hwfenv as [Ξ].
    destruct IHa_wf_wwl as [n].
    eapply a_wf_work_n_wf_work in H; eauto.
    apply exp_size_work_total in H; eauto. destruct H as [m].
    exists (m + n). eauto using exp_size_wl.
    eapply awl_to_nenv_uniq; eauto.
Qed.

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
  | contd_infapp _ cs => 5 + judge_size_conts cs
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

Fixpoint lookup_tvar_bind (Σ : aenv) (X : atom) : option abind :=
  match Σ with
  | nil => None
  | (Y, b) :: Σ' => if X == Y then Some b else lookup_tvar_bind Σ' X
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

Fixpoint iu_size (A : typ) : nat :=
  match A with
    | typ_arrow A1 A2 => iu_size A1 + iu_size A2
    | typ_all A => iu_size A
    | typ_union A1 A2 => 2 + iu_size A1 + iu_size A2
    | typ_intersection A1 A2 => 2 + iu_size A1 + iu_size A2
    | _ => 0
  end.


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

Lemma binds_lookup_tvar_bind : forall Σ X B,
  ⊢ᵃ Σ -> B = abind_tvar_empty \/ B = abind_stvar_empty \/ B = abind_etvar_empty ->
  binds X B Σ <-> lookup_tvar_bind Σ X = Some B.
Proof.
  intros. induction H; simpl.
  - split; intros; inversion H.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H2; auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H2; auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H2; auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
  - destruct_eq_atom.
    + split; intros.
      * destruct_binds; auto.
        destruct H0 as [Hcontra | [Hcontra | Hcontra]];
        exfalso; eapply binds_dom_contradiction; eauto. 
      * inversion H3. auto.
    + split; intros.
      * destruct_binds; auto.
        apply IHa_wf_env; auto.
      * eapply binds_cons; eauto. apply IHa_wf_env; auto.
Qed.

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
  | contd_infapp _ cs => inftapp_depth_conts_tail_rec cs ans
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
  | contd_infapp _ cs => infabs_judge_size_conts cs
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
  | contd_infapp _ cs => inftapp_judge_size_conts cs
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

(* Lemma a_iuv_size_subst_mono : forall Σ A X A0 n,
  Σ ᵗ⊢ᵃₘ A ->
  iuv_size Σ (subst_typ_in_typ A X A0) n ->
  iuv_size Σ A0 n.
Proof.
  intros Σ A X A0 Hmono.
  induction A0; simpl; auto.
  destruct (eq_dec X0 X); subst; simpl; eauto.
  eapply iuv_size_mono; eauto.
Qed. *)
(* 
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
Qed. *)

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

Lemma apply_conts_exp_size : forall Ξ c A w a n m,
  uniq Ξ -> apply_conts c A w -> n_iuv_size A a ->
  exp_size_conts Ξ c a n -> exp_size_work Ξ w m -> m = n.
Proof.
  intros Ξ c A w a n m Huniq Happly Hsize1 Hsize2 Hsize3.
  induction Happly; dependent destruction Hsize2; dependent destruction Hsize3; eauto.
  - eapply n_iuv_size_det in Hsize1; eauto. subst.
    eapply exp_size_contd_det in H; eauto.
  - eapply n_iuv_size_det in Hsize1; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_conts_det in H2; eauto.
  - eapply n_iuv_size_det in Hsize1; eauto.
    eapply n_iuv_size_det in H; eauto.
    eapply n_iuv_size_det in H0; eauto. subst.
    eapply exp_size_conts_det in H4; eauto.
  - eapply n_iuv_size_det in Hsize1; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_conts_det in H2; eauto.
Qed.

(* Lemma apply_conts_exp_size : forall Σ c A w n m,
  apply_conts c A w -> exp_size_conts Σ c n -> exp_size_work Σ w m -> n = m.
Proof.
  intros Σ c A w n m Happly Hsize1 Hsize2.
  induction Happly; dependent destruction Hsize1; dependent destruction Hsize2;
    try solve [ eapply exp_size_contd_det in H; eauto];
    try solve [ eapply exp_size_conts_det in H; eauto]; eauto.
Qed.

Lemma apply_contd_exp_size : forall Σ c A B w n m,
  apply_contd c A B w -> exp_size_work Σ w n -> exp_size_contd Σ c m -> n <= m.
Proof.
  intros Σ c A B w n m Happly Hsize1 Hsize2. induction Happly.
  - dependent destruction Hsize1. dependent destruction Hsize2.
    eapply exp_size_conts_det in H2; eauto; subst; eauto. 
    (* eapply exp_size_det in H0; eauto; subst; eauto. *)
    assert (m0 * (1 + iu_size A) <= ne * (1 + n0)).
    { eapply mult_le_compat; eauto. admit. lia. } lia.
  - dependent destruction Hsize1.
    dependent destruction Hsize2.
    eapply exp_size_contd_det in H; eauto; subst; eauto.
  - dependent destruction Hsize1.
    dependent destruction Hsize2.
    eapply exp_size_contd_det in H; eauto; subst; eauto.
Admitted. *)

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

(* Lemma exp_size_wl_aworklist_subst' : forall Γ2 Γ X A Γ1 Γ1' Γ2',
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
Admitted. *)

Lemma lookup_tvar_bind_etvar : forall Γ2 Γ1 X X0,
  X <> X0 ->
  lookup_tvar_bind (⌊ Γ2 ⧺ Γ1 ⌋ᵃ) X = lookup_tvar_bind (⌊ Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) X.
Proof.
  intros Γ2. induction Γ2; simpl; intros; eauto.
  - destruct (X == X0); subst; auto; try contradiction.
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
(* Proof.
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
    admit. *)
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
(* Proof.
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
Qed. *)
Admitted.

Lemma split_depth_rec_non_zero_non_mono : forall A Γ n,
  ⊢ᵃʷ Γ -> split_depth_rec (⌊ Γ ⌋ᵃ) A n > 0 ->
  a_mono_typ (awl_to_aenv Γ) A -> False.
(* Proof.
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
Qed. *)
Admitted.

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

(* Lemma split_depth_rec_subst : forall B Γ2 X A Γ1 n,
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
Qed. *)

(* Lemma exp_size_weaken_work : forall Γ e w,
  ⊢ᵃʷₛ Γ -> exp_size (w ⫤ᵃ Γ) e = exp_size Γ e
with body_size_weaken_work : forall Γ b w,
  ⊢ᵃʷₛ Γ -> body_size (w ⫤ᵃ Γ) b = body_size Γ b.
Proof.
  intros Γ e w Hwf. dependent destruction e; simpl; auto.
  intros Γ e w Hwf. dependent destruction e; simpl; auto.
Qed.

Corollary rename_var_a_wf_exp_cons : forall Γ x y e A,
  x ~ (abind_var_typ A) ++ ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ e  ->
  y ~ (abind_var_typ A) ++ ⌊ Γ ⌋ᵃ ᵉ⊢ᵃ {exp_var_f y ᵉ/ₑ x} e.
Admitted. *)

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
(* Proof.
  intros c A B.
  destruct c; eauto using apply_contd.
  destruct (le_lt_dec (iu_size A) n); eauto.
  right. intros [w Happly]. dependent destruction Happly. lia.
Qed. *)
Admitted.

Inductive le_nenv : nenv -> nenv -> Prop :=
  | le_nenv_base : forall Ξ, le_nenv Ξ Ξ
  | le_nenv__tvar : forall Ξ Ξ' X,
      le_nenv Ξ Ξ' ->
      le_nenv ((X, nbind_tvar_empty) :: Ξ) ((X, nbind_tvar_empty) :: Ξ')
  | le_nenv__stvar : forall Ξ Ξ' X,
      le_nenv Ξ Ξ' ->
      le_nenv ((X, nbind_stvar_empty) :: Ξ) ((X, nbind_stvar_empty) :: Ξ')
  | le_nenv__etvar : forall Ξ Ξ' X,
      le_nenv Ξ Ξ' ->
      le_nenv ((X, nbind_etvar_empty) :: Ξ) ((X, nbind_etvar_empty) :: Ξ')
  | le_nenv__var : forall Ξ Ξ' x n n',
      le_nenv Ξ Ξ' -> n <= n' ->
      le_nenv ((x, nbind_var_typ n) :: Ξ) ((x, nbind_var_typ n') :: Ξ').

#[local] Hint Constructors le_nenv : core.

Lemma le_nenv_same_dom : forall Ξ Ξ',
  le_nenv Ξ Ξ' -> dom Ξ = dom Ξ'.
Proof.
  intros Ξ Ξ' Hle. dependent induction Hle; simpl;
    try rewrite IHHle; reflexivity.
Qed.

Lemma le_nenv__binds_le : forall Ξ x n Ξ' n',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  binds x (nbind_var_typ n) Ξ -> binds x (nbind_var_typ n') Ξ' ->
  n <= n'.
Proof.
  intros Ξ x n Ξ' n' Huniq Hle Hbinds Hbinds'.
  dependent induction Hle; eauto.
  - unify_binds. eauto.
  - dependent destruction Huniq. destruct_binds; eauto.
  - dependent destruction Huniq. destruct_binds; eauto.
  - dependent destruction Huniq. destruct_binds; eauto.
  - dependent destruction Huniq. destruct_binds; eauto.
    + exfalso. eauto.
    + exfalso. erewrite le_nenv_same_dom in H; eauto.
Qed.

Lemma exp_split_size_le : forall Ξ Ξ' e n n' m m',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  exp_split_size Ξ e m -> exp_split_size Ξ' e m' ->
  n <= n' -> m <= m'.
Proof.
  intros Ξ Ξ' e n n' m m' Huniq Hle Hsize.
  generalize dependent m'. generalize dependent n'. generalize dependent Ξ'.
  dependent induction Hsize; intros * Hle * Hsize' Hlen; dependent destruction Hsize'; try lia.
  - eapply le_nenv__binds_le; eauto.
  - remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
    eapply H0 in H1; simpl; eauto.
  - eapply IHHsize1 in Hsize'1; eauto.
    eapply IHHsize2 in Hsize'2; eauto. lia.
  - remember (dom Ξ). pick fresh X. subst. inst_cofinites_with X. simpl in *.
    eapply H0 in H3; simpl; eauto.
    eapply n_iuv_size_det in H1; eauto. subst.
    eapply mult_le_compat_r with (p := S (S m)) in H3. lia.
  - eapply IHHsize in Hsize'; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply mult_le_compat_r with (p := S (S m)) in Hsize'. lia.
  - eapply IHHsize in Hsize'; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply mult_le_compat_r with (p := S (S m)) in Hsize'. lia.
Qed.

Lemma exp_size_le : forall Ξ Ξ' e n n' m m',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  exp_size Ξ e n m -> exp_size Ξ' e n' m' ->
  n <= n' -> m <= m'.
Proof.
  intros Ξ Ξ' e n n' m m' Huniq Hle Hsize.
  generalize dependent m'. generalize dependent n'. generalize dependent Ξ'.
  dependent induction Hsize; intros * Hle * Hsize' Hlen; dependent destruction Hsize'; try lia.
  - remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
    eapply H0 in H2; simpl; eauto. lia.
  - eapply exp_split_size_le in H1; eauto.
    eapply mult_le_compat with (p := n) (q := n0) in H1 as Hlesn; eauto.
    eapply IHHsize1 in Hsize'1; eauto.
    eapply IHHsize2 in Hsize'2; eauto; try lia.
    eapply mult_le_compat with (p := m2) (q := m3) in H1 as Hlesm; eauto. lia.
  - remember (dom Ξ). pick fresh X. inst_cofinites_with X.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply H1 in H4; eauto.
    eapply mult_le_compat with (p := n) (q := n0) in H4 as Hlemn; eauto. lia.
    eapply le_nenv__tvar; eauto.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply mult_le_compat_l with (p := a) in Hlen as Hlean; eauto.
    eapply IHHsize in Hsize'; eauto; try lia.
    eapply mult_le_compat with (p := n) (q := n0) in Hsize' as Hlemn; eauto. lia.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply IHHsize in Hsize'; eauto.
    eapply mult_le_compat with (p := n) (q := n0) in Hsize' as Hlemn; eauto. lia.
Qed.

Lemma exp_size_conts_le : forall c Ξ Ξ' n n' m m',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  exp_size_conts Ξ c n m -> exp_size_conts Ξ' c n' m' ->
  n <= n' -> m <= m'
with exp_size_contd_le : forall c Ξ Ξ' n n' m m',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  exp_size_contd Ξ c n m -> exp_size_contd Ξ' c n' m' ->
  n <= n' -> m <= m'.
Proof.
  - clear exp_size_conts_le.
    intro c. induction c; intros * Huniq Hle Hsize * Hsize' Hlen; dependent destruction Hsize; dependent destruction Hsize'; try lia.
    + apply exp_size_contd_le with (Ξ := Ξ) (n := n) (m := m) in H0; auto.
    + apply IHc with (Ξ := Ξ) (n := (2 + b) * n) (m := m) in Hsize'; auto.
      apply n_iuv_size_det with (n := b) in H0; auto. subst.
      apply mult_le_compat_r with (p := b0) in Hlen as Hlen'. lia.
    + apply IHc with (Ξ := Ξ) (n := 2 + a * (2 + b) + n) (m := m) in Hsize'; auto.
      apply n_iuv_size_det with (n := a) in H1; auto.
      apply n_iuv_size_det with (n := b) in H2; auto. subst.
      eapply mult_le_compat_r with (p := b0) in Hlen as Hlen'. lia.
    + apply IHc with (Ξ := Ξ) (n := 2 + a + n) (m := m) in Hsize'; auto.
      apply n_iuv_size_det with (n := a) in H0; auto. subst. lia.
  - clear exp_size_contd_le.
    intro c. induction c; intros * Huniq Hle Hsize * Hsize' Hlen; dependent destruction Hsize; dependent destruction Hsize'; try lia.
    + apply IHc with (Ξ := Ξ) (n := 1 + n + a) (m := m) in Hsize'; auto.
      apply n_iuv_size_det with (n := a) in H0; auto. lia.
    + apply exp_size_le with (Ξ := Ξ) (n := n) (m := ne) in H1; auto.
      apply exp_size_conts_le with (Ξ := Ξ) (n := n) (m := ncs) in H2; auto.
      apply mult_le_compat with (p := ne) (q := ne0) in Hlen; auto. lia. 
    + apply IHc with (Ξ := Ξ) (n := 1 + a + n) (m := m) in Hsize'; auto.
      apply n_iuv_size_det with (n := a) in H0; auto. lia.
Qed.

Lemma le_nenv_uniq_l : forall Ξ Ξ',
  le_nenv Ξ Ξ' -> uniq Ξ -> uniq Ξ'.
Proof.
  intros Ξ Ξ' Hle Huniq. induction Hle; eauto; dependent destruction Huniq;
    try solve [erewrite le_nenv_same_dom in H; eauto].
  erewrite le_nenv_same_dom in H0; eauto.
Qed.

Lemma le_nenv_uniq_r : forall Ξ Ξ',
  le_nenv Ξ Ξ' -> uniq Ξ' -> uniq Ξ.
Proof.
  intros Ξ Ξ' Hle Huniq. induction Hle; eauto; dependent destruction Huniq;
    try solve [erewrite <- le_nenv_same_dom in H; eauto].
  erewrite <- le_nenv_same_dom in H0; eauto.
Qed.

Lemma exp_size_split : forall Ξ Ξ1 Ξ2 e n m n1 n2 m1 m2,
  uniq Ξ -> exp_size Ξ e n m -> le_nenv Ξ1 Ξ -> le_nenv Ξ2 Ξ ->
  exp_size Ξ1 e n1 m1 -> exp_size Ξ2 e n2 m2 ->
  1 + n1 + n2 < n -> m1 + m2 < m.
Proof.
  intros Ξ Ξ1 Ξ2 e n m n1 n2 m1 m2 Huniq Hsize.
  generalize dependent m2. generalize dependent m1.
  generalize dependent n2. generalize dependent n1.
  generalize dependent Ξ2. generalize dependent Ξ1.
  dependent induction Hsize; intros * Hle1 Hle2 Hs1 Hs2 Hlt;
    dependent destruction Hs1; dependent destruction Hs2; simpl in *; eauto; try lia.
  - remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
    assert (Hlt': m0 + m1 < m). {
      eapply H0 with (Ξ1 := (x, nbind_var_typ n0) :: Ξ0) (Ξ2 := (x, nbind_var_typ n1) :: Ξ1); eauto.
      eapply le_nenv__var; eauto. lia.
      eapply le_nenv__var; eauto. lia.
    }
    lia.
  - unfold lt in *.
    eapply le_nenv_uniq_r in Hle1 as Huniq1; eauto.
    eapply le_nenv_uniq_r in Hle2 as Huniq2; eauto.
    eapply IHHsize1 with (Ξ1 := Ξ0) (n1 := n0) in Hs2_1; eauto.
    eapply exp_split_size_le with (Ξ' := Ξ) in H1 as Hles1; eauto.
    eapply exp_split_size_le with (Ξ' := Ξ) in H2 as Hles2; eauto.
    assert (s0 * n0 + s1 * n1 + s0 + s1 <= s * n).
    {
      eapply mult_le_compat_r with (p := n0) in Hles1 as Hlesn1.
      eapply mult_le_compat_r with (p := n1) in Hles2 as Hlesn2.
      eapply mult_le_compat_l with (p := s) in Hlt as Hlesn.
      lia.
    }
    eapply IHHsize2 with (Ξ1 := Ξ0) in Hs2_2; eauto; try lia.
    assert (s0 * m4 + s1 * m5 <= s * m2).
    {
      eapply mult_le_compat_r with (p := m4) in Hles1 as Hlesm1.
      eapply mult_le_compat_r with (p := m5) in Hles2 as Hlesm2.
      eapply mult_le_compat_l with (p := s) in Hs2_2 as Hlesm.
      lia.
    }
    lia.
  - eapply le_nenv_uniq_r in Hle1 as Huniq1; eauto.
    eapply le_nenv_uniq_r in Hle2 as Huniq2; eauto.
    remember (dom Ξ). remember (dom Ξ0). remember (dom Ξ1).
    pick fresh X. subst. inst_cofinites_with X.
    eapply n_iuv_size_det in H3; eauto. subst.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_le with (Ξ := (X, nbind_tvar_empty) :: Ξ0) in H0 as Hlem1; eauto.
    eapply exp_size_le with (Ξ := (X, nbind_tvar_empty) :: Ξ1) in H0 as Hlem2; eauto.
    assert (m0 * n0 + m1 * n1 + m0 + m1 <= m * n).
    {
      eapply mult_le_compat_r with (p := n0) in Hlem1 as Hlemn1.
      eapply mult_le_compat_r with (p := n1) in Hlem2 as Hlemn2.
      eapply mult_le_compat_l with (p := m) in Hlt as Hlemn.
      lia.
    }
    lia.
  - unfold lt in *.
    eapply le_nenv_uniq_r in Hle1 as Huniq1; eauto.
    eapply le_nenv_uniq_r in Hle2 as Huniq2; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply n_iuv_size_det in H1; eauto. subst.
    eapply mult_le_compat_l with (p := a0) in Hlt as Hlt'.
    eapply IHHsize with (Ξ1 := Ξ0) in Hs2; eauto; try lia.
    assert (m0 * n0 + m1 * n1 + m0 + m1 <= m * n).
    {
      eapply mult_le_compat with (n := S (m1 + m0)) (m := m) in Hlt; try lia.
    }
    lia.
  - unfold lt in *.
    eapply le_nenv_uniq_r in Hle1 as Huniq1; eauto.
    eapply le_nenv_uniq_r in Hle2 as Huniq2; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply n_iuv_size_det in H1; eauto. subst.
    eapply exp_size_le with (Ξ := Ξ0) in Hsize as Hlem1; eauto.
    eapply exp_size_le with (Ξ := Ξ1) in Hsize as Hlem2; eauto.
    assert (m0 * n0 + m1 * n1 + m0 + m1 <= m * n).
    {
      eapply mult_le_compat_r with (p := n0) in Hlem1 as Hlemn1.
      eapply mult_le_compat_r with (p := n1) in Hlem2 as Hlemn2.
      eapply mult_le_compat_l with (p := m) in Hlt as Hlemn.
      lia.
    }
    lia.
Qed.

Lemma apply_contd_exp_size : forall Ξ c A B w a b n m,
  uniq Ξ -> apply_contd c A B w ->
  n_iuv_size A a -> n_iuv_size B b ->
  exp_size_contd Ξ c (a + b) n -> exp_size_work Ξ w m -> m <= n.
Proof.
  intros Ξ c A B w a b n m Huniq Happly Ha Hb Hsize1 Hsize2.
  induction Happly; dependent destruction Hsize1; dependent destruction Hsize2; eauto.
  - eapply n_iuv_size_det in Ha; eauto. subst.
    eapply n_iuv_size_det in Hb; eauto. subst.
    eapply exp_size_conts_det with (m' := n) in H0; eauto.
    eapply exp_size_det in H; eauto. subst. lia.
  - eapply n_iuv_size_det in Ha; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_contd_le; eauto. lia.
  - eapply n_iuv_size_det in Ha; eauto.
    eapply n_iuv_size_det in H; eauto. subst.
    eapply exp_size_contd_le; eauto. lia.
Qed.

Lemma awl_to_nenv_binds : forall Γ Ξ x A n,
  uniq Ξ -> awl_to_nenv Γ Ξ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ -> binds x (nbind_var_typ n) Ξ ->
  n_iuv_size A n.
Proof.
  intros Γ Ξ x A n Huniq Hnenv Hbinds Hbinds'.
  dependent induction Hnenv; eauto.
  - exfalso. eauto.
  - dependent destruction Huniq.
    destruct_binds; eauto.
    + dependent destruction H0; eauto.
    + exfalso. erewrite awl_to_nenv_same_dom in H; eauto.
    + exfalso. eauto.
Qed.

Lemma a_wf_wl_uniq : forall Γ,
  a_wf_wl Γ ->
  uniq (⌊ Γ ⌋ᵃ).
Proof.
  intros. induction H; simpl; auto.
Qed.

Fixpoint rename_var_in_aworklist (y x:expvar) (Γ:aworklist) {struct Γ} : aworklist :=
  match Γ with
    | aworklist_empty => aworklist_empty
    | (aworklist_cons_var Γ' x' b) => 
      match b with 
        | abind_var_typ _ => aworklist_cons_var (rename_var_in_aworklist y x Γ') (if x' == x then y else x') b
        | _ => aworklist_cons_var (rename_var_in_aworklist y x Γ') x' b
      end
    | (aworklist_cons_work Γ' w) => aworklist_cons_work (rename_var_in_aworklist y x Γ') (subst_exp_in_work (exp_var_f y) x w)
  end.

Lemma exp_split_size_weaken : forall Ξ1 Ξ2 Ξ3 e n,
  exp_split_size (Ξ3 ++ Ξ1) e n ->
  exp_split_size (Ξ3 ++ Ξ2 ++ Ξ1) e n.
Proof.
  intros Ξ1 Ξ2 Ξ3 e n Hsize.
  generalize dependent Ξ2.
  dependent induction Hsize; intros *; eauto.
  - inst_cofinites_for exp_split_size__abs n:=n; try lia.
    intros * Hnotin.
    rewrite_env ((x ~ nbind_var_typ 0 ++ Ξ3) ++ Ξ2 ++ Ξ1).
    eapply H0; eauto. 
  - inst_cofinites_for exp_split_size__tabs n:=n,m:=m; try lia; eauto.
    intros * Hnotin.
    rewrite_env ((X ~ nbind_tvar_empty ++ Ξ3) ++ Ξ2 ++ Ξ1).
    eapply H0; eauto.
Qed.

Lemma exp_size_weaken : forall Ξ1 Ξ2 Ξ3 e n m,
  exp_size (Ξ3 ++ Ξ1) e n m ->
  exp_size (Ξ3 ++ Ξ2 ++ Ξ1) e n m.
Proof.
  intros Ξ1 Ξ2 Ξ3 e n m Hsize.
  generalize dependent Ξ2.
  dependent induction Hsize; intros *; eauto.
  - inst_cofinites_for exp_size__abs m:=m; try lia.
    intros * Hnotin.
    rewrite_env ((x ~ nbind_var_typ n ++ Ξ3) ++ Ξ2 ++ Ξ1).
    eapply H0; eauto.
  - eapply exp_split_size_weaken in H; eauto.
  - inst_cofinites_for exp_size__tabs a:=a,n:=n,m:=m; try lia; eauto.
    intros * Hnotin.
    rewrite_env ((X ~ nbind_tvar_empty ++ Ξ3) ++ Ξ2 ++ Ξ1).
    eapply H1; eauto.
Qed.

Lemma exp_size_conts_weaken : forall c Ξ1 Ξ2 Ξ3 n m,
  exp_size_conts (Ξ3 ++ Ξ1) c n m ->
  exp_size_conts (Ξ3 ++ Ξ2 ++ Ξ1) c n m
with exp_size_contd_weaken : forall c Ξ1 Ξ2 Ξ3 n m,
  exp_size_contd (Ξ3 ++ Ξ1) c n m ->
  exp_size_contd (Ξ3 ++ Ξ2 ++ Ξ1) c n m.
Proof.
  - clear exp_size_conts_weaken. intro c. induction c; intros * Hsize; dependent destruction Hsize; eauto.
  - clear exp_size_contd_weaken. intro c. induction c; intros * Hsize; dependent destruction Hsize; eauto.
    eapply exp_size_weaken in H; eauto.
Qed.

(* Lemma n_iuv_size_open_typ_wrt_typ_rec : forall A B n m1 m2 m3,
  n_iuv_size (open_typ_wrt_typ_rec n B A) m1 ->
  n_iuv_size A m2 ->
  n_iuv_size B m3 ->
  m1 <= m2 * (1 + m3).
Proof.
  intros * Hopen Ha Hb. generalize dependent n. generalize dependent m1. generalize dependent m2. generalize dependent m3.
  induction A; intros; simpl in *; eauto; 
    try (dependent destruction Ha; dependent destruction Hb; dependent destruction Hopen; eauto; lia).
  - dependent destruction Hopen.
    dependent destruction Ha. 
    specialize (IHA1 _ Hb _ Ha1 _ n Hopen1).
    specialize (IHA2 _ Hb _ Ha2 _ n Hopen2). lia. 
  - dependent destruction Hopen.
    dependent destruction Ha. 
    pick fresh X. inst_cofinites_with X.
    specialize (IHA _ Hb _ H).
  admit.
  - dependent destruction Hopen.
    dependent destruction Ha. 
    specialize (IHA1 _ Hb _ Ha1 _ n Hopen1).
    specialize (IHA2 _ Hb _ Ha2 _ n Hopen2). lia. 
  - dependent destruction Hopen.
    dependent destruction Ha. 
    specialize (IHA1 _ Hb _ Ha1 _ n Hopen1).
    specialize (IHA2 _ Hb _ Ha2 _ n Hopen2). lia. 
Admitted. *)

Lemma num_occurs_in_typ_fresh : forall A X n,
  X `notin` ftvar_in_typ A -> num_occurs_in_typ X A n -> n = 0.
Proof.
  intros A X n Hnotin Hocc.
  induction Hocc; simpl in *; eauto;
    try solve [exfalso; eauto];
    try solve [rewrite IHHocc1; eauto].
  pick fresh Y. inst_cofinites_with Y.
  eapply H0. rewrite ftvar_in_typ_open_typ_wrt_typ_upper; eauto.
Qed.

Lemma num_occurs_in_typ_subst : forall A B X Y n m,
  X `notin` ftvar_in_typ B -> lc_typ B ->
  num_occurs_in_typ X (subst_typ_in_typ B Y A) n ->
  num_occurs_in_typ X A m -> n <= m.
Proof.
  intros A B X Y n m Hfv Hlcb Hocc1 Hocc2.
  generalize dependent B. generalize dependent Y.
  generalize dependent n.
  induction Hocc2; intros; simpl in *; eauto;
    try solve [dependent destruction Hocc1; eauto; lia].
  - destruct_eq_atom.
    erewrite num_occurs_in_typ_fresh with (n := n); eauto.
    dependent destruction Hocc1; auto.
  - destruct_eq_atom.
    + erewrite num_occurs_in_typ_fresh with (n := n); eauto.
    + dependent destruction Hocc1; eauto.
      exfalso. eauto.
  - dependent destruction Hocc1.
    eapply IHHocc2_1 in Hocc1_1; eauto.
    eapply IHHocc2_2 in Hocc1_2; eauto. lia.
  - dependent destruction Hocc1.
    pick fresh Y0. inst_cofinites_with Y0.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H1; eauto.
  - dependent destruction Hocc1.
    eapply IHHocc2_1 in Hocc1_1; eauto.
    eapply IHHocc2_2 in Hocc1_2; eauto. lia.
  - dependent destruction Hocc1.
    eapply IHHocc2_1 in Hocc1_1; eauto.
    eapply IHHocc2_2 in Hocc1_2; eauto. lia.
Qed.

Lemma iuv_size_open_typ_wrt_typ : forall A X B n m1 m2 m3,
  lc_typ A ->
  lc_typ B ->
  X `notin` ftvar_in_typ B -> 
  num_occurs_in_typ X A n ->
  n_iuv_size (subst_typ_in_typ B X A) m1 ->
  n_iuv_size A m2 ->
  n_iuv_size B m3 ->
  m1 <= (n + m2) * (1 + m3).
Proof.
  intros * Hlca Hlcb Hfv Hocc Hopen Ha Hb.
  generalize dependent n. generalize dependent m1. generalize dependent m2. generalize dependent m3.  
  induction Hlca; intros; simpl in *;
     try solve [dependent destruction Ha; dependent destruction Hb; dependent destruction Hopen; simpl in *; try lia].
  - destruct_eq_atom.
    + eapply n_iuv_size_det with (n := m3) in Hopen; eauto. subst.
      dependent destruction Hocc. lia.
      solve_false.
    + dependent destruction Hopen. lia.
  - dependent destruction Ha.
    dependent destruction Hopen.
    dependent destruction Hocc.
    specialize (IHHlca1 _ Hb _ Ha1 _ Hopen1 _ Hocc1).
    specialize (IHHlca2 _ Hb _ Ha2 _ Hopen2 _ Hocc2).
    lia.
  - dependent destruction Ha.
    dependent destruction Hopen.
    dependent destruction Hocc.
    pick fresh X0. inst_cofinites_with X0.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H3; eauto.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H4; eauto.
    specialize (H0 X0 _ Hb _ H1 _ H3 _ H5). 
    eapply num_occurs_in_typ_subst with (B := B) in H2; eauto.
    lia.
  - dependent destruction Ha.
    dependent destruction Hopen.
    dependent destruction Hocc.
    specialize (IHHlca1 _ Hb _ Ha1 _ Hopen1 _ Hocc1).
    specialize (IHHlca2 _ Hb _ Ha2 _ Hopen2 _ Hocc2).
    lia.
- dependent destruction Ha.
    dependent destruction Hopen.
    dependent destruction Hocc.
    specialize (IHHlca1 _ Hb _ Ha1 _ Hopen1 _ Hocc1).
    specialize (IHHlca2 _ Hb _ Ha2 _ Hopen2 _ Hocc2).
    lia.
Qed.

Lemma n_iuv_size_open : forall A B n a b,
  lc_typ (typ_all A) -> lc_typ B ->
  n_iuv_size (typ_all A) a -> n_iuv_size B b ->
  n_iuv_size (A ᵗ^^ₜ B) n -> n <= a + a * b.
Proof.
  intros * Hlca Hlcb Ha Hb Hn.
  intros. dependent destruction Ha; eauto.
  dependent destruction Hlca.
  pick fresh X. inst_cofinites_with X. specialize (H X).
  erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 in Hn; eauto.
  assert (Hnotin: X `notin` ftvar_in_typ B) by auto.
  specialize (iuv_size_open_typ_wrt_typ (A ᵗ^ₜ X) X B _ _ _ _ H Hlcb Hnotin H1 Hn H0 Hb).
  lia.
Qed.

Lemma a_wf_wl_red_decidable : forall me mj mt mtj ma maj ms mw ne Γ,
  ⊢ᵃʷₛ Γ ->
  exp_size_wl Γ ne -> ne < me ->
  judge_size_wl Γ < mj ->
  inftapp_depth_wl Γ < mt ->
  inftapp_judge_size_wl Γ < mtj ->
  infabs_depth_wl Γ < ma ->
  infabs_judge_size_wl Γ < maj ->
  split_depth_wl Γ < ms ->
  weight_wl Γ < mw ->
  Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅.
Proof.
  intros me; induction me;
  intros mj; induction mj;
  intros mt; induction mt;
  intros mtj; induction mtj;
  intros ma; induction ma;
  intros maj; induction maj;
  intros ms; induction ms;
  intros mw; induction mw; try lia.
  intros ne Γ Hwf He Helt Hj Ht Htj Ha Haj Hm Hw.
  eapply a_wf_wl_uniq in Hwf as Huniq.
  dependent destruction Hwf; auto.
  - rename H into Hwf. dependent destruction Hwf; auto.
    + simpl in *. dependent destruction He.
      assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
      { eapply IHmw with (ne := n); eauto. lia. }
      destruct Jg as [Jg | Jg]; auto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + simpl in *. dependent destruction He.
      assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
      { eapply IHmw; eauto. lia. }
      destruct Jg as [Jg | Jg]; auto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + simpl in *. dependent destruction He.
      assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
      { eapply IHmw; eauto. lia. }
      destruct Jg as [Jg | Jg]; auto.
      right. intro Hcontra.
      dependent destruction Hcontra.
      apply Jg; auto.
    + dependent destruction He.
      dependent destruction H.
      * dependent destruction H3.
        dependent destruction H; simpl in *.
        -- dependent destruction H3. dependent destruction H4.
           assert (Jg: (work_applys cs typ_unit ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_applys cs typ_unit ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHme with (ne := m + n); eauto; simpl; try lia. }
           destruct Jg as [Jg | Jg]; auto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- dependent destruction H3. dependent destruction H4.
           assert (Jg: (work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHme; eauto; simpl; try lia.
             eapply a_wf_wl_a_wf_bind_typ in H; eauto.
             eapply exp_size_wl__cons_work; eauto.
             eapply exp_size_work__applys; eauto.
             eapply awl_to_nenv_binds with (Ξ := Ξ); eauto.
             eapply awl_to_nenv_uniq; eauto. lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply binds_unique with (b:= (abind_var_typ A0)) in H; auto. dependent destruction H.
           subst. apply Jg; auto.
        -- dependent destruction H4. dependent destruction H5.
           pick fresh x. inst_cofinites_with x.
           pick fresh X1. pick fresh X2.
           assert (Jg: (work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1 ;ᵃ work_applys cs (typ_arrow ` X1 ` X2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1 ;ᵃ work_applys cs (typ_arrow ` X1 ` X2) ⫤ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (Huniq': uniq Ξ).
             { eapply awl_to_nenv_uniq; eauto. } 
             assert (He': exists m, exp_size_conts Ξ cs 0 m).
             {
              eapply exp_size_conts_total; eauto.
              eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
              eapply a_wf_twl_a_wf_wwl; eauto.
             }
             destruct He' as [m' He'].
             eapply exp_size_conts_le with (Ξ := Ξ) (m := m') in H6; eauto; try lia.
             eapply IHme with (ne := m0 + (m' + n)); auto.
             ++ repeat (constructor; simpl; auto).
                eapply a_wf_exp_weaken_etvar_twice. simpl. eauto.
                apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.
             ++ eapply exp_size_wl__cons_work with (m := m0) (n := m' + n)
                (Ξ := ((x, nbind_var_typ 0) :: (X2, nbind_etvar_empty) :: (X1, nbind_etvar_empty) :: Ξ)); eauto.
                eapply awl_to_nenv__cons_var; eauto.
                eapply exp_size_work__check; eauto.
                rewrite_env (((x, nbind_var_typ 0) :: nil) ++ ((X2, nbind_etvar_empty) :: (X1, nbind_etvar_empty) :: nil) ++ Ξ).
                eapply exp_size_weaken; eauto.
                constructor...
                eapply exp_size_wl__cons_work with (m := m')
                    (Ξ := ((X2, nbind_etvar_empty) :: (X1, nbind_etvar_empty) :: Ξ)); eauto.
                eapply exp_size_work__applys with (n := 0); eauto.
                rewrite_env (nil ++ ((X2, nbind_etvar_empty) :: (X1, nbind_etvar_empty) :: nil) ++ Ξ).
                eapply exp_size_conts_weaken. simpl. eauto.
             ++ lia. }
            admit. (* renaming *)
        -- dependent destruction H4. dependent destruction H5.
           assert (Jg: (work_infer e1 (conts_infabs (contd_infapp e2 cs)) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infer e1 (conts_infabs (contd_infapp e2 cs)) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (Huniq': uniq Ξ).
             { eapply awl_to_nenv_uniq; eauto. } 
             eapply exp_split_size_det with (n := s0) in H5_; eauto. subst.
             assert (He': exists m, exp_size_conts Ξ cs n1 m).
             {
               eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto.
             }
             destruct He' as [m' He'].
             eapply exp_size_conts_le with (Ξ := Ξ) (m := m') in H6; eauto; try lia.
             simpl in *. eapply IHme; eauto; simpl; try lia. constructor; auto.
             rewrite mult_0_r in H4_0. rewrite plus_0_r in H4_0. simpl in H4_0.
             eapply exp_size_wl__cons_work with (Ξ := Ξ) (n := n); eauto.
             lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra. eauto.
        -- dependent destruction H4. dependent destruction H6.
           assert (lc_typ (typ_all A)). {  
            pick fresh X. inst_cofinites_with X. 
            dependent destruction H0. eapply lc_typ_all_exists; eauto. 
           }
           apply n_iuv_size_total in H9 as Hiuv.
           destruct Hiuv as [a' Hiuv].
           pick fresh X. inst_cofinites_with X (keep).
           assert (Jg: (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (Huniq': uniq Ξ).
             { eapply awl_to_nenv_uniq; eauto. } 
             assert (He': exists m, exp_size_conts Ξ cs a' m).
             {
               eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto.
             }
             destruct He' as [m' He'].
             assert (m' <= m) by admit.
             eapply IHme; eauto; simpl; try lia.
             ++ dependent destruction H4. repeat (constructor; simpl; auto).
                 inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
                 dependent destruction H12; auto.
             ++ eapply exp_size_wl__cons_work; eauto.
                 eapply awl_to_nenv__cons_var; eauto. 
             ++ lia. 
           }
           admit. (* renaming *)
        -- dependent destruction H4. dependent destruction H6.
           assert (Jg: (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHme; eauto; simpl; try lia.
             eapply exp_size_wl__cons_work; eauto.
             eapply exp_size_work__infer; eauto.
             admit. admit. (* exp_size_tail_rec_le *) }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- dependent destruction H4. dependent destruction H6.
           eapply n_iuv_size_det with (n := a) in H7; eauto. subst.
           assert (Huniq' : uniq Ξ).
           { eapply awl_to_nenv_uniq; eauto. }
           assert (He': exists m, exp_size_conts Ξ cs m1 m).
           { eapply exp_size_conts_total; eauto.
             eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
             eapply a_wf_twl_a_wf_wwl; eauto. }
           destruct He' as [m' He'].
           eapply exp_size_conts_le with (m' := m) in He' as Hle; eauto; try lia.
           assert (Jg: (work_check e A ⫤ᵃ work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check e A ⫤ᵃ work_applys cs A ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHme; eauto; simpl; try lia. constructor; auto.
             eapply exp_size_wl__cons_work with (m := m0) (n := m' + n); eauto. lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
      * dependent destruction H3. simpl in *.
        assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        assert (Jg: (work_infer e (conts_sub A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                  ~ (work_infer e (conts_sub A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { assert (Hes: exists s, exp_split_size Ξ e s).
          { eapply exp_split_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct Hes as [s Hes].
          assert (He': exists m, exp_size Ξ e 0 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He' as [m' He'].
          eapply exp_size_le with (m' := m) in He' as Hle; eauto; try lia.
          eapply IHmj; eauto; simpl; try lia. }
        assert (Jg1: forall A1 A2, A = typ_union A1 A2 ->
                       (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { intros A1 A2 Heq. subst.
          dependent destruction H0. dependent destruction H3.
          assert (He1: exists m, exp_size Ξ e n1 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He1 as [m1 He1].
          assert (He2: exists m, exp_size Ξ e n2 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He2 as [m2 He2].
          eapply exp_size_split with (n := 2 + n1 + n2) in He1 as Hle'; eauto; try lia.
          eapply IHme; eauto; simpl; try lia. }
        assert (Jg2: forall A1 A2, A = typ_union A1 A2 ->
                       (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { intros A1 A2 Heq. subst.
          dependent destruction H0. dependent destruction H3.
          assert (He1: exists m, exp_size Ξ e n1 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He1 as [m1 He1].
          assert (He2: exists m, exp_size Ξ e n2 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He2 as [m2 He2].
          eapply exp_size_split with (n := 2 + n1 + n2) in He1 as Hle'; eauto; try lia.
          eapply IHme; eauto; simpl; try lia. }
        assert (Jg': forall A1 A2, A = typ_intersection A1 A2 ->
                       (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ ).
        { intros A1 A2 Heq. subst.
          dependent destruction H0. dependent destruction H3.
          assert (He1: exists m, exp_size Ξ e n1 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He1 as [m1 He1].
          assert (He2: exists m, exp_size Ξ e n2 m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He2 as [m2 He2].
          eapply exp_size_split with (n := 2 + n1 + n2) in He1 as Hle'; eauto; try lia.
          eapply IHme; eauto; simpl; try lia. constructor; auto.
          eapply exp_size_wl__cons_work; eauto. lia. }
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
        -- dependent destruction H5. dependent destruction H1; simpl in *;
             try solve [right; intro Hcontra; dependent destruction Hcontra; eapply Jg; eauto].
           ++ remember (dom Ξ). pick fresh x. subst.
              assert (Jgt: (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                         ~ (work_check (e ᵉ^^ₑ exp_var_f x) typ_top ⫤ᵃ x ~ᵃ typ_bot;ᵃ Γ) ⟶ᵃʷ⁎⋅).
              { inst_cofinites_with x.
                assert (He': exists m, exp_size ((x, nbind_var_typ 0) :: Ξ) (e ᵉ^^ₑ exp_var_f x) 0 m).
                { eapply exp_size_total; eauto.
                  eapply a_wf_exp_n_wf_exp with (Γ := aworklist_cons_var Γ x (abind_var_typ typ_top)); eauto.
                  eapply a_wf_twl_a_wf_wwl; eauto.
                  simpl. eapply a_wf_exp_var_binds_another with (Σ2 := nil); simpl; eauto. }
                destruct He' as [m' He'].
                eapply exp_size_le with (Ξ' := (x, nbind_var_typ n0) :: Ξ) (m' := m) in He' as Hle; eauto; try lia.
                eapply IHme; eauto; simpl; try lia.
                constructor; auto. constructor; auto. constructor; auto.
                apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
                eapply exp_size_wl__cons_work with (Ξ := ((x, nbind_var_typ 0) :: Ξ)); eauto. lia.
                eapply le_nenv__var; eauto. lia. }
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
           ++ admit. (* TODO: split *)
           ++ remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
              dependent destruction H4.
              assert (JgArr: (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                           ~ (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅).
              { assert (He': exists m, exp_size ((x, nbind_var_typ n1) :: Ξ) (e ᵉ^^ₑ exp_var_f x) n2 m).
                { eapply exp_size_total; eauto.
                  eapply a_wf_exp_n_wf_exp with (Γ := aworklist_cons_var Γ x (abind_var_typ A1)); eauto.
                  eapply a_wf_twl_a_wf_wwl; eauto.
                  simpl. eapply a_wf_exp_var_binds_another with (Σ2 := nil); simpl; eauto. }
                destruct He' as [m' He'].
                eapply exp_size_le with (Ξ' := (x, nbind_var_typ (n1 + n2)) :: Ξ) (m' := m) in He' as Hle; eauto; try lia.
                eapply IHme; eauto; simpl; try lia.
                constructor; auto. constructor; auto. constructor; auto.
                apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
                simpl. eapply a_wf_typ_weaken_cons; eauto.
                eapply exp_size_wl__cons_work with (Ξ := ((x, nbind_var_typ n1) :: Ξ)); eauto.
                lia.
                eapply le_nenv__var; eauto. lia. }
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
                     erewrite subst_exp_in_exp_intro with (x1:=x); eauto.
                     apply a_wf_exp_rename_var_cons; eauto.
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
      * dependent destruction H3. simpl in *.
        assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. } 
        dependent destruction H;
          try solve [right; intro Hcontra; dependent destruction Hcontra].
        -- assert (Jg:   (work_infabs (typ_arrow typ_top typ_bot) cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                       ~ (work_infabs (typ_arrow typ_top typ_bot) cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHma; eauto; simpl in *; try lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- right. intro Hcontra.
           dependent destruction Hcontra. unify_binds.
        -- right. intro Hcontra.
           dependent destruction Hcontra. unify_binds.
        -- admit. (* TODO: split *)
        -- destruct (apply_contd_dec cd A1 A2) as [[w Happly] | Happly];
            try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
                      eapply Happly; eauto].
          assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
          { eapply a_wf_wl_apply_contd in Happly as Hwf'; eauto.
            eapply a_wf_work_apply_contd in Happly as Hwf''; eauto.
            assert (He': exists m, exp_size_work Ξ w m).
            { eapply exp_size_work_total; eauto.
              eapply a_wf_work_n_wf_work with (Γ := Γ); eauto.
              eapply a_wf_wl_a_wf_wwl; eauto. }
            destruct He' as [m' He'].
            dependent destruction H4.
            assert (He'': exists m, exp_size_contd Ξ cd (n1 + n2) m).
            { eapply exp_size_contd_total; eauto.
              eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto.
              eapply a_wf_twl_a_wf_wwl; eauto. }
            destruct He'' as [m'' He''].
            eapply exp_size_contd_le with (m := m'') in H5 as Hle; eauto; try lia.
            eapply apply_contd_exp_size with (n := m'') in Happly as ?; eauto. subst.
            eapply IHmaj; eauto; simpl in *; try lia.
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
        -- dependent destruction H4.
           remember (dom Ξ). pick fresh X. subst. inst_cofinites_with X.
           assert (Jg: (work_infabs (A ᵗ^ₜ X) cd ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infabs (A ᵗ^ₜ X) cd ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (Heq: infabs_depth (open_typ_wrt_typ A (typ_var_f X)) = infabs_depth A) by admit. (* should be fine *)
             assert (He': exists m, exp_size_contd Ξ cd n0 m).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m' He'].
             eapply exp_size_contd_le with (m := m') in H6; eauto; try lia.
             eapply exp_size_contd_weaken with (Ξ3 := nil) (Ξ2 := (X, nbind_etvar_empty) :: nil) in He'.
             eapply IHma with (ne := m' + n); eauto; simpl in *; try lia.
             constructor; simpl; auto. constructor; simpl; auto. constructor; simpl; auto.
             eapply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
             eapply a_wf_contd_weaken_cons; auto.
             eapply exp_size_wl__cons_work with (Ξ := ((X, nbind_etvar_empty) :: Ξ)); eauto. }
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
             apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H7; auto.
             ** simpl in H7. destruct_eq_atom.
                rewrite rename_tvar_in_aworklist_fresh_eq in H7; auto.
                rewrite subst_typ_in_contd_fresh_eq in H7; auto.
                rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H7; auto.
             ** eapply a_wf_wl_a_wf_wwl.
                constructor; auto. constructor; auto. constructor; simpl; auto.
                admit. admit. (* wf *)
        -- assert (Jg: (work_infabs A1 (contd_infabsunion A2 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infabs A1 (contd_infabsunion A2 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { dependent destruction H4.
             assert (He': exists m, exp_size_contd Ξ cd (1 + n1 + n2) m).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m' He'].
             eapply exp_size_contd_le with (m := m') in H5; eauto; try lia.
             eapply IHma; eauto; simpl in *; try lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- assert (Jg1: (work_infabs A1 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                      ~ (work_infabs A1 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { dependent destruction H4.
             assert (He': exists m, exp_size_contd Ξ cd n1 m).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m' He'].
             eapply exp_size_contd_le with (m := m') in H5; eauto; try lia.
             eapply IHma; eauto; simpl in *; try lia. }
           assert (Jg2: (work_infabs A2 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                      ~ (work_infabs A2 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { dependent destruction H4.
             assert (He': exists m, exp_size_contd Ξ cd n2 m).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m' He'].
             eapply exp_size_contd_le with (m := m') in H5; eauto; try lia.
             eapply IHma; eauto; simpl in *; try lia. } 
           destruct Jg1 as [Jg1 | Jg1]; eauto.
           destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg1; auto. apply Jg2; auto.
      * dependent destruction H4. simpl in *. dependent destruction H;
        try solve [right; intro Hcontra; dependent destruction Hcontra].
        assert (Jg:  (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                   ~ (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHmaj; eauto; simpl in *; try lia. constructor; auto. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra. 
        dependent destruction Hcontra. eauto.
      * dependent destruction H4. simpl in *.
        assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H; try solve [right; intro Hcontra; dependent destruction Hcontra].
        assert (Jg:  (work_check e A ⫤ᵃ work_applys cs B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                  ~ (work_check e A ⫤ᵃ work_applys cs B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { assert (He': exists m, exp_size Ξ e a m).
          { eapply exp_size_total; eauto.
            eapply a_wf_exp_n_wf_exp with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He' as [m' He'].
          assert (He'': exists m, exp_size_conts Ξ cs b m).
          { eapply exp_size_conts_total; eauto.
            eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He'' as [m'' He''].
          eapply exp_size_le with (m := m') in H7; eauto; try lia.
          eapply exp_size_conts_le with (m := m'') in H8; eauto; try lia.
          eapply IHmj with (ne := m' + (m'' + n)); eauto; simpl in *; try lia. constructor; auto.
          eapply exp_size_wl__cons_work; eauto. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra.
        dependent destruction Hcontra. eauto.
      * dependent destruction H4. simpl in *.
        assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H;
          try solve [right; intro Hcontra; dependent destruction Hcontra].
        -- destruct (apply_conts_dec cs typ_bot) as [[w Happly] | Happly];
           try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
             eapply Happly; eauto].
           assert (Jg: a_wl_red (aworklist_cons_work Γ w) \/
                     ~ a_wl_red (aworklist_cons_work Γ w)).
           { eapply a_wf_work_apply_conts in Happly as Hwf'; eauto.
             assert (He': exists m, exp_size_work Ξ w m).
             { eapply exp_size_work_total; eauto.
               eapply a_wf_work_n_wf_work with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m' He'].
             assert (He'': exists m, exp_size_conts Ξ cs n1 m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He'' as [m'' He''].
             eapply exp_size_conts_le with (m := m'') in H6; eauto; try lia.
             eapply apply_conts_exp_size with (n := m'') in Happly as Hle; eauto. subst.
             eapply IHmtj; eauto; simpl in *; try lia.
             eapply a_wf_wl_apply_conts; eauto.
             eapply apply_conts_judge_size in Happly; lia.
             replace (inftapp_depth A2 * 0) with 0 in Ht by lia.
             eapply apply_conts_inftapp_depth_bot in Happly; lia.
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
           { eapply a_wf_work_apply_conts in Happly as Hwf'; eauto.
             2: { eapply a_wf_typ_all_open; eauto. }
             assert (He': exists m, exp_size_work Ξ w m).
             { eapply exp_size_work_total; eauto.
               eapply a_wf_work_n_wf_work with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m' He'].
             assert (He'': exists n, n_iuv_size (A ᵗ^^ₜ A2) n).
             { eapply n_iuv_size_total; eauto.
               eapply a_wf_typ_lc; eauto.
               eapply a_wf_typ_all_open; eauto. }
             destruct He'' as [n' He''].
             assert (He''': exists m, exp_size_conts Ξ cs n' m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He''' as [m'' He'''].
             assert (Hle: n' <= n1 + n1 * n2).
             { eapply n_iuv_size_open with (A := A) (B := A2); eauto. }
             eapply exp_size_conts_le with (m := m'') in H7; eauto; try lia.
             eapply apply_conts_exp_size in Happly as Hwf''; eauto. subst.
             eapply IHmtj; eauto; simpl in *; try lia.
             eapply a_wf_wl_apply_conts; eauto.
             constructor; auto. constructor; auto.
             eapply a_wf_typ_all_open; eauto.
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
        -- dependent destruction H5.
           assert (Jg: (work_inftapp A1 A2 (conts_inftappunion A0 A2 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_inftapp A1 A2 (conts_inftappunion A0 A2 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           {
            (* eapply IHmt. admit.
            eapply exp_size_wl__cons_work. admit.
            eapply exp_size_work__inftapp. admit. admit.
            eapply exp_size_conts__inftappunion. admit. admit. *)

            assert (He': exists m, exp_size_conts Ξ cs (2 + n3 * (2 + n2) + (2 + n2) * n1) m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m He'].
             eapply exp_size_conts_le with (m := m) in H7; eauto; try lia.
             eapply IHmt; eauto; simpl in *; try lia.
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
        -- dependent destruction H5.
           assert (Jg1: (work_inftapp A1 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_inftapp A1 A2 cs ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { 
            (* eapply IHmt. admit.
            eapply exp_size_wl__cons_work. admit.
            eapply exp_size_work__inftapp. admit. admit. *)
             assert (He': exists m, exp_size_conts Ξ cs ((2 + n2) * n1) m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m He'].
             eapply exp_size_conts_le with (m := m) in H7; eauto; try lia.
             eapply IHmt; eauto; simpl in *; try lia.
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
           { assert (He': exists m, exp_size_conts Ξ cs ((2 + n2) * n3) m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
               eapply a_wf_twl_a_wf_wwl; eauto. }
             destruct He' as [m He'].
             eapply exp_size_conts_le with (m := m) in H7; eauto; try lia.
             eapply IHmt; eauto; simpl in *; try lia.
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
      * assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H5. simpl in *.
        assert (Jg:  (work_inftapp A2 B (conts_unioninftapp A1 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                   ~ (work_inftapp A2 B (conts_unioninftapp A1 cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { 
          (* eapply IHmt. admit.
            eapply exp_size_wl__cons_work. admit.
            eapply exp_size_work__inftapp. admit. admit.
            eapply exp_size_conts__unioninftapp. admit. *)
          assert (He': exists m, exp_size_conts Ξ cs (2 + n1 + (2 + n0) * n2) m).
          { eapply exp_size_conts_total; eauto.
            eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He' as [m' He'].
          eapply exp_size_conts_le with (m := m') in H8; eauto; try lia.
          eapply IHmtj; eauto; simpl; try lia.
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
      * assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H4. simpl in *.
        destruct (apply_conts_dec cs (typ_union A1 A2)) as [[w Happly] | Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply a_wf_work_apply_conts in Happly as Hwf'; eauto.
          assert (He': exists n, exp_size_work Ξ w n).
          { eapply exp_size_work_total; eauto.
            eapply a_wf_work_n_wf_work with (Γ := Γ); eauto.
            eapply a_wf_twl_a_wf_wwl; eauto. }
          destruct He' as [n' He'].
          eapply apply_conts_exp_size with (n := m) in Happly as Hle; eauto. subst.
          eapply IHmtj; eauto; simpl in *; try lia.
          eapply a_wf_wl_apply_conts; eauto.
          (* eapply apply_conts_exp_size with (n := n0) in Happly; eauto; lia. *)
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
      * dependent destruction H4. simpl in *. dependent destruction H;
          try solve [right; intro Hcontra; dependent destruction Hcontra];
        dependent destruction H1;
          try solve [right; intro Hcontra; dependent destruction Hcontra].
        destruct (apply_contd_dec cd ( (typ_intersection A1 A2) )   ( (typ_union B1 B2) ) ) as [[w Happly] | Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply a_wf_wl_apply_contd with (Γ := Γ) in Happly as Hwf'; eauto.
          2: { constructor; auto. }
          eapply a_wf_work_apply_contd in Happly as Hwf''; eauto.
          destruct exp_size_work_total with (Γ := Γ) (w := w) as [n' He'] in Hwf''; eauto.
          eapply IHmaj; eauto; simpl in *; try lia.
          eapply apply_contd_exp_size with (n := n') in Happly; eauto; lia.
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
      * dependent destruction H3. simpl in *.
        edestruct (apply_conts_dec cs A) as [[w Happly] | Happly].
        -- eapply a_wf_wl_apply_conts in Happly as Hwf'; eauto.
           eapply a_wf_work_apply_conts in Happly as Hwf''; eauto.
           edestruct exp_size_work_total as [n' He'] in Hwf''; eauto.
           assert (JgApply: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHmj; eauto; simpl in *; try lia.
             eapply apply_conts_exp_size with (n := n0) in Happly; eauto; lia.
             eapply apply_conts_judge_size in Happly; lia. }
           destruct JgApply as [JgApply | JgApply]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply apply_conts_det in Happly; eauto. subst. eapply JgApply; eauto.
        -- right; intro Hcontra; dependent destruction Hcontra;
           eapply Happly; eauto.
      * dependent destruction H4. simpl in *.
        simpl in *. edestruct (apply_contd_dec cd A B) as [[w Happly] | Happly].
        -- eapply a_wf_wl_apply_contd with (Γ := Γ) in Happly as Hwf'; eauto.
           eapply a_wf_work_apply_contd in Happly as Hwf''; eauto.
           edestruct exp_size_work_total as [n' He'] in Hwf''; eauto.
           assert (JgApply: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply IHmj; eauto; simpl in *; try lia.
             eapply apply_contd_exp_size with (n := n') in Happly; eauto; lia.
             eapply apply_contd_judge_size in Happly; lia. }
           destruct JgApply as [JgApply | JgApply]; eauto.
           right. intro Hcontra. dependent destruction Hcontra.
           eapply apply_contd_det in Happly; eauto. subst. eapply JgApply; eauto.
        -- right; intro Hcontra; dependent destruction Hcontra;
           eapply Happly; eauto.
  - dependent destruction He. simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHmw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction He. simpl in *.
    assert (Jg: a_wl_red Γ \/ ~ a_wl_red Γ).
    { eapply IHmw; eauto. lia. }
    destruct Jg as [Jg | Jg]; auto.
    right. intro Hcontra.
    dependent destruction Hcontra.
    apply Jg; auto.
  - dependent destruction He. simpl in *.
    assert (HwA: weight A >= 1) by apply weight_gt_0.
    assert (HwB: weight B >= 1) by apply weight_gt_0.
    assert (Jg: Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅).
    { eapply IHmw; eauto; simpl; try lia. }
    assert (JgInter1: forall A1 A2, B = typ_intersection A1 A2 ->
        (work_sub A A2 ⫤ᵃ work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A A2 ⫤ᵃ work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHmw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H0. apply a_wf_wl__conswork_sub; auto. }
    assert (JgInter2: forall A1 A2, A = typ_intersection A1 A2 ->
        (work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHmw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H. apply a_wf_wl__conswork_sub; auto. }
    assert (JgInter3: forall A1 A2, A = typ_intersection A1 A2 ->
        (work_sub A2 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A2 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHmw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H. apply a_wf_wl__conswork_sub; auto. }
    assert (JgUnion1: forall A1 A2, B = typ_union A1 A2 ->
        (work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHmw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H0. apply a_wf_wl__conswork_sub; auto. }
    assert (JgUnion2: forall A1 A2, B = typ_union A1 A2 ->
        (work_sub A A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHmw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H0. apply a_wf_wl__conswork_sub; au>to. }
    assert (JgUnion3: forall A1 A2, A = typ_union A1 A2 ->
        (work_sub A2 B ⫤ᵃ work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_sub A2 B ⫤ᵃ work_sub A1 B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 A2 Heq. subst.
      eapply IHmw; eauto; simpl in *; unfold split_depth in *; simpl in *; try lia.
      dependent destruction H. apply a_wf_wl__conswork_sub; auto. }
    assert (JgAlll: forall A1 X L, A = typ_all A1 ->
              a_wneq_all (awl_to_aenv Γ) B->
              X \notin  L `union` (dom (⌊ Γ ⌋ᵃ)) ->
              (work_sub (A1 ᵗ^ₜ X) B ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
            ~ (work_sub (A1 ᵗ^ₜ X) B ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
    { intros A1 X L Heq HneqAll Hnin. subst.
      eapply IHms; eauto; simpl in *; try lia.
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
      eapply IHmw; eauto; simpl in *; try lia.
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
      eapply IHmw.
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
    dependent destruction H1. dependent destruction H.
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
            { eapply a_ws__work_stay. eapply worklist_subst_fresh_etvar_total with (Γ1 := Γ1) (Γ2 := Γ2); eauto. }
            assert (JgArr1: (work_sub ` X2 (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A2) ⫤ᵃ work_sub (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A1) ` X1 ⫤ᵃ subst_typ_in_aworklist (typ_arrow ` X1 ` X2) X Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) ⟶ᵃʷ⁎⋅ \/
                          ~ (work_sub ` X2 (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A2) ⫤ᵃ work_sub (subst_typ_in_typ (typ_arrow ` X1 ` X2) X A1) ` X1 ⫤ᵃ subst_typ_in_aworklist (typ_arrow ` X1 ` X2) X Γ2 ⧺ X1 ~ᵃ ⬒ ;ᵃ X2 ~ᵃ ⬒ ;ᵃ Γ1) ⟶ᵃʷ⁎⋅).
            { eapply IHms; simpl in *; eauto.
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
         { eapply IHmw; eauto.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H2; auto.
            ** simpl in H2. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H2; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H2; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
      -- right. unfold not. intros. dependent destruction H1.
         dependent destruction H1.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H2; auto.
            ** simpl in H2. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H2; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H2; auto.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X1); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               simpl. auto.
      -- pick fresh X1. inst_cofinites_with X1.
         right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H3].
         dependent destruction H2. unify_binds. unify_binds.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H2; auto.
            ** simpl in H2. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H2; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H2; auto.
               rewrite subst_typ_in_typ_fresh_eq in H2; auto.
               rewrite subst_typ_in_typ_fresh_eq in H2; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               apply a_wf_typ_weaken_cons; auto.
      --  pick fresh X. inst_cofinites_with X.
          assert (JgAll: (work_sub (A ᵗ^ₜ X) (A0 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                       ~ (work_sub (A ᵗ^ₜ X) (A0 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
          { eapply IHmw; eauto; simpl in *; try lia.
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
         pick fresh X. inst_cofinites_with X.
         assert (JgAll: (work_sub (A ᵗ^ₜ X) (typ_union A1 A2) ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                      ~ (work_sub (A ᵗ^ₜ X) (typ_union A1 A2) ⫤ᵃ X ~ᵃ ⬒ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
         { eapply IHmw; eauto; simpl in *; try lia.
            admit. (* safe: wf *)
            admit. admit. }
        admit.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         admit.
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
