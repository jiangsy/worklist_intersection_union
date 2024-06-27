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
        n_wf_exp Ξ (exp_anno (open_exp_wrt_typ e (typ_var_f X)) (open_typ_wrt_typ A (typ_var_f X)))) ->
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
  | n_wf_work__infabsunion : forall Ξ A1 B1 A2 cd,
      lc_typ A1 ->
      lc_typ B1 ->
      lc_typ A2 ->
      n_wf_contd Ξ cd ->
      n_wf_work Ξ (work_infabsunion A1 B1 A2 cd)
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
  | exp_split_size__tabs : forall Ξ e A n,
      n_iuv_size (typ_all A) n ->
      exp_split_size Ξ (exp_tabs (exp_anno e A)) n
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
        exp_size Ξ (open_exp_wrt_typ e (typ_var_f X)) a m) ->
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
  | exp_size_conts__infabs : forall Ξ cd n m m1 m2,
      exp_size_contd Ξ cd n n m1 m2 ->
      m = m1 + m2 ->
      exp_size_conts Ξ (conts_infabs cd) n m
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
with exp_size_contd : nenv -> contd -> nat -> nat -> nat -> nat -> Prop :=
  | exp_size_contd__infabsunion : forall Ξ A cd n1 n2 m1 m2 a,
      n_iuv_size A a ->
      exp_size_contd Ξ cd (2 + n1 + a) (2 + n2 + a) m1 m2 ->
      exp_size_contd Ξ (contd_infabsunion A cd) n1 n2 m1 m2
  | exp_size_contd__infapp : forall Ξ n1 n2 m e cs ne ncs,
      exp_size Ξ e n1 ne ->
      exp_size_conts Ξ cs n2 ncs ->
      m = ne + ne * n1 + ncs ->
      exp_size_contd Ξ (contd_infapp e cs) n1 n2 0 m
  | exp_size_contd__unioninfabs : forall Ξ A B cd n1 n2 m1 m2 a b,
      n_iuv_size A a ->
      n_iuv_size B b ->
      exp_size_contd Ξ cd (2 + a + n1) (2 + b + n2) m1 m2 ->
      exp_size_contd Ξ (contd_unioninfabs A B cd) n1 n2 m1 m2.

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
  | exp_size_work__infabs : forall Ξ A cd n m m1 m2,
      n_iuv_size A n ->
      exp_size_contd Ξ cd n n m1 m2 ->
      m = m1 + m2 ->
      exp_size_work Ξ (work_infabs A cd) m
  | exp_size_work__infabsunion : forall Ξ A1 B1 A2 cd n1 n2 n m m1 m2,
      n_iuv_size A1 n1 ->
      n_iuv_size B1 n2 ->
      n_iuv_size A2 n ->
      exp_size_contd Ξ cd (2 + n1 + n) (2 + n2 + n) m1 m2 ->
      m = m1 + m2 ->
      exp_size_work Ξ (work_infabsunion A1 B1 A2 cd) m
  | exp_size_work__infapp : forall Ξ A B e cs a b n m k,
      n_iuv_size A a ->
      n_iuv_size B b ->
      exp_size Ξ e a m ->
      exp_size_conts Ξ cs b n ->
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
  | exp_size_work__unioninfabs : forall Ξ A1 A2 B1 B2 cd n1 n2 n3 n4 m m1 m2,
      n_iuv_size A1 n1 ->
      n_iuv_size A2 n2 ->
      n_iuv_size B1 n3 ->
      n_iuv_size B2 n4 ->
      exp_size_contd Ξ cd (2 + n1 + n2) (2 + n3 + n4) m1 m2 ->
      m = m1 + m2 ->
      exp_size_work Ξ (work_unioninfabs A1 B1 A2 B2 cd) m
  | exp_size_work__applys : forall Ξ cs A n m,
      n_iuv_size A n ->
      exp_size_conts Ξ cs n m ->
      exp_size_work Ξ (work_applys cs A) m
  | exp_size_work__applyd : forall Ξ cd A B n1 n2 m m1 m2,
      n_iuv_size A n1 ->
      n_iuv_size B n2 ->
      exp_size_contd Ξ cd n1 n2 m1 m2 ->
      m = m1 + m2 ->
      exp_size_work Ξ (work_applyd cd A B) m.

Inductive awl_to_nenv : aworklist -> nenv -> Prop :=
  | awl_to_nenv__empty :
      awl_to_nenv aworklist_empty nil
  | awl_to_nenv__skip_tvar : forall Γ Ξ x,
      awl_to_nenv Γ Ξ ->
      awl_to_nenv (aworklist_cons_var Γ x abind_tvar_empty) Ξ
  | awl_to_nenv__skip_stvar : forall Γ Ξ x,
      awl_to_nenv Γ Ξ ->
      awl_to_nenv (aworklist_cons_var Γ x abind_stvar_empty) Ξ
  | awl_to_nenv__skip_etvar : forall Γ Ξ x,
      awl_to_nenv Γ Ξ ->
      awl_to_nenv (aworklist_cons_var Γ x abind_etvar_empty) Ξ
  | awl_to_nenv__cons_var : forall Γ Ξ x A n,
      awl_to_nenv Γ Ξ ->
      n_iuv_size A n ->
      awl_to_nenv (aworklist_cons_var Γ x (abind_var_typ A)) ((x, nbind_var_typ n) :: Ξ)
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
  
Hint Constructors n_iuv_size exp_split_size exp_size exp_size_conts exp_size_contd exp_size_work exp_size_wl awl_to_nenv : core.

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

Ltac unify_n_iuv_size :=
  repeat 
  match goal with
  | [ H1 : n_iuv_size ?A ?n1, H2 : n_iuv_size ?A ?n2 |- _ ] =>
    eapply n_iuv_size_det with (n:=n1) (n':=n2) in H1; auto; subst
  end.

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
  - remember (dom Ξ). pick fresh X. subst. unify_n_iuv_size.
  - eapply IHHsize in Hsize'; eauto. unify_n_iuv_size. lia.
  - eapply IHHsize in Hsize'; eauto. unify_n_iuv_size. lia.
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
    unify_n_iuv_size.
    eapply H1 in H4; eauto.
  - unify_n_iuv_size.
    eapply IHHsize in Hsize'; eauto.
  - unify_n_iuv_size. 
    eapply IHHsize in Hsize'; eauto.
Qed.

Lemma exp_size_conts_det : forall Ξ cs n m m',
  exp_size_conts Ξ cs n m -> uniq Ξ -> exp_size_conts Ξ cs n m' -> m = m'
with exp_size_contd_det : forall Ξ cd n1 n2 m1 m2 m1' m2',
  exp_size_contd Ξ cd n1 n2 m1 m2 -> uniq Ξ -> exp_size_contd Ξ cd n1 n2 m1' m2' -> m1 = m1' /\ m2 = m2'.
Proof.
  - clear exp_size_conts_det. intros Ξ cs n m m' Hsize Huniq Hsize'. generalize dependent m'. generalize dependent n.
    induction cs; intros; dependent destruction Hsize; dependent destruction Hsize'; auto; try solve [unify_n_iuv_size; eauto].
    + edestruct exp_size_contd_det with (m1 := m1) in H; eauto.
  - clear exp_size_contd_det. intros Ξ cd n1 n2 m1 m2 m1' m2' Hsize Huniq Hsize'.
    generalize dependent m2'. generalize dependent m1'. generalize dependent n1. generalize dependent n2.
    induction cd; intros; dependent destruction Hsize; dependent destruction Hsize'; auto.
    + unify_n_iuv_size. 
      apply IHcd in Hsize'; auto.
    + apply exp_size_conts_det with (m := ncs) in H2; auto. subst.
      apply exp_size_det with (m := ne) in H1; auto.
    + unify_n_iuv_size. eauto.
Qed.

Lemma exp_size_work_det : forall Ξ w n n',
  uniq Ξ -> exp_size_work Ξ w n -> exp_size_work Ξ w n' -> n = n'.
Proof.
  intros Ξ w n n' Huniq Hsize. generalize dependent n'.
  induction Hsize; intros n' Hsize'; dependent destruction Hsize'; eauto.
  - eapply exp_size_det in H; eauto.
    eapply exp_split_size_det in H0; eauto. subst.
    eapply exp_size_conts_det in H5; eauto.
  - unify_n_iuv_size.
    eapply exp_size_det in H0; eauto.
  - unify_n_iuv_size.
    eapply exp_size_contd_det in H0; eauto.
    destruct H0. subst. auto.
  - unify_n_iuv_size.
    eapply exp_size_contd_det in H2; eauto.
    destruct H2. subst. auto.
  - unify_n_iuv_size.
    eapply exp_size_det in H1; eauto. subst.
    eapply exp_size_conts_det in H2; eauto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H1; eauto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H2; eauto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H1; eauto.
  - unify_n_iuv_size. subst.
    eapply exp_size_contd_det in H3; eauto.
    destruct H3. subst. auto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H2; eauto.
  - unify_n_iuv_size.
    eapply exp_size_contd_det in H1; eauto.
    destruct H1. subst. auto.
Qed.

Lemma awl_to_nenv_dom : forall Γ Ξ,
  awl_to_nenv Γ Ξ -> dom Ξ [<=] dom (⌊ Γ ⌋ᵃ).
Proof.
  intros Γ Ξ Hnenv. dependent induction Hnenv; simpl; fsetdec.
Qed.

Lemma awl_to_nenv_uniq : forall Γ Ξ,
  awl_to_nenv Γ Ξ -> uniq (⌊ Γ ⌋ᵃ) -> uniq Ξ.
Proof.
  intros Γ Ξ Hnenv Huniq.
  dependent induction Hnenv; eauto;
    dependent destruction Huniq; eauto.
  erewrite <- awl_to_nenv_dom in H0; eauto.
Qed.

Lemma awl_to_nenv_det : forall Γ Ξ Ξ',
  awl_to_nenv Γ Ξ -> awl_to_nenv Γ Ξ' -> Ξ = Ξ'.
Proof.
  intros Γ Ξ Ξ' Henv. generalize dependent Ξ'.
  induction Henv; intros Ξ' Henv'; dependent destruction Henv'; eauto.
  eapply IHHenv in Henv'; eauto. subst.
  eapply n_iuv_size_det in H; eauto. subst. auto.
Qed.

Lemma exp_size_wl_det : forall Γ n n',
  uniq (⌊ Γ ⌋ᵃ) ->
  exp_size_wl Γ n -> 
  exp_size_wl Γ n' -> 
  n = n'.
Proof.
  intros * Huniq Hsize1 Hsize2. generalize dependent n'. 
  induction Hsize1; intros; dependent destruction Hsize2; eauto.
  - dependent destruction Huniq; eauto.
  - simpl in Huniq.
    eapply awl_to_nenv_det in H; eauto. subst.
    (* eapply awl_to_nenv_det in Ha2n; eauto. subst. *)
    eapply exp_size_work_det in H0; eauto.
    eapply awl_to_nenv_uniq; eauto.
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

Lemma exp_split_size_rename_tvar : forall Ξ e X Y n,
  uniq Ξ ->
  Y `notin` dom Ξ ->
  exp_split_size Ξ e n -> 
  exp_split_size Ξ (subst_typ_in_exp (typ_var_f Y) X e) n.
Proof with eauto using exp_split_size.
  intros. dependent induction H1; simpl in *...
  - remember (dom Ξ). inst_cofinites_for exp_split_size__abs. subst. 
    intros. inst_cofinites_with x.
    replace (exp_var_f x) with (subst_typ_in_exp (typ_var_f Y) X (exp_var_f x))...
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp...
  - econstructor.
    replace (typ_all ({` Y ᵗ/ₜ X} A)) with  ({` Y ᵗ/ₜ X} typ_all A) by auto.
    apply n_iuv_size_rename; eauto.
  - econstructor; eauto.
    + eapply n_iuv_size_rename...
    + lia.
  - econstructor; eauto.
    + eapply n_iuv_size_rename...
    + lia.
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
  - remember (dom Ξ). pick fresh X.
    assert (lc_typ (typ_all A)). { pick fresh X0. inst_cofinites_with X0.
      dependent destruction H0. apply lc_typ_all_exists with (X1:=X0). auto. }
    apply n_iuv_size_total in H2. destruct H2 as [n].
    exists n. econstructor; eauto.
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
  | eq_nenv__var : forall Ξ Ξ' x n n',
      equiv_nenv Ξ Ξ' ->
      equiv_nenv ((x, nbind_var_typ n) :: Ξ) ((x, nbind_var_typ n') :: Ξ').

Lemma equiv_nenv_binds_var : forall Ξ Ξ' x n,
  equiv_nenv Ξ Ξ' ->
  binds x (nbind_var_typ n) Ξ ->
  exists n', binds x (nbind_var_typ n') Ξ'.
Proof.
  intros. induction H; destruct_binds; destruct_conj; eauto.
  apply IHequiv_nenv in H2. destruct_conj; eauto.
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
Qed.

Lemma exp_size_rename_tvar : forall Ξ e X Y n m,
  uniq Ξ ->
  Y `notin` dom Ξ ->
  exp_size Ξ e n m -> 
  exp_size Ξ (subst_typ_in_exp (typ_var_f Y) X e) n m.
Proof.
  intros. dependent induction H1; simpl in *; eauto using exp_size.
  - remember (dom Ξ). inst_cofinites_for exp_size__abs m:=m; eauto. intros. subst.
    subst. replace (exp_var_f x) with (subst_typ_in_exp (typ_var_f Y) X (exp_var_f x)); auto.
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp.
    eapply H2; eauto.
  - econstructor; eauto.
    apply exp_split_size_rename_tvar; eauto.  
  - remember (dom Ξ). 
    inst_cofinites_for exp_size__tabs n:=n,m:=m,a:=a; eauto; intros; subst.
    + erewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
      apply n_iuv_size_rename; eauto.
    + erewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2; eauto.
  - econstructor; eauto.
    apply n_iuv_size_rename; eauto.
  - econstructor; eauto.
    apply n_iuv_size_rename; eauto.
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
    rewrite <- subst_exp_in_exp_open_exp_wrt_typ; eauto.
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
    specialize (H1 H Ξ' H2 n). 
    destruct H1 as [m].
    dependent destruction H1.
    exists (1 + m * n + m + n). 
    remember (dom Ξ). inst_cofinites_for exp_size__tabs a:=a,m:=m; eauto; intros; subst.
    + erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
      eapply n_iuv_size_rename; eauto. 
    + replace (e ᵉ^^ₜ ` X0) with (subst_typ_in_exp (typ_var_f X0) X (e ᵉ^^ₜ `X))...
      eapply exp_size_rename_tvar; eauto; simpl.
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
with exp_size_contd_total : forall Ξ cd n1 n2,
  uniq Ξ ->
  n_wf_contd Ξ cd ->
  exists m1 m2, exp_size_contd Ξ cd n1 n2 m1 m2.
Proof with eauto  using exp_size_conts.
  - clear exp_size_conts_total. intros. generalize dependent n. induction H0; intros...
    + eapply exp_size_contd_total with (n1:=n) in H0... destruct_conj; eauto.
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
  - clear exp_size_contd_total. intros.
    generalize dependent n2. generalize dependent n1.
    induction H0; intros.
    + apply n_iuv_size_total in H0. 
      destruct H0 as [a].
      specialize (IHn_wf_contd H (2 + n1 + a) (2 + n2 + a)).
      destruct_conj; eauto.
    + eapply exp_size_total with (n:=n1) in H as Hesz; eauto.
      eapply exp_size_conts_total with (n:=n2) in H1; eauto.
      destruct_conj; eauto. 
    + apply n_iuv_size_total in H0. 
      destruct H0 as [a].
      apply n_iuv_size_total in H1. 
      destruct H1 as [b].
      specialize (IHn_wf_contd H (2 + a + n1) (2 + b + n2)).
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
    apply exp_size_contd_total with (n1:=n) (n2:=n) in H1...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply n_iuv_size_total in H2. destruct H2 as [n].
    apply exp_size_contd_total with (n1:=(2+n1+n)) (n2:=(2+n2+n)) in H3...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0.
    destruct H0 as [a].
    apply n_iuv_size_total in H1.
    destruct H1 as [b].
    apply exp_size_total with (n:=a) in H2...
    apply exp_size_conts_total with (n:=b) in H3...
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
    apply n_iuv_size_total in H2. destruct H2 as [n3].
    apply n_iuv_size_total in H3. destruct H3 as [n4].
    apply exp_size_contd_total with (n1:=(2+n1+n2)) (n2:=(2+n3+n4)) in H4...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. 
    destruct H0 as [n].
    apply exp_size_conts_total with (n:=n) in H1...
    destruct_conj; eauto.
  - apply n_iuv_size_total in H0. destruct H0 as [n1].
    apply n_iuv_size_total in H1. destruct H1 as [n2].
    apply exp_size_contd_total with (n1:=n1) (n2:=n2) in H2...
    destruct_conj; eauto.
Qed.

Lemma binds_var_typ_binds_var_num : forall Γ Ξ x A,
  ⊢ᵃʷ Γ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ -> 
  awl_to_nenv Γ Ξ ->
  exists n, binds x (nbind_var_typ n) Ξ.
Proof.
  intros. dependent induction H1; eauto; destruct_binds; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H3; destruct_conj; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H3; destruct_conj; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H3; destruct_conj; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H4; destruct_conj; eauto.
  - dependent destruction H; apply IHawl_to_nenv in H0; destruct_conj; eauto. 
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
  - unify_n_iuv_size.
    eapply exp_size_contd_det in H; eauto. lia.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H2; eauto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H4; eauto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det in H2; eauto.
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
  assert (X ∉ ftvar_in_work w). {
    rewrite <- ftvar_in_wf_work_upper in H1;eauto.
  }
  erewrite <- split_depth_work_etvar; eauto. 
Qed.

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
  ⊢ᵃʷ Γ -> 
  split_depth_rec (⌊ Γ ⌋ᵃ) A n > 0 ->
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
  ⊢ᵃʷ Γ -> 
  split_depth_rec (⌊ Γ ⌋ᵃ) A n > 0 -> 
  n < m ->
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

Lemma infabs_depth_open_tvar_rec : forall A X n,
  infabs_depth (open_typ_wrt_typ_rec n (typ_var_f X) A) = infabs_depth A.
Proof.
  intros. generalize dependent n; induction A; intros; simpl; eauto.  
  - destruct (lt_eq_lt_dec n n0); eauto. 
    destruct s; eauto.
Qed.

Lemma infabs_depth_open_tvar : forall A X,
  infabs_depth (open_typ_wrt_typ A (typ_var_f X) ) = infabs_depth A.
Proof.  
  intros. unfold open_typ_wrt_typ. erewrite infabs_depth_open_tvar_rec; eauto.
Qed.

Lemma split_depth_rec_non_mono_lt : forall A Γ n m,
  ⊢ᵃʷ Γ -> 
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃ A -> 
  (⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A -> False) ->
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

Lemma apply_conts_total : forall c A,
  exists w, apply_conts c A w.
Proof.
  intros. induction c; eauto.
Qed.

Lemma apply_contd_total : forall c A B,
  exists w, apply_contd c A B w.
Proof.
  intros. induction c; eauto.
Qed.

Inductive le_nenv : nenv -> nenv -> Prop :=
  | le_nenv_base : forall Ξ, le_nenv Ξ Ξ
  | le_nenv_cons : forall Ξ Ξ' x n n',
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
    unify_n_iuv_size. lia.
  - eapply IHHsize in Hsize'; eauto.
    unify_n_iuv_size.
    eapply mult_le_compat_r with (p := S (S m0)) in Hsize'. lia.
  - eapply IHHsize in Hsize'; eauto.
    unify_n_iuv_size.
    eapply mult_le_compat_r with (p := S (S m0)) in Hsize'. lia.
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
    unify_n_iuv_size.
    eapply H1 in H4; eauto.
    eapply mult_le_compat with (p := n) (q := n0) in H4 as Hlemn; eauto. lia.
  - eapply n_iuv_size_det in H; eauto. subst.
    eapply mult_le_compat_l with (p := a) in Hlen as Hlean; eauto.
    eapply IHHsize in Hsize'; eauto; try lia.
    eapply mult_le_compat with (p := n) (q := n0) in Hsize' as Hlemn; eauto. lia.
  - unify_n_iuv_size.
    eapply IHHsize in Hsize'; eauto.
    eapply mult_le_compat with (p := n) (q := n0) in Hsize' as Hlemn; eauto. lia.
Qed.

Lemma exp_size_conts_le : forall c Ξ Ξ' n n' m m',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  exp_size_conts Ξ c n m -> exp_size_conts Ξ' c n' m' ->
  n <= n' -> m <= m'
with exp_size_contd_le : forall c Ξ Ξ' n1 n1' n2 n2' m1 m1' m2 m2',
  uniq Ξ -> le_nenv Ξ Ξ' ->
  exp_size_contd Ξ c n1 n2 m1 m2 ->
  exp_size_contd Ξ' c n1' n2' m1' m2' ->
  n1 <= n1' -> n2 <= n2' -> m1 <= m1' /\ m2 <= m2'.
Proof.
  - clear exp_size_conts_le.
    intro c. induction c; intros * Huniq Hle Hsize * Hsize' Hlen; dependent destruction Hsize; dependent destruction Hsize'; try lia.
    + apply exp_size_contd_le with (Ξ := Ξ) (n1 := n) (n2 := n) (m1 := m1) (m2 := m2) in H0; auto. lia.
    + apply IHc with (Ξ := Ξ) (n := (2 + b) * n) (m := m) in Hsize'; auto.
      unify_n_iuv_size.
      apply mult_le_compat_r with (p := b0) in Hlen as Hlen'. lia.
    + apply IHc with (Ξ := Ξ) (n := 2 + a * (2 + b) + n) (m := m) in Hsize'; auto.
      unify_n_iuv_size.
      eapply mult_le_compat_r with (p := b0) in Hlen as Hlen'. lia.
    + apply IHc with (Ξ := Ξ) (n := 2 + a + n) (m := m) in Hsize'; auto.
      unify_n_iuv_size. lia.
  - clear exp_size_contd_le.
    intro c. induction c; intros * Huniq Hle Hsize * Hsize' Hlen1 Hlen2;
      dependent destruction Hsize; dependent destruction Hsize'; try lia.
    + unify_n_iuv_size. 
      apply IHc with (Ξ := Ξ) (n1 := 2 + n1 + a0) (n2 := 2 + n2 + a0) (m1 := m1) (m2 := m2) in Hsize'; auto; lia.
    + apply exp_size_le with (Ξ := Ξ) (n := n1) (m := ne) in H1; auto.
      apply exp_size_conts_le with (Ξ := Ξ) (n := n2) (m := ncs) in H2; auto.
      apply mult_le_compat with (p := ne) (q := ne0) in Hlen1; auto. lia. 
    + unify_n_iuv_size.
      apply IHc with (Ξ := Ξ) (n1 := 2 + a0 + n1) (n2 := 2 + b0 + n2) (m1 := m1) (m2 := m2) in Hsize'; auto; lia.
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
      eapply le_nenv_cons; eauto. lia.
      eapply le_nenv_cons; eauto. lia.
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
    eapply exp_size_le with (Ξ := Ξ0) in H0 as Hlem1; eauto.
    eapply exp_size_le with (Ξ := Ξ1) in H0 as Hlem2; eauto.
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
    unify_n_iuv_size.
    eapply mult_le_compat_l with (p := a1) in Hlt as Hlt'.
    eapply IHHsize with (Ξ1 := Ξ0) in Hs2; eauto; try lia.
    assert (m0 * n0 + m1 * n1 + m0 + m1 <= m * n).
    {
      eapply mult_le_compat with (n := S (m1 + m0)) (m := m) in Hlt; try lia.
    }
    lia.
  - unfold lt in *.
    eapply le_nenv_uniq_r in Hle1 as Huniq1; eauto.
    eapply le_nenv_uniq_r in Hle2 as Huniq2; eauto.
    unify_n_iuv_size.
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

Lemma apply_contd_exp_size : forall Ξ c A B w a b n1 n2 m,
  uniq Ξ -> apply_contd c A B w ->
  n_iuv_size A a -> n_iuv_size B b ->
  exp_size_contd Ξ c a b n1 n2 ->
  exp_size_work Ξ w m -> m = n1 + n2.
Proof.
  intros Ξ c A B w a b n1 n2 m Huniq Happly Ha Hb Hsize1 Hsize2.
  induction Happly; dependent destruction Hsize1; dependent destruction Hsize2; eauto.
  - unify_n_iuv_size.
    eapply exp_size_conts_det with (m' := n) in H0; eauto.
    eapply exp_size_det in H; eauto. subst. lia.
  - unify_n_iuv_size.
    eapply exp_size_contd_det in Hsize1; eauto. lia.
  - unify_n_iuv_size.
    eapply exp_size_contd_det in Hsize1; eauto. lia.
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
  inst_cofinites_for exp_split_size__abs n:=n; try lia.
  intros * Hnotin.
  rewrite_env ((x ~ nbind_var_typ 0 ++ Ξ3) ++ Ξ2 ++ Ξ1).
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
Qed.

Lemma exp_size_conts_weaken : forall c Ξ1 Ξ2 Ξ3 n m,
  exp_size_conts (Ξ3 ++ Ξ1) c n m ->
  exp_size_conts (Ξ3 ++ Ξ2 ++ Ξ1) c n m
with exp_size_contd_weaken : forall c Ξ1 Ξ2 Ξ3 n1 n2 m1 m2,
  exp_size_contd (Ξ3 ++ Ξ1) c n1 n2 m1 m2 ->
  exp_size_contd (Ξ3 ++ Ξ2 ++ Ξ1) c n1 n2 m1 m2.
Proof.
  - clear exp_size_conts_weaken. intro c. induction c; intros * Hsize; dependent destruction Hsize; eauto.
  - clear exp_size_contd_weaken. intro c. induction c; intros * Hsize; dependent destruction Hsize; eauto.
    eapply exp_size_weaken in H; eauto.
Qed.

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
    + unify_n_iuv_size.
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

Lemma n_iuv_size_mono_typ : forall Σ A,
  a_mono_typ Σ A -> n_iuv_size A 0.
Proof.
  intros Σ A Hmono. induction Hmono; eauto.
Qed.

Lemma num_occurs_in_typ_subst_eq : forall A B X Y n m,
  X `notin` ftvar_in_typ B `union` (singleton Y) -> lc_typ B ->
  num_occurs_in_typ X (subst_typ_in_typ B Y A) n ->
  num_occurs_in_typ X A m -> n = m.
Proof.
  intros A B X Y n m Hfv Hlcb Hocc1 Hocc2.
  generalize dependent B. generalize dependent Y.
  generalize dependent n.
  induction Hocc2; intros; simpl in *; eauto;
    try solve [dependent destruction Hocc1; eauto; lia].
  - destruct_eq_atom.
    dependent destruction Hocc1; auto.
    exfalso. eauto.
  - destruct_eq_atom.
    + erewrite num_occurs_in_typ_fresh with (n := n); eauto.
    + dependent destruction Hocc1; eauto.
      exfalso. eauto.
  - dependent destruction Hocc1.
    pick fresh Y0. inst_cofinites_with Y0.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H1; eauto.
Qed.

Lemma n_iuv_size_lc_typ : forall A n,
  n_iuv_size A n -> lc_typ A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma n_iuv_size_subst_mono' : forall A n Σ B X,
  n_iuv_size A n -> a_mono_typ Σ B ->
  n_iuv_size ({B ᵗ/ₜ X} A) n.
Proof.
  intros A n Σ B X Hsize.
  generalize dependent B. generalize dependent Σ.
  induction Hsize; intros * Hmono; eauto; simpl; eauto.
  - destruct_eq_atom; eauto. eapply n_iuv_size_mono_typ; eauto.
  - simpl. inst_cofinites_for n_iuv_size__all n:=n,m:=m; auto; intros * Hnotin;
      inst_cofinites_with X0; rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2; eauto.
    assert (Hn: exists m, num_occurs_in_typ X0 ({B ᵗ/ₜ X} A ᵗ^ₜ X0) m).
    { eapply num_occurs_in_typ_total; eauto.
      eapply lc_typ_subst; eauto. eapply n_iuv_size_lc_typ; eauto. }
    destruct Hn as [m' Hn].
    eapply num_occurs_in_typ_subst_eq in H1; eauto. subst. auto.
Qed.

Lemma n_iuv_size_subst_mono : forall A n n' Σ B X,
  Σ ᵗ⊢ᵃₘ B -> 
  n_iuv_size A n -> 
  n_iuv_size ({B ᵗ/ₜ X} A) n' ->
  n = n'.
Proof.
  intros. eapply n_iuv_size_subst_mono' with (X:=X) in H0; eauto.
  unify_n_iuv_size.
Qed.

Lemma awl_to_nenv_tvar : forall Γ2 Γ1 X b Ξ Ξ',
  b = □%abind \/ b = ■%abind \/ b = ⬒ ->
  awl_to_nenv (Γ2 ⧺ X ~ᵃ b; Γ1) Ξ ->
  awl_to_nenv (Γ2 ⧺ Γ1) Ξ' -> Ξ = Ξ'.
Proof.
  intros Γ2. induction Γ2; intros * Hbinds Hsize1 Hsize2; simpl in *.
  - dependent destruction Hsize1; try solve [eapply awl_to_nenv_det; eauto].
    destruct Hbinds as [Hbinds | [Hbinds | Hbinds]];
      dependent destruction Hbinds.
  - dependent destruction Hsize1; dependent destruction Hsize2;
      simpl in *; eauto.
    eapply n_iuv_size_det in H; eauto.
    eapply IHΓ2 in Hsize2; eauto. subst. eauto.
  - dependent destruction Hsize1; dependent destruction Hsize2;
      simpl in *; eauto.
Qed.

Lemma aworklist_subst_same_nenv : forall Γ2 X A Γ1 Γ1' Γ2' Ξ Ξ',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' ->
  ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ ᵗ⊢ᵃₘ A ->
  awl_to_nenv (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) Ξ ->
  awl_to_nenv ({A ᵃʷ/ₜ X} Γ2' ⧺ Γ1') Ξ' ->
  Ξ = Ξ'.
Proof.
   intros Γ2. induction Γ2; intros * Hwf Hsubst Hmono Hsize1 Hsize2;
    dependent destruction Hwf; dependent destruction Hsubst;
    simpl in *; dependent destruction Hsize1;
    eapply awl_to_nenv_det in Hsize1 as Hdet; eauto; subst;
    try solve [exfalso; eauto].
  - dependent destruction Hsize2.
    eapply n_iuv_size_subst_mono in H2; eauto. subst. 
    assert (Heq: Ξ = Ξ0).
    { eapply IHΓ2; eauto. eapply a_mono_typ_strengthen_var; eauto. }
    subst. eauto.
  - dependent destruction Hsize2.
    assert (Heq: Ξ = Ξ0).
    { eapply IHΓ2; eauto.
      eapply a_mono_typ_strengthen_mtvar with (b := □%abind); eauto. }
    subst. eauto.
  - dependent destruction Hsize2.
    assert (Heq: Ξ = Ξ0).
    { eapply IHΓ2; eauto.
      eapply a_mono_typ_strengthen_stvar; eauto. }
    subst. eauto.
  - dependent destruction Hsize2.
    assert (Heq: Ξ = Ξ0).
    { eapply IHΓ2; eauto.
      eapply a_mono_typ_strengthen_mtvar with (b := ⬒); eauto. }
    subst. eauto.
  - eapply worklist_split_etvar_det in x. destruct x. subst.
    assert (Heq: Ξ = Ξ').
    { eapply IHΓ2 with (Γ1 := X ~ᵃ ⬒ ;ᵃ Γ1) (A := A); eauto.
      eapply a_wf_wwl_move_etvar_back; eauto.
      eapply a_mono_typ_move_etvar_back; eauto.
      assert (Hsize: exists Ξ, awl_to_nenv (Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ1) Ξ).
      { eapply awl_to_nenv_total; eauto. eapply a_wf_wwl_move_etvar_back; eauto. }
      destruct Hsize as [Ξ'' Hsize].
      rewrite awl_rewrite_middle in Hsize1.
      rewrite awl_rewrite_middle in Hsize.
      eapply awl_to_nenv_tvar in Hsize1; eauto. subst.
      rewrite <- awl_rewrite_middle in Hsize. eauto. }
    subst. eauto.
    eapply a_wf_wwl_tvar_notin_remaining in Hwf; eauto.
  - dependent destruction Hsize2.
    assert (Heq: Ξ = Ξ0).
    { eapply IHΓ2; eauto. }
    subst. eauto.
Qed.

Lemma exp_split_size_subst_mono : forall Ξ Σ e A X m m',
  uniq Ξ -> 
  Σ ᵗ⊢ᵃₘ A ->
  exp_split_size Ξ e m -> 
  exp_split_size Ξ ({A ᵉ/ₜ X} e) m' -> 
  m = m'.
Proof.
  intros * Huniq Hmono Hsz Hszsusbt. 
    generalize dependent m'. induction Hsz; intros; simpl in *; dependent destruction Hszsusbt; simpl in *; eauto.
  - unify_binds; eauto.
  - remember (dom Ξ). pick fresh x. inst_cofinites_with x. subst.
    replace (exp_var_f x) with ({A ᵉ/ₜ X} (exp_var_f x)) in H1; eauto.
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp in H1.
    apply H0 in H1; eauto. 
  - apply IHHsz1 in Hszsusbt1; eauto.
    apply IHHsz2 in Hszsusbt2; eauto. subst. auto.
  - eapply n_iuv_size_subst_mono in H; eauto.
  - apply IHHsz in Hszsusbt; eauto.
    eapply n_iuv_size_subst_mono in H; eauto. subst. 
    auto.
  - apply IHHsz in Hszsusbt; eauto. 
    eapply n_iuv_size_subst_mono in H; eauto. subst.
    auto.
Qed.

Lemma exp_size_subst_mono : forall Ξ Σ e A X n m m',
  uniq Ξ ->
  Σ ᵗ⊢ᵃₘ A ->
  exp_size Ξ e n m -> 
  exp_size Ξ ({A ᵉ/ₜ X} e) n m' -> 
  m = m'.
Proof.
  intros * Huniq Hmono Hsize1 Hsize2.
  generalize dependent m'. generalize dependent X. generalize dependent A.
  dependent induction Hsize1; intros; dependent destruction Hsize2; eauto.
  - remember (dom Ξ). pick fresh x. inst_cofinites_with x. subst.
    replace (exp_var_f x) with ({A ᵉ/ₜ X} (exp_var_f x)) in H2; eauto.
    rewrite <- subst_typ_in_exp_open_exp_wrt_exp in H2.
    apply H0 in H2; eauto.
  - eapply exp_split_size_subst_mono in H1; eauto.
    eapply IHHsize1_1 in Hsize2_1; eauto. subst.
    eapply IHHsize1_2 in Hsize2_2; eauto.
  - pick fresh X0. inst_cofinites_with X0.
    rewrite subst_typ_in_typ_open_typ_wrt_typ_fresh2 in H3; eauto.
    eapply n_iuv_size_subst_mono in H; eauto. subst.
    rewrite subst_typ_in_exp_open_exp_wrt_typ_fresh2 in H4; eauto.
    apply H1 in H4; eauto.
  - eapply n_iuv_size_subst_mono in H1; eauto. subst.
    apply IHHsize1 in Hsize2; eauto. 
  - eapply n_iuv_size_subst_mono in H1; eauto. subst.
    eapply IHHsize1 in Hsize2; eauto.
Qed.

Lemma exp_size_conts_subst_mono : forall Ξ Σ c A X n m m',
  uniq Ξ ->  Σ ᵗ⊢ᵃₘ A -> exp_size_conts Ξ c n m -> exp_size_conts Ξ ({A ᶜˢ/ₜ X} c) n m' -> m = m'
with exp_size_contd_subst_mono : forall Ξ Σ c A X n1 n2 m1 m2 m1' m2',
  uniq Ξ ->  Σ ᵗ⊢ᵃₘ A -> exp_size_contd Ξ c n1 n2 m1 m2 -> exp_size_contd Ξ ({A ᶜᵈ/ₜ X} c) n1 n2 m1' m2' -> m1 = m1' /\ m2 = m2'.
Proof.
  - intros * Huniq Hmono Hsize1 Hsize2. clear exp_size_conts_subst_mono; generalize dependent m'.
    generalize dependent n; generalize dependent X; generalize dependent A.
    induction c; intros; simpl in *; dependent destruction Hsize1; dependent destruction Hsize2; eauto.
    + eapply exp_size_contd_subst_mono in H0; destruct_conj; eauto.
    + eapply n_iuv_size_subst_mono in H; eauto. subst.
      eapply IHc in Hsize1; eauto.
    + eapply n_iuv_size_subst_mono in H; eauto. subst.
      eapply n_iuv_size_subst_mono in H0; eauto. subst.
      eapply IHc in Hsize1; eauto.
    + eapply n_iuv_size_subst_mono in H; eauto. subst.
      eapply IHc in Hsize1; eauto.
  - intros * Huniq Hmono Hsize1 Hsize2. clear exp_size_contd_subst_mono; generalize dependent m1'; generalize dependent m2'.
    generalize dependent n1; generalize dependent n2; generalize dependent X; generalize dependent A.
    induction c; intros; simpl in *; dependent destruction Hsize1; dependent destruction Hsize2; auto.
    + eapply n_iuv_size_subst_mono in H0; eauto 3. subst.
      eapply IHc in Hsize2; eauto 3.
    + eapply exp_size_subst_mono in H1; eauto 3.
      eapply exp_size_conts_subst_mono in H2; eauto 3.
      subst. auto.
    + eapply n_iuv_size_subst_mono in H1; eauto 3.
      eapply n_iuv_size_subst_mono in H2; eauto 3. subst.
      eapply IHc in Hsize2; eauto 3.
Qed.

Lemma exp_size_work_aworklist_subst : forall X w A Γ1 Γ2 Γ1' Γ2' Ξ Ξ' m m',
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ ʷ⊢ᵃ w ->
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' ->
  ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ ᵗ⊢ᵃₘ A ->
  X `notin` ftvar_in_typ A ->
  awl_to_nenv (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) Ξ ->
  awl_to_nenv ({A ᵃʷ/ₜ X} Γ2' ⧺ Γ1') Ξ' ->
  exp_size_work Ξ w m ->
  exp_size_work Ξ' ({A ʷ/ₜ X} w) m' ->
  m = m'.
Proof.
  intros X w A Γ1 Γ2 Γ1' Γ2' Ξ Ξ' m m' Hwf1 Hwf2 Hsubst Hmono Hnotin Ha2n Ha2n' Hsize1 Hsize2.
  assert (Huniq : uniq Ξ'). {
      eapply awl_to_nenv_uniq; eauto.
      apply a_wf_wwl_uniq.
      eapply aworklist_subst_wf_wwl; eauto.
    }
  induction Hsize1; simpl in *; dependent destruction Hsize2.
  - eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply exp_size_subst_mono in H3; eauto.
    eapply exp_split_size_subst_mono in H4; eauto. subst.
    eapply exp_size_conts_subst_mono in H5; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H1; eauto.
    eapply n_iuv_size_det in H3; eauto. subst.
    eapply exp_size_subst_mono in H2; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono in H4; eauto. subst.
    eapply exp_size_contd_subst_mono in H2; eauto. lia.
  - dependent destruction Hwf2. dependent destruction H.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono in H8; eauto.
    eapply n_iuv_size_subst_mono in H9; eauto.
    eapply n_iuv_size_subst_mono in H10; eauto. subst.
    eapply exp_size_contd_subst_mono in H6; eauto. lia.
  - dependent destruction Hwf2. dependent destruction H.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H8; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H9; eauto. subst.
    eapply exp_size_subst_mono in H5; eauto. subst.
    eapply exp_size_conts_subst_mono in H6; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H5; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H6; eauto. subst.
    eapply exp_size_conts_subst_mono in H4; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H7; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H8; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H9; eauto. subst.
    eapply exp_size_conts_subst_mono in H6; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H5; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H6; eauto. subst.
    eapply exp_size_conts_subst_mono in H4; eauto.
  - dependent destruction Hwf2.
    dependent destruction H. dependent destruction H1.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H9; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H10; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H11; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H12; eauto. subst.
    eapply exp_size_contd_subst_mono in H7; eauto. lia.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H3; eauto. subst.
    eapply exp_size_conts_subst_mono in H2; eauto.
  - dependent destruction Hwf2.
    eapply aworklist_subst_same_nenv in Ha2n; eauto. subst.
    eapply n_iuv_size_subst_mono with (X := X) in H6; eauto.
    eapply n_iuv_size_subst_mono with (X := X) in H7; eauto. subst.
    eapply exp_size_contd_subst_mono in H4; eauto. lia.
Qed. 

Lemma exp_size_wl_move_etvar_back : forall X Y Γ1 Γ2 n m,
  uniq (⌊ Y ~ᵃ ⬒ ;ᵃ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ) ->
  exp_size_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) n -> 
  exp_size_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Y ~ᵃ ⬒ ;ᵃ Γ1) m ->
  n = m.
Proof.
  intros * Huniq Hsize1 Hsize2. generalize dependent n; generalize dependent m; induction Γ2; intros; simpl in *; eauto.
  - dependent destruction Hsize1. dependent destruction Hsize2. 
    dependent destruction Hsize2; eauto. 
    eapply exp_size_wl_det in Hsize2; eauto.
    dependent destruction Huniq. dependent destruction Huniq. auto.
  - dependent destruction Huniq. dependent destruction Huniq.
    dependent destruction Hsize1. dependent destruction Hsize2. eauto. 
  - dependent destruction Hsize1. dependent destruction Hsize2.
    rewrite awl_rewrite_middle in H.
    eapply awl_to_nenv_tvar with (X:=Y) (Γ2:=(Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ aworklist_empty)%aworklist) (Γ1:=Γ1) (Ξ':=Ξ0) in H; eauto.
    subst. eapply exp_size_work_det in H0; eauto.
    dependent destruction Huniq. eapply awl_to_nenv_uniq; eauto.
    rewrite <- awl_rewrite_middle. eauto.  
Qed.

Open Scope aworklist.

Lemma exp_size_wl_aworklist_subst : forall Γ2 X A Γ1 Γ1' Γ2' n m,
  ⊢ᵃʷ (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) ->
  aworklist_subst (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) X A Γ1' Γ2' ->
  X `notin` ftvar_in_typ A ->
  ⌊ Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1 ⌋ᵃ ᵗ⊢ᵃₘ A ->
  exp_size_wl ({A ᵃʷ/ₜ X} Γ2' ⧺ Γ1') n ->
  exp_size_wl (Γ2 ⧺ X ~ᵃ ⬒ ;ᵃ Γ1) m -> n = m.
Proof.
  intros Γ2. induction Γ2; intros * Hwf Hsubst Hnotin Hmono Hsize1 Hsize2;
    dependent destruction Hwf; dependent destruction Hsubst;
    destruct (awl_to_nenv_total _ Hwf) as [Ξ Ha2n];
    eapply awl_to_nenv_uniq in Ha2n as Huniq; eauto;
    simpl in *; dependent destruction Hsize2;
    try solve [exfalso; eauto];
    try solve [eapply exp_size_wl_det in Hsize1; eauto];
    try solve [dependent destruction Hsize1; eapply IHΓ2; eauto;
      try solve [eapply a_mono_typ_strengthen_var; eauto];
      try solve [eapply a_mono_typ_strengthen_mtvar with (b := □%abind); eauto];
      try solve [eapply a_mono_typ_strengthen_mtvar with (b := ⬒); eauto];
      try solve [eapply a_mono_typ_strengthen_stvar; eauto]].
  - eapply worklist_split_etvar_det in x. destruct x. subst.
    eapply IHΓ2 with (Γ1 := X ~ᵃ ⬒ ;ᵃ Γ1) (A := A); eauto.
    eapply a_wf_wwl_move_etvar_back; eauto.
    eapply a_mono_typ_move_etvar_back; eauto.
    assert (⊢ᵃʷ (Γ2 ⧺ X0 ~ᵃ ⬒ ;ᵃ X ~ᵃ ⬒ ;ᵃ Γ1)). {
      apply a_wf_wwl_move_etvar_back; eauto.
    }
    apply exp_size_wl_total in H2. destruct H2 as [m H2].
    erewrite exp_size_wl_move_etvar_back with (Y:=X) (X:=X0); eauto.
    eapply a_wf_wwl_tvar_notin_remaining in Hwf; eauto.
  - dependent destruction Hsize1.
    erewrite IHΓ2 with (n := n); eauto.
    eapply exp_size_work_aworklist_subst in H3; eauto.
Qed.

Lemma exp_size_wl_aworklist_subst' : forall Γ X A Γ1' Γ2' n m,
  ⊢ᵃʷ Γ -> X ~ ⬒ ∈ᵃ ⌊ Γ ⌋ᵃ ->
  aworklist_subst Γ X A Γ1' Γ2' ->
  ⌊ Γ ⌋ᵃ ᵗ⊢ᵃₘ A ->
  X `notin` ftvar_in_typ A ->
  exp_size_wl ({A ᵃʷ/ₜ X} Γ2' ⧺ Γ1') n ->
  exp_size_wl Γ m -> n = m.
Proof.
  intros * Hwf Hbinds Hsubst Hmono Hnotin Hsize1 Hsize2.
  eapply awl_split_etvar in Hbinds as [Γ1 [Γ2 Hbinds]]. subst.
  eapply exp_size_wl_aworklist_subst in Hsize2; eauto.
Qed.

Lemma awl_to_nenv_dom' : forall Γ Ξ x A,
  awl_to_nenv Γ Ξ -> x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ -> x `in` dom Ξ.
Proof.
  intros Γ Ξ x A Ha2n Hbinds.
  induction Ha2n; eauto; destruct_binds; eauto.
  Unshelve. simpl in Hbinds. exfalso. eauto.
Qed.

Lemma awl_to_nenv_binds : forall Γ Ξ x A n,
  uniq Ξ -> awl_to_nenv Γ Ξ -> binds x (nbind_var_typ n) Ξ ->
  x ~ A ∈ᵃ ⌊ Γ ⌋ᵃ -> n_iuv_size A n.
Proof.
  intros Γ Ξ x A n Huniq Ha2n.
  generalize dependent n. generalize dependent A. generalize dependent x.
  dependent induction Ha2n; intros * Hbinds Hsize; simpl in *; eauto;
    try solve [exfalso; eauto]; try solve [destruct_binds; eauto].
  destruct_binds; eauto; dependent destruction Huniq.
  - exfalso. eauto.
  - exfalso. eapply H. eapply awl_to_nenv_dom'; eauto.
  - eapply IHHa2n; eauto.
Qed.

Lemma exp_size_total_a_wf_exp : forall Γ Ξ e n,
  ⊢ᵃʷ Γ ->
  a_wf_exp (awl_to_aenv Γ) e ->  
  awl_to_nenv Γ Ξ ->
  exists m, exp_size Ξ e n m.
Proof.
  intros. 
  eapply a_wf_exp_n_wf_exp with (Γ := Γ) in H0; eauto.
  eapply exp_size_total in H0; eauto.
  eapply awl_to_nenv_uniq; eauto.
Qed.

Hint Immediate a_wf_twl_a_wf_wwl : core.
Hint Immediate a_wf_wl_a_wf_wwl : core.

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
             }
             destruct He' as [m' He'].
             eapply exp_size_conts_le with (Ξ := Ξ) (m := m') in H6; eauto; try lia.
             eapply IHme with (ne := m0 + (m' + n)); auto.
             ++ repeat (constructor; simpl; auto).
                eapply a_wf_exp_weaken_etvar_twice. simpl. eauto.
                apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.
             ++ eapply exp_size_wl__cons_work with (m := m0) (n := m' + n)
                (Ξ := ((x, nbind_var_typ 0) :: Ξ)); eauto.
                constructor...
                eapply exp_size_wl__cons_work with (m := m')
                    (Ξ := Ξ); eauto.
             ++ lia. }
             ++ destruct Jg as [Jg | Jg].
                ** left. inst_cofinites_for a_wl_red__inf_abs_mono; intros.
                   apply rename_var_in_a_wf_wwl_a_wl_red with (x:=x) (y:=x0) in Jg; eauto.
                   simpl in Jg. destruct_eq_atom.
                   rewrite subst_exp_in_exp_open_exp_wrt_exp in Jg. 
                   simpl in Jg. destruct_eq_atom.
                   rewrite subst_exp_in_exp_fresh_eq in Jg; eauto.
                   rewrite subst_exp_in_conts_fresh_eq in Jg; eauto.
                   rewrite rename_var_in_aworklist_fresh_eq in Jg; eauto. 
                   apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X2) (Y:=X3) in Jg; simpl; eauto.
                   simpl in Jg. destruct_eq_atom.
                   rewrite subst_typ_in_exp_open_exp_wrt_exp in Jg.
                   simpl in Jg. rewrite subst_typ_in_exp_fresh_eq in Jg; eauto.
                   rewrite subst_typ_in_conts_fresh_eq in Jg; eauto.
                   rewrite rename_tvar_in_aworklist_fresh_eq in Jg; eauto.
                   apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X0) in Jg; simpl; eauto.
                   simpl in Jg. destruct_eq_atom.
                   rewrite subst_typ_in_exp_open_exp_wrt_exp in Jg.
                   simpl in Jg. rewrite subst_typ_in_exp_fresh_eq in Jg; eauto.
                   rewrite subst_typ_in_conts_fresh_eq in Jg; eauto.
                   rewrite rename_tvar_in_aworklist_fresh_eq in Jg; eauto.
                   auto.
                   --- repeat (constructor; simpl; auto). 
                       apply a_wf_exp_rename_var_cons with (y:=x0) in H0; eauto.
                       rewrite subst_exp_in_exp_open_exp_wrt_exp in H0; auto. simpl in H0. destruct_eq_atom.  
                       rewrite subst_exp_in_exp_fresh_eq in H0; eauto.
                       eapply a_wf_exp_weaken_etvar_twice; simpl; eauto.
                       apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.                     
                   --- repeat (constructor; simpl; auto). 
                       apply a_wf_exp_rename_var_cons with (y:=x0) in H0; eauto.
                       rewrite subst_exp_in_exp_open_exp_wrt_exp in H0; auto. simpl in H0. destruct_eq_atom.  
                       rewrite subst_exp_in_exp_fresh_eq in H0; eauto.
                       eapply a_wf_exp_weaken_etvar_twice; simpl; eauto.
                       apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.
                   --- rewrite fvar_in_wf_conts_upper; eauto. 
                   --- auto.
                   --- repeat (constructor; simpl; auto).
                       eapply a_wf_exp_weaken_etvar_twice; simpl; eauto.
                       apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.
                ** right. unfold not. intros Hcontra. dependent destruction Hcontra. rename H7 into Hcontra.
                   pick fresh x0. pick fresh X3. pick fresh X4.
                   inst_cofinites_with x0. inst_cofinites_with X3. inst_cofinites_with X4. 
                   apply rename_var_in_a_wf_wwl_a_wl_red with (x:=x0) (y:=x) in Hcontra; eauto.
                   simpl in Hcontra. destruct_eq_atom.
                   rewrite subst_exp_in_exp_open_exp_wrt_exp in Hcontra. 
                   simpl in Hcontra. destruct_eq_atom.
                   rewrite subst_exp_in_exp_fresh_eq in Hcontra; eauto.
                   rewrite subst_exp_in_conts_fresh_eq in Hcontra; eauto.
                   rewrite rename_var_in_aworklist_fresh_eq in Hcontra; eauto. 
                   apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X4) (Y:=X2) in Hcontra; simpl; eauto.
                   simpl in Hcontra. destruct_eq_atom.
                   rewrite subst_typ_in_exp_open_exp_wrt_exp in Hcontra.
                   simpl in Hcontra. rewrite subst_typ_in_exp_fresh_eq in Hcontra; eauto.
                   rewrite subst_typ_in_conts_fresh_eq in Hcontra; eauto.
                   rewrite rename_tvar_in_aworklist_fresh_eq in Hcontra; eauto.
                   apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X3) (Y:=X1) in Hcontra; simpl; eauto.
                   simpl in Hcontra. destruct_eq_atom.
                   rewrite subst_typ_in_exp_open_exp_wrt_exp in Hcontra.
                   simpl in Hcontra. rewrite subst_typ_in_exp_fresh_eq in Hcontra; eauto.
                   rewrite subst_typ_in_conts_fresh_eq in Hcontra; eauto.
                   rewrite rename_tvar_in_aworklist_fresh_eq in Hcontra; eauto.
                   auto.
                   --- repeat (constructor; simpl; auto). 
                       eapply a_wf_exp_weaken_etvar_twice; simpl; eauto.
                       apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.  
                   --- repeat (constructor; simpl; auto). 
                       eapply a_wf_exp_weaken_etvar_twice; simpl; eauto.
                       apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.  
                   --- rewrite fvar_in_wf_conts_upper; eauto. 
                   --- auto.
                   --- repeat (constructor; simpl; auto).
                       apply a_wf_exp_rename_var_cons with (y:=x0) in H0; eauto.
                       rewrite subst_exp_in_exp_open_exp_wrt_exp in H0; auto. simpl in H0. destruct_eq_atom.  
                       rewrite subst_exp_in_exp_fresh_eq in H0; eauto.
                       eapply a_wf_exp_weaken_etvar_twice; simpl; eauto.
                       apply a_wf_conts_weaken_cons. apply a_wf_conts_weaken_cons. auto.
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
           apply n_iuv_size_total in H8 as Hiuv.
           destruct Hiuv as [a' Hiuv].
           pick fresh X. inst_cofinites_with X (keep).
           assert (Jg: (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check (e ᵉ^^ₜ ` X) (A ᵗ^ₜ X) ⫤ᵃ X ~ᵃ □ ;ᵃ work_applys cs (typ_all A) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (Huniq': uniq Ξ).
             { eapply awl_to_nenv_uniq; eauto. } 
             eapply IHme; eauto; simpl; try lia.
             ++ dependent destruction H4. repeat (constructor; simpl; auto).
                 inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X0; auto.
                 dependent destruction H11; auto.
             ++ eapply exp_size_wl__cons_work; eauto.
             ++ lia. 
           }
           destruct Jg as [Jg | Jg].
           ++ left. inst_cofinites_for a_wl_red__inf_tabs; intros.
              apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X) (Y:=X0) in Jg; eauto.
              simpl in Jg. destruct_eq_atom.
              rewrite subst_typ_in_exp_open_exp_wrt_typ in Jg. 
              simpl in Jg. destruct_eq_atom.
              rewrite subst_typ_in_exp_fresh_eq in Jg; eauto.
              rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in Jg; eauto.
              rewrite subst_typ_in_conts_fresh_eq in Jg; eauto.
              rewrite subst_typ_in_typ_fresh_eq in Jg; eauto.
              rewrite rename_tvar_in_aworklist_fresh_eq in Jg; eauto.
              auto.
              ** dependent destruction H4. repeat (constructor; simpl; auto).
                 inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X1; auto.
                 dependent destruction H11; auto.
           ++ right. unfold not. intros Hcontra. dependent destruction Hcontra. rename H13 into Hcontra.
              pick fresh X0. inst_cofinites_with X0 (keep).
              clear Hcontra. rename H13 into Hcontra. 
              apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X0) (Y:=X) in Hcontra; eauto.
              simpl in Hcontra. destruct_eq_atom.
              rewrite subst_typ_in_exp_open_exp_wrt_typ in Hcontra. 
              simpl in Hcontra. destruct_eq_atom.
              rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in Hcontra; eauto.
              rewrite subst_typ_in_exp_fresh_eq in Hcontra; eauto.
              rewrite subst_typ_in_conts_fresh_eq in Hcontra; eauto.
              rewrite subst_typ_in_typ_fresh_eq in Hcontra; eauto.
              rewrite rename_tvar_in_aworklist_fresh_eq in Hcontra; eauto.
              auto.
              ** dependent destruction H11. repeat (constructor; simpl; auto).
                  inst_cofinites_for a_wf_typ__all; intros; inst_cofinites_with X1; auto.
                  dependent destruction H15; auto.
        -- dependent destruction H4. dependent destruction H6.
           assert (Jg: (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infer e (conts_inftapp A cs) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { assert (Huniq': uniq Ξ).
             { eapply awl_to_nenv_uniq; eauto. }
             assert (He': exists m, exp_size_conts Ξ cs ((2 + m1) * n0) m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
             destruct He' as [m' He'].
             eapply exp_size_conts_le with (m := m') in H8 as Hle; eauto; try lia.
             assert (He'': exists m, exp_size Ξ e 0 m).
             { eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto. }
             destruct He'' as [m'' He''].
             eapply exp_size_le with (m := m'') in H5 as Hle'; eauto; try lia.
             eapply IHme; eauto; simpl; try lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- dependent destruction H4. dependent destruction H6.
           unify_n_iuv_size.
           assert (Huniq' : uniq Ξ).
           { eapply awl_to_nenv_uniq; eauto. }
           assert (He': exists m, exp_size_conts Ξ cs m1 m).
           { eapply exp_size_conts_total; eauto.
             eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.
          }
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
          }
          destruct Hes as [s Hes].
          assert (He': exists m, exp_size Ξ e 0 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He' as [m' He'].
          eapply exp_size_le with (m' := m) in He' as Hle; eauto; try lia.
          eapply IHmj; eauto; simpl; try lia. }
        assert (Jg1: forall A1 A2, A = typ_union A1 A2 ->
                       (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { intros A1 A2 Heq. subst.
          dependent destruction H0. dependent destruction H3.
          assert (He1: exists m, exp_size Ξ e n1 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He1 as [m1 He1].
          assert (He2: exists m, exp_size Ξ e n2 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He2 as [m2 He2].
          eapply exp_size_split with (n := 2 + n1 + n2) in He1 as Hle'; eauto; try lia.
          eapply IHme; eauto; simpl; try lia. }
        assert (Jg2: forall A1 A2, A = typ_union A1 A2 ->
                       (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (work_check e A2 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { intros A1 A2 Heq. subst.
          dependent destruction H0. dependent destruction H3.
          assert (He1: exists m, exp_size Ξ e n1 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He1 as [m1 He1].
          assert (He2: exists m, exp_size Ξ e n2 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He2 as [m2 He2].
          eapply exp_size_split with (n := 2 + n1 + n2) in He1 as Hle'; eauto; try lia.
          eapply IHme; eauto; simpl; try lia. }
        assert (Jg': forall A1 A2, A = typ_intersection A1 A2 ->
                       (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_check e A2 ⫤ᵃ work_check e A1 ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ ).
        { intros A1 A2 Heq. subst.
          dependent destruction H0. dependent destruction H3.
          assert (He1: exists m, exp_size Ξ e n1 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He1 as [m1 He1].
          assert (He2: exists m, exp_size Ξ e n2 m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
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
                { eapply exp_size_total_a_wf_exp with (Γ := x ~ᵃ typ_top;ᵃ Γ ) ; eauto.
                  simpl. eapply a_wf_exp_var_binds_another with (Σ2 := nil); simpl; eauto. }
                destruct He' as [m' He'].
                eapply exp_size_le with (Ξ' := (x, nbind_var_typ n0) :: Ξ) (m' := m) in He' as Hle; eauto; try lia.
                eapply IHme; eauto; simpl; try lia.
                constructor; auto. constructor; auto. constructor; auto.
                apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
                eapply exp_size_wl__cons_work with (Ξ := ((x, nbind_var_typ 0) :: Ξ)); eauto. lia.
                eapply le_nenv_cons; eauto. lia. }
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
           ++ remember (dom Ξ). pick fresh x.
              pick fresh X1. pick fresh X2. subst.
              dependent destruction H4. simpl in *.
              assert (Hsubst: exists Γ1 Γ2, aworklist_subst (work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X (typ_arrow ` X1 ` X2) Γ1 Γ2).
              { assert (Hsubst': exists Γ1 Γ2, aworklist_subst (X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) X 
              (typ_arrow ` X1 ` X2) Γ1 Γ2).
                { eapply worklist_subst_fresh_etvar_total'; eauto. }
                destruct Hsubst' as [Γ1 [Γ2 Hsubst']]. eauto. }
              destruct Hsubst as [Γ1 [Γ2 Hsubst]].
              assert (He': exp_size_wl (work_check (e ᵉ^^ₑ exp_var_f x) ` X2 ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ) (m + n)).
              { eapply exp_size_wl__cons_work; eauto.
                eapply awl_to_nenv__cons_var; eauto. }
              assert (He'': exists k, exp_size_wl ({typ_arrow ` X1 ` X2 ᵃʷ/ₜ X} Γ2 ⧺ Γ1) k).
              { eapply exp_size_wl_total; eauto.
                eapply aworklist_subst_wf_wwl with (Γ := (work_check (e ᵉ^^ₑ exp_var_f x) ` X2
                ⫤ᵃ x ~ᵃ ` X1;ᵃ X2 ~ᵃ ⬒ ;ᵃ X1 ~ᵃ ⬒ ;ᵃ Γ)); eauto.
                admit.
                simpl. econstructor; eauto.
              }
              destruct He'' as [k He''].
              eapply exp_size_wl_aworklist_subst' in He'; simpl; eauto. subst.
              assert (Jge: ({typ_arrow ` X1 ` X2 ᵃʷ/ₜ X} Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅ \/
                         ~ ({typ_arrow ` X1 ` X2 ᵃʷ/ₜ X} Γ2 ⧺ Γ1) ⟶ᵃʷ⁎⋅).
              { eapply IHme with (ne := m + n); eauto; simpl; try lia. admit. (* wf *) }
              admit. (* rename *)
              admit.
              econstructor; eauto.
           ++ remember (dom Ξ). pick fresh x. subst. inst_cofinites_with x.
              dependent destruction H4.
              assert (JgArr: (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ 
                           ~ (work_check (e ᵉ^^ₑ exp_var_f x) A2 ⫤ᵃ x ~ᵃ A1;ᵃ Γ) ⟶ᵃʷ⁎⋅).
              { assert (He': exists m, exp_size ((x, nbind_var_typ n1) :: Ξ) (e ᵉ^^ₑ exp_var_f x) n2 m).
                { eapply exp_size_total_a_wf_exp with (Γ := x ~ᵃ A1;ᵃ Γ); eauto.
                  simpl. eapply a_wf_exp_var_binds_another with (Σ2 := nil); simpl; eauto. }
                destruct He' as [m' He'].
                eapply exp_size_le with (Ξ' := (x, nbind_var_typ (n1 + n2)) :: Ξ) (m' := m) in He' as Hle; eauto; try lia.
                eapply IHme; eauto; simpl; try lia.
                constructor; auto. constructor; auto. constructor; auto.
                apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
                simpl. eapply a_wf_typ_weaken_cons; eauto.
                eapply exp_size_wl__cons_work with (Ξ := ((x, nbind_var_typ n1) :: Ξ)); eauto.
                lia.
                eapply le_nenv_cons; eauto. lia. }
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
                     repeat (constructor; auto). simpl. apply a_wf_exp_var_binds_another with (Σ2 := nil) (A1 := T); simpl; auto.
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
        -- destruct (apply_contd_total cd A1 A2) as [w Happly].
          assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
          { eapply a_wf_wl_apply_contd in Happly as Hwf'; eauto.
            eapply a_wf_work_apply_contd in Happly as Hwf''; eauto.
            assert (He': exists m, exp_size_work Ξ w m).
            { eapply exp_size_work_total; eauto.
              eapply a_wf_work_n_wf_work with (Γ := Γ); eauto. }
            destruct He' as [m' He'].
            dependent destruction H4.
            assert (He'': exists m1 m2, exp_size_contd Ξ cd n1 n2 m1 m2).
            { eapply exp_size_contd_total; eauto.
              eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto. }
            destruct He'' as [m1' [m2' He'']].
            eapply exp_size_contd_le with (Ξ := Ξ) (n1 := n1) (n2 := n2) (m1 := m1') (m2 := m2') in H5 as Hle; auto; try lia.
            eapply apply_contd_exp_size with (n1 := m1') (n2 := m2') in Happly as ?; eauto. subst.
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
           { assert (Heq: infabs_depth (open_typ_wrt_typ A (typ_var_f X)) = infabs_depth A) by apply infabs_depth_open_tvar. 
             assert (He': exists m1 m2, exp_size_contd Ξ cd n0 n0 m1 m2).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto. }
             destruct He' as [m1' [m2' He']].
             eapply exp_size_contd_le with (m1 := m1') (m2 := m2') in H6; eauto; try lia.
             eapply IHma with (ne := m1' + m2' + n); eauto; simpl in *; try lia.
             constructor; simpl; auto. constructor; simpl; auto. constructor; simpl; auto.
             eapply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl. auto.
             eapply a_wf_contd_weaken_cons; auto. }
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
                repeat (constructor; simpl; auto).
                --- apply a_wf_typ_tvar_etvar_cons.
                    erewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2; eauto.
                    apply a_wf_typ_rename_tvar_cons; eauto.
                --- apply a_wf_contd_weaken_cons; eauto.
        -- assert (Jg: (work_infabs A1 (contd_infabsunion A2 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                     ~ (work_infabs A1 (contd_infabsunion A2 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { dependent destruction H4.
             assert (He': exists m1 m2, exp_size_contd Ξ cd (2 + n1 + n2) (2 + n1 + n2) m1 m2).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto. }
             destruct He' as [m1' [m2' He']].
              eapply exp_size_contd_le with (m1 := m1') (m2 := m2') in H5; eauto; try lia.
             eapply IHma; eauto; simpl in *; try lia. }
           destruct Jg as [Jg | Jg]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg; auto.
        -- assert (Jg1: (work_infabs A1 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                      ~ (work_infabs A1 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { dependent destruction H4.
             assert (He': exists m1 m2, exp_size_contd Ξ cd n1 n1 m1 m2).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto. }
             destruct He' as [m1' [m2' He']].
             eapply exp_size_contd_le with (m1 := m1') (m2 := m2') in H5; eauto; try lia.
             eapply IHma; eauto; simpl in *; try lia. }
           assert (Jg2: (work_infabs A2 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                      ~ (work_infabs A2 cd ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { dependent destruction H4.
             assert (He': exists m1 m2, exp_size_contd Ξ cd n2 n2 m1 m2).
             { eapply exp_size_contd_total; eauto.
               eapply a_wf_contd_n_wf_contd with (Γ := Γ); eauto. }
             destruct He' as [m1' [m2' He']].
             eapply exp_size_contd_le with (m1 := m1') (m2 := m2') in H5; eauto; try lia.
             eapply IHma; eauto; simpl in *; try lia. } 
           destruct Jg1 as [Jg1 | Jg1]; eauto.
           destruct Jg2 as [Jg2 | Jg2]; eauto.
           right. intro Hcontra.
           dependent destruction Hcontra.
           apply Jg1; auto. apply Jg2; auto.
      * dependent destruction H4. simpl in *. dependent destruction H.
        assert (Jg:  (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                   ~ (work_infabs A2 (contd_unioninfabs A1 B1 cd) ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHmaj; eauto; simpl in *; try lia. constructor; auto. }
        destruct Jg as [Jg | Jg]; eauto.
        right. intro Hcontra. 
        dependent destruction Hcontra. eauto.
      * dependent destruction H4. simpl in *.
        assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H.
        assert (Jg:  (work_check e A ⫤ᵃ work_applys cs B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                  ~ (work_check e A ⫤ᵃ work_applys cs B ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { assert (He': exists m, exp_size Ξ e a m) by (eapply exp_size_total_a_wf_exp with (Γ := Γ); eauto).
          destruct He' as [m' He'].
          assert (He'': exists m, exp_size_conts Ξ cs b m).
          { eapply exp_size_conts_total; eauto.
            eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
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
        -- destruct (apply_conts_total cs typ_bot) as [w Happly].
           assert (Jg: a_wl_red (aworklist_cons_work Γ w) \/
                     ~ a_wl_red (aworklist_cons_work Γ w)).
           { eapply a_wf_work_apply_conts in Happly as Hwf'; eauto.
             assert (He': exists m, exp_size_work Ξ w m).
             { eapply exp_size_work_total; eauto.
               eapply a_wf_work_n_wf_work with (Γ := Γ); eauto. }
             destruct He' as [m' He'].
             assert (He'': exists m, exp_size_conts Ξ cs n1 m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
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
        -- destruct (apply_conts_total cs (open_typ_wrt_typ A A2)) as [w Happly].
           assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
           { eapply a_wf_work_apply_conts in Happly as Hwf'; eauto.
             2: { eapply a_wf_typ_all_open; eauto. }
             assert (He': exists m, exp_size_work Ξ w m).
             { eapply exp_size_work_total; eauto.
               eapply a_wf_work_n_wf_work with (Γ := Γ); eauto. }
             destruct He' as [m' He'].
             assert (He'': exists n, n_iuv_size (A ᵗ^^ₜ A2) n).
             { eapply n_iuv_size_total; eauto.
               eapply a_wf_typ_lc; eauto.
               eapply a_wf_typ_all_open; eauto. }
             destruct He'' as [n' He''].
             assert (He''': exists m, exp_size_conts Ξ cs n' m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
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
            assert (He': exists m, exp_size_conts Ξ cs (2 + n3 * (2 + n2) + (2 + n2) * n1) m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
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
           { assert (He': exists m, exp_size_conts Ξ cs ((2 + n2) * n1) m).
             { eapply exp_size_conts_total; eauto.
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
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
               eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto.  }
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
          assert (He': exists m, exp_size_conts Ξ cs (2 + n1 + (2 + n0) * n2) m).
          { eapply exp_size_conts_total; eauto.
            eapply a_wf_conts_n_wf_conts with (Γ := Γ); eauto. }
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
        destruct (apply_conts_total cs (typ_union A1 A2)) as [w Happly].
        assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply a_wf_work_apply_conts in Happly as Hwf'; eauto.
          assert (He': exists n, exp_size_work Ξ w n).
          { eapply exp_size_work_total; eauto.
            eapply a_wf_work_n_wf_work with (Γ := Γ); eauto. }
          destruct He' as [n' He'].
          eapply apply_conts_exp_size with (n := m) in Happly as Hle; eauto. subst.
          eapply IHmtj; eauto; simpl in *; try lia.
          eapply a_wf_wl_apply_conts; eauto.
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
      * assert (Huniq' : uniq Ξ).
         { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H4. simpl in *. dependent destruction H;
          try solve [right; intro Hcontra; dependent destruction Hcontra];
        dependent destruction H1;
          try solve [right; intro Hcontra; dependent destruction Hcontra].
        destruct (apply_contd_total cd ( (typ_intersection A1 A2) )   ( (typ_union B1 B2) ) ) as [w Happly];
        try solve [right; intro Hcontra; dependent destruction Hcontra; dependent destruction Hcontra;
          eapply Happly; eauto].
        assert (Jg: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply a_wf_wl_apply_contd with (Γ := Γ) in Happly as Hwf'; eauto.
          2 : { constructor; auto. }
          eapply a_wf_work_apply_contd in Happly as Hwf''; eauto.
          assert (He': exists n, exp_size_work Ξ w n).
          { eapply exp_size_work_total; eauto.
            eapply a_wf_work_n_wf_work with (Γ := Γ); eauto. }
          destruct He' as [n' He'].
          eapply IHmaj; eauto; simpl in *; try lia.
          eapply apply_contd_exp_size in Happly; eauto. lia.
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
      * assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H3. simpl in *.
        destruct (apply_conts_total cs A) as [w Happly].
        eapply a_wf_wl_apply_conts in Happly as Hwf'; eauto.
        eapply a_wf_work_apply_conts in Happly as Hwf''; eauto.
        assert (He': exists n, exp_size_work Ξ w n).
        { eapply exp_size_work_total; eauto.
          eapply a_wf_work_n_wf_work with (Γ := Γ); eauto. }
        destruct He' as [n' He'].
        assert (JgApply: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { 
          eapply IHmj; eauto; simpl in *; try lia.
          eapply apply_conts_exp_size in Happly; eauto. lia.
          eapply apply_conts_judge_size in Happly; lia. }
        destruct JgApply as [JgApply | JgApply]; eauto.
        right. intro Hcontra. dependent destruction Hcontra.
        eapply apply_conts_det in Happly; eauto. subst. eapply JgApply; eauto.
      * assert (Huniq' : uniq Ξ).
        { eapply awl_to_nenv_uniq; eauto. }
        dependent destruction H4. simpl in *.
        destruct (apply_contd_total cd A B) as [w Happly].
        eapply a_wf_wl_apply_contd with (Γ := Γ) in Happly as Hwf'; eauto.
        eapply a_wf_work_apply_contd in Happly as Hwf''; eauto.
        assert (He': exists n, exp_size_work Ξ w n).
        { eapply exp_size_work_total; eauto.
          eapply a_wf_work_n_wf_work with (Γ := Γ); eauto.  }
        destruct He' as [n' He'].
        assert (JgApply: (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅ \/ ~ (w ⫤ᵃ Γ) ⟶ᵃʷ⁎⋅).
        { eapply IHmj; eauto; simpl in *; try lia.
          eapply apply_contd_exp_size in Happly; eauto; lia.
          eapply apply_contd_judge_size in Happly; lia. }
        destruct JgApply as [JgApply | JgApply]; eauto.
        right. intro Hcontra. dependent destruction Hcontra.
        eapply apply_contd_det in Happly; eauto. subst. eapply JgApply; eauto.
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
      dependent destruction H0. apply a_wf_wl__conswork_sub; auto. }
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
    dependent destruction H2. dependent destruction H.
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
    * assert (Γ ⟶ᵃʷ⁎⋅ \/ ~ Γ ⟶ᵃʷ⁎⋅). { eapply IHmw; eauto. lia. lia. }
      dependent destruction H;
      dependent destruction H0;
        try solve [right; intro Hcontra;
          dependent destruction Hcontra];
        try solve [destruct Jg as [Jg | Jg]; eauto;
          right; intro Hcontra; dependent destruction Hcontra;
          eapply Jg; eauto];
        destruct Jg as [Jg | Jg]; eauto;
        try solve [right; intro Hcontra; dependent destruction Hcontra;
          eapply Jg; eauto; dependent destruction H1].
      -- right. unfold not. intros. dependent destruction H2; auto. dependent destruction H3.
      -- right. unfold not. intros. dependent destruction H2; auto. dependent destruction H3.
      -- right. unfold not. intros. dependent destruction H2; auto. dependent destruction H3.
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
      -- right. intro Hcontra. dependent destruction Hcontra. dependent destruction H2.
      -- right. intro Hcontra. dependent destruction Hcontra. dependent destruction H2.
      -- right. intro Hcontra. dependent destruction Hcontra. dependent destruction H2.
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
         dependent destruction H3; try unify_binds.
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
         dependent destruction H2.
      -- destruct Jg as [Jg | Jg]; eauto.
         right; intro Hcontra; dependent destruction Hcontra; try unify_binds; eauto.
         dependent destruction H2.
      -- destruct (eq_dec X X0) as [Heq | Hneq]; subst; try unify_binds. 
         destruct (a_wf_wl_aworklist_subst_dec Γ X (` X0)) as [[Γ1 [Γ2 Hsubst]] | Hsubst]; eauto.
         ++ edestruct JgInst1 as [JgInst1' | JgInst1']; eauto.
            right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
            assert (Heq: Γ1 = Γ3 /\ Γ2 = Γ4).
            { eapply aworklist_subst_det; eauto. }
            destruct Heq as [Heq1 Heq2]. subst. eauto.
         ++ right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
      -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H3; try unify_binds.
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
      -- destruct (a_mono_typ_dec Γ (typ_arrow A1 A2)); auto. 
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
              admit. 
              admit. admit. admit. admit. admit. admit. admit.
            }          
            admit. (* TODO: renaming stuff *)
      -- right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H4; try unify_binds.
      -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
         edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
         right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H2. 
         eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         right. intro Hcontra. dependent destruction Hcontra; try unify_binds.
         dependent destruction H2. eauto.
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
            admit. simpl in *. lia. }
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X1); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               simpl. auto.
            ** dependent destruction H4.
      -- pick fresh X1. inst_cofinites_with X1.
         right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H4].
         dependent destruction H3. unify_binds. unify_binds. 
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
         ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H4].
            pick fresh X1'. inst_cofinites_with X1'.
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1') (Y:=X1) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
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
            apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H3; auto.
            ** simpl in H3. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H3; auto.
               rewrite subst_typ_in_typ_fresh_eq in H3; auto.
               rewrite subst_typ_in_typ_fresh_eq in H3; auto.
            ** apply a_wf_wl_a_wf_wwl.
               apply a_wf_wl__conswork_sub; auto. simpl.
               apply a_wf_typ_tvar_etvar with (Σ2 := nil). simpl.
               rewrite <- subst_typ_in_typ_open_typ_wrt_typ_tvar2 with (X := X); auto.
               apply a_wf_typ_rename_tvar_cons; auto.
               apply a_wf_typ_weaken_cons; auto.
      --  pick fresh X. inst_cofinites_with X.
          assert (JgAll: (work_sub (A ᵗ^ₜ X) (A0 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ⟶ᵃʷ⁎⋅ \/
                       ~ (work_sub (A ᵗ^ₜ X) (A0 ᵗ^ₜ X) ⫤ᵃ X ~ᵃ ■ ;ᵃ Γ) ⟶ᵃʷ⁎⋅).
          { eapply IHmw; eauto; simpl in *; try lia; simpl.
            eapply a_wf_wl__conswork_sub; auto; simpl. 
            apply a_wf_typ_tvar_stvar_cons; auto.
            apply a_wf_typ_tvar_stvar_cons; auto.
            econstructor; eauto. econstructor; eauto.
            admit. simpl in *. admit. }
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
          ++ right. intro Hcontra. dependent destruction Hcontra; try solve [dependent destruction H4].
             pick fresh X1. inst_cofinites_with X1.
             apply rename_tvar_in_a_wf_wwl_a_wl_red with (X:=X1) (Y:=X) in H4; auto.
            ** simpl in H4. destruct_eq_atom.
               rewrite rename_tvar_in_aworklist_fresh_eq in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
               rewrite subst_typ_in_typ_open_typ_wrt_typ_tvar2 in H4; auto.
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
           apply a_wf_wl__conswork_sub; auto. simpl.
           apply a_wf_typ_tvar_etvar_cons; auto.
           apply a_wf_typ_weaken_cons; auto.
           econstructor; econstructor; eauto.
            admit. admit. }
         admit.
      -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
         admit.
  * dependent destruction H1;
      try solve [edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto;
                  right; intro Hcontra; dependent destruction Hcontra;
                  eapply JgUnion3'; eauto; try dependent destruction H3].
    -- edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       dependent destruction H4. auto.
    -- edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       dependent destruction H4. auto.
    -- edestruct JgUnion3 as [JgUnion3' | JgUnion3']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       dependent destruction H4. auto.
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
    -- right. unfold not. intros. dependent destruction H3; auto. dependent destruction H4.
    -- right. unfold not. intros. dependent destruction H3; auto. dependent destruction H4.    
    -- right. unfold not. intros. dependent destruction H3; auto. dependent destruction H4.
    -- edestruct JgUnion1 as [JgUnion1' | JgUnion1']; eauto.
       edestruct JgUnion2 as [JgUnion2' | JgUnion2']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       eapply JgInter2'; eauto. eapply JgInter3'; eauto.
       eapply JgUnion1'; eauto. eapply JgUnion2'; eauto.
    -- edestruct JgInter1 as [JgInter1' | JgInter1']; eauto.
       right. intro Hcontra. dependent destruction Hcontra.
       eapply JgInter1'; eauto. eapply JgInter2'; eauto. eapply JgInter3'; eauto.
    Unshelve. all: auto.
Admitted.
