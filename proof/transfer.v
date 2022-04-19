Require Import Metalib.Metatheory.
Require Import Metalib.Metatheory.

Require Import algo_new.ott.
Require Import decl.ott.


Definition subst_set := list (var * ld_type).

Declare Scope subst_set_scope.
Delimit Scope subst_set_scope with subst.
Bind Scope subst_set_scope with subst_set.

Notation "s1 ;; s2" := (app s2 s1)
  (at level 58, left associativity) : subst_set_scope.

Notation "s ; x t" := (cons (pair x t) s)
  ( at level 58, x at level 0, t at level 52, left associativity) : subst_set_scope.

Notation "x : A ∈ s" := (binds x A s)
   (at level 65, A at level 52, no associativity) : type_scope.


Inductive wf_ss : subst_set -> Prop :=
| wf_ss_nil : wf_ss nil.


Inductive inst_type : subst_set -> la_type -> ld_type -> Prop := 
| inst_t_tvar : forall θ x, wf_ss θ -> inst_type θ (la_t_tvar_f x) (ld_t_var_f x)
| inst_t_evar : forall θ x A, wf_ss θ -> x : A ∈ θ -> inst_type θ (la_t_evar x) A
| inst_t_int : forall θ, wf_ss θ -> inst_type θ la_t_int ld_t_int
| inst_t_arrow : forall θ A' B' A B, 
    inst_type θ A' A -> inst_type θ B' B ->
    inst_type θ (la_t_arrow A' B') (ld_t_arrow A B)
| inst_t_forall : forall θ L A' A,
    (forall x, x `notin` L -> 
    inst_type θ (open_la_type_wrt_la_type A' (la_t_tvar_f x)) (open_ld_type_wrt_ld_type A (ld_t_var_f x))) ->
    inst_type θ (la_t_forall A') (ld_t_forall A)
.

Inductive inst_ex : subst_set -> var -> la_typelist -> la_typelist -> ld_worklist -> Prop :=
  | inst_ex_nil : forall θ x, inst_ex θ x la_tl_nil la_tl_nil ld_wl_nil
  | inst_ex_lbs : forall θ x lb lbs wl ubs lb' t', inst_ex θ x lbs ubs wl -> 
      inst_type θ lb lb' -> inst_type θ (la_t_evar x) t' -> inst_ex θ x (la_tl_cons lbs lb) ubs (ld_wl_cons wl (ld_w_sub lb' t'))
  | inst_ex_ubs : forall θ x lbs wl ub ubs ub' t', inst_ex θ x lbs ubs wl -> 
      inst_type θ ub ub' -> inst_type θ (la_t_evar x) t' -> inst_ex θ x lbs (la_tl_cons ubs ub) (ld_wl_cons wl (ld_w_sub t' ub'))
.

Inductive inst_work : subst_set -> la_work -> ld_worklist -> Prop := 
| inst_w_sub : forall θ t1 t2 t1' t2', 
  inst_type θ t1 t1' -> inst_type θ t2 t2' -> inst_work θ (la_w_sub t1 t2) (ld_wl_cons ld_wl_nil (ld_w_sub t1' t2'))
| inst_w_ex : forall θ ex lbs ubs wl, inst_ex θ ex lbs ubs wl -> inst_work θ (la_w_evar lbs ex ubs) wl.


Inductive inst_worklist : subst_set -> la_worklist -> ld_worklist -> subst_set -> Prop := 
| inst_wl_nil  : forall Θ, wf_ss Θ -> inst_worklist Θ la_wl_nil ld_wl_nil Θ
| inst_wl_tvar : forall θ θ' x awl dwl, inst_worklist θ awl dwl θ' -> inst_worklist θ (la_wl_cons_tv awl x) (ld_wl_bind dwl x) θ'
| inst_wl_w : forall θ θ' aw awl dwl' dwl, inst_worklist θ awl dwl θ' -> inst_work θ' aw dwl' -> inst_worklist θ (la_wl_cons_w awl aw) (ld_wl_app dwl dwl') θ
.