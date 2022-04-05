Require Import Metalib.Metatheory.
Require Import Metalib.Metatheory.

Require Import algo.ott.
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

(* Inductive la_type : Set := 
 | la_t_int : la_type
 | la_t_forall (t:la_type)
 | la_t_var_b (_:nat)
 | la_t_var_f (x5:x)
 | la_t_tvar (tx5:tx)
 | la_t_evar (ex5:ex). *)

Inductive inst_type : subst_set -> la_type -> ld_type -> Prop := 
| inst_tx : forall θ x, wf_ss θ -> inst_type θ (la_t_tvar x) (ld_t_var_f x)
| inst_ex : forall θ x A, wf_ss θ -> x : A ∈ θ -> inst_type θ (la_t_evar x) A
| inst_int : forall θ, wf_ss θ -> inst_type θ la_t_int ld_t_int
| inst_arrow : forall θ A' B' A B, 
    inst_type θ A' A -> inst_type θ B' B ->
    inst_type θ (la_t_arrow A' B') (ld_t_arrow A B)
| inst_forall : forall θ L A' A,
    (forall x, x `notin` L -> 
    inst_type θ (open_la_type_wrt_la_type A' (la_t_var_f x)) (open_ld_type_wrt_ld_type A (ld_t_var_f x))) ->
    inst_type θ (la_t_forall A') (ld_t_forall A)
.

Inductive inst_work : subst_set -> la_work -> list ld_work -> subst_set -> Prop := True.