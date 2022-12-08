(* Require Import Metalib.Metatheory.

Require Import algo.ott.
Require Import decl.ott.


Inductive ss_entry := 
  | sse_tv 
  | sse_ev (t : ld_type).

Definition subst_set := list (var * ss_entry).

Declare Scope subst_set_scope.
Delimit Scope subst_set_scope with subst.
Bind Scope subst_set_scope with subst_set.

Check binds.

Notation "s1 ;; s2" := (app s2 s1)
  (at level 58, left associativity) : subst_set_scope.

Notation "s ; x : t" := (cons (pair x (sse_ev t)) s)
  ( at level 58, x at level 0, t at level 52, left associativity) : subst_set_scope.

Notation "x : A ∈ s" := (binds x A s)
   (at level 65, A at level 52, no associativity) : type_scope.

Inductive wf_ss : subst_set -> Prop :=
  | wf_ss_nil : wf_ss nil
  | wf_ss_ex : forall x t Θ
    , wf_ss Θ -> x `notin` dom Θ -> ld_mono_type t
    -> wf_ss (Θ; x : t)
.

Lemma wf_uniq : forall Θ,
    wf_ss Θ -> uniq Θ.
Proof.
  induction 1; eauto.
Qed.


Inductive inst_type : subst_set -> la_type -> ld_type -> Prop := 
  | inst_t_tvar : forall θ x, wf_ss θ -> inst_type θ (la_t_tvar_f x) (ld_t_var_f x)
  | inst_t_evar : forall θ x t, wf_ss θ -> x : t ∈ θ -> inst_type θ (la_t_evar x) t
  | inst_t_int : forall θ, wf_ss θ -> inst_type θ la_t_int ld_t_int
  | inst_t_arrow : forall θ A' B' A B, 
      inst_type θ A' A -> inst_type θ B' B ->
      inst_type θ (la_t_arrow A' B') (ld_t_arrow A B)
  | inst_t_forall : forall θ L A' A,
      (forall x, x `notin` L -> 
      inst_type θ (open_la_type_wrt_la_type A' (la_t_tvar_f x)) (open_ld_type_wrt_ld_type A (ld_t_var_f x))) ->
      inst_type θ (la_t_forall A') (ld_t_forall A)
.

Lemma inst_t_wf_ss : forall θ t t',
    inst_type θ t t' -> wf_ss θ.
Proof.
  induction 1; pick fresh x'; eauto.
Qed.


Inductive inst_ev : subst_set -> var -> la_typelist -> la_typelist -> ld_worklist -> Prop :=
  | inst_ev_nil : forall θ x, inst_ev θ x la_tl_nil la_tl_nil ld_wl_nil
  | inst_ev_lbs : forall θ x lb lbs wl ubs lb' t', inst_ev θ x lbs ubs wl -> 
      inst_type θ lb lb' -> inst_type θ (la_t_evar x) t' -> inst_ev θ x (la_tl_cons lbs lb) ubs (ld_wl_cons_w wl (ld_w_sub lb' t'))
  | inst_ev_ubs : forall θ x lbs wl ub ubs ub' t', inst_ev θ x lbs ubs wl -> 
      inst_type θ ub ub' -> inst_type θ (la_t_evar x) t' -> inst_ev θ x lbs (la_tl_cons ubs ub) (ld_wl_cons_w wl (ld_w_sub t' ub'))
.


(* Lemma split : theta |- awl --> dwl -| theta1 -> exists theta0,  theta |- awl  *)

Inductive inst_worklist : subst_set -> la_worklist -> ld_worklist -> subst_set -> Prop := 
  | inst_wl_nil : forall θ, 
      wf_ss θ -> inst_worklist θ la_wl_nil ld_wl_nil θ
  | inst_wl_sub : forall θ θ' awl dwl t1 t2 t1' t2', 
      inst_worklist θ awl dwl θ' -> 
      inst_type θ' t1 t1' -> 
      inst_type θ' t2 t2' -> 
      inst_worklist θ (la_wl_cons_w awl (la_w_sub t1 t2)) (ld_wl_cons_w dwl (ld_w_sub t1' t2')) θ'
  | inst_wl_tv : forall θ θ' x awl dwl, 
      inst_worklist θ awl dwl θ' -> 
      inst_worklist θ (la_wl_cons_tv awl x) (ld_wl_cons_tv dwl x) θ'
  | inst_wl_ev : forall θ θ' t lbs ex ubs awl dwl' dwl, 
      inst_worklist θ awl dwl θ' -> 
      ld_mono_type t -> 
      ex `notin` dom θ' -> 
      inst_ev (θ' ; ex : t) ex lbs ubs dwl' -> 
      inst_worklist θ (la_wl_cons_ev awl lbs ex ubs) (ld_wl_app dwl dwl')  (θ' ; ex : t)
.


Definition transfer' (Γ : la_worklist) (Γ' : ld_worklist) : Prop :=
  exists θ', inst_worklist nil Γ Γ' θ'. *)