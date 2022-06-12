Require Export Coq.Unicode.Utf8.

Require Export decl_new.ott.
Require Export decl_new.ln_inf.

Notation "⊢ G" :=
  (ld_wf_context G)
    (at level 65, no associativity) : ld_type_scope.

Notation "G ⊢ t" :=
  (ld_wf_type G t)
    (at level 65, t at level 50, no associativity) : ld_type_scope.

Notation "G ⊢ t1 <: t2" :=
  (ld_sub G t1 t2)
    (at level 65, t1 at level 50, t2 at level 50, no associativity) : ld_type_scope.

Notation "x ∈ G" := (ld_in_context x G)
  (at level 65, no associativity) : type_ld_type_scopescope.

Notation "` x" := (ld_t_var_f x)
  (at level 0, x at level 0, no associativity) : ld_type_scope.
Notation "↑ n" := (ld_t_var_b n)
  (at level 0, n at level 0, no associativity) : ld_type_scope.

(* Notation "e < n > ^^' e' " := (open_ld_type_wrt_ld_type_rec n e' e)
  (at level 40, n at level 0, left associativity) : dk_type_scope.
 *)
Notation "[ t' /_ x ] t" :=
  (subst_ld_type t' x t)
    ( at level 49, t' at level 50, x at level 0
    , right associativity) : ld_type_scope.

Notation "t ^` x" := (open_ld_type_wrt_ld_type t (ld_t_var_f x))
  (at level 48, left associativity) : ld_type_scope.

Notation "t1 ^^ t2" := (open_ld_type_wrt_ld_type t1 t2)
  (at level 48, left associativity) : ld_type_scope.


Declare Scope ld_context_scope.
Delimit Scope ld_context_scope with ld_context.
Bind Scope ld_context_scope with ld_context.

Notation "G , x" :=
  (ld_ctx_cons G x)
    (at level 58, x at level 0, left associativity) : ld_context_scope.

Reserved Notation "G1 ,, G2"
  (at level 58, left associativity).

Fixpoint ld_ctx_app (G1 G2 : ld_context) : ld_context :=
  match G2 with
  | ld_ctx_nil => G1
  | G2', x => G1 ,, G2' , x
  end%ld_context

where "G1 ,, G2" := (ld_ctx_app G1 G2) : ld_context_scope.


Open Scope ld_type_scope.
Open Scope ld_context_scope.