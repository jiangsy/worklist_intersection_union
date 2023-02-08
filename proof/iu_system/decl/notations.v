Require Export Coq.Unicode.Utf8.

Require Export decl.ott.
Require Export decl.ln_inf.

Notation "⊢ E" :=
  (dwf_env E)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ T" :=
  (dwf_typ E T)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ S <: T" :=
  (dsub E S T)
    (at level 65, S at next level, no associativity) : type_scope.

Notation "E ⊢ e <= T" :=
    (d_check E e T) 
      (at level 65, e at next level, no associativity) : 
      type_scope.

Notation "X ∈ E" := (binds X (dbind_tvar_empty))
  (at level 65, no associativity) : type_scope.

Notation "~ X ∈ E" := (binds X (dbind_stvar_empty))
  (at level 65, no associativity) : type_scope.


Notation "`ᵈ X" := (dtyp_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.
Notation "↑ n" := (dtyp_var_b n)
  (at level 0, n at level 0, no associativity) : type_scope.

Notation "[ T' /ᵈ X ] T" :=
  (dsubst_tv_in_dtyp T' X T)
    ( at level 49, T' at level 50, X at level 0
    , right associativity) : type_scope.

Notation "T ^ᵈ X" := (open_dtyp_wrt_dtyp T (dtyp_var_f X))
  (at level 48, left associativity) : type_scope.

Notation "T1 ^^ᵈ T2" := (open_dtyp_wrt_dtyp T1 T2)
  (at level 48, left associativity) : type_scope.


(* Declare Scope decl_context_scope.
Delimit Scope decl_context_scope with decl_context.
Bind Scope decl_context_scope with decl_context.

Notation "G , x" :=
  (decl_ctx_cons G x)
    (at level 58, x at level 0, left associativity) : decl_context_scope.

Reserved Notation "G1 ,, G2"
  (at level 58, left associativity).

Fixpoint decl_ctx_app (G1 G2 : decl_context) : decl_context :=
  match G2 with
  | decl_ctx_nil => G1
  | G2', x => G1 ,, G2' , x
  | decl_ctx_cons_sv G2' sx => decl_ctx_cons_sv (G1 ,, G2') sx
  end%decl_context
where "G1 ,, G2" := (decl_ctx_app G1 G2) : decl_context_scope.

Open Scope decl_context_scope. *)