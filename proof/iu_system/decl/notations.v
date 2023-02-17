Require Export Coq.Unicode.Utf8.

Require Export decl.def_ott.
Require Export decl.def_extra.
Require Export decl.prop_ln.


Notation "⊢ E" :=
  (dwf_env E)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ T" :=
  (dwf_typ E T)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ₛ T" :=
  (dwf_typ_s E T)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ S <: T" :=
  (dsub E S T)
    (at level 65, S at next level, no associativity) : type_scope.

(* Notation "E ⊢ e ⇐ T" :=
    (dchk E e T) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "E ⊢ e ⇒ T" := 
    (dinf E e T) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "E ⊢ T1 • e ⇒⇒ T2" :=
    (dinfapp E T1 e T2) 
      (at level 65, T1 at next level, e at next level, no associativity) : type_scope. *)

Notation "X ∈ E" := (binds X (dbind_tvar_empty))
  (at level 65, no associativity) : type_scope.

Notation "~ X ∈ E" := (binds X (dbind_stvar_empty))
  (at level 65, no associativity) : type_scope.


Notation "`ᵈ X" := (dtyp_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.
Notation "↑ n" := (dtyp_var_b n)
  (at level 0, n at level 0, no associativity) : type_scope.

Notation "{ T' /ᵈ X } T" :=
  (dsubst_tv_in_dtyp T' X T)
    ( at level 49, T' at level 50, X at level 0
    , right associativity) : type_scope.

Notation "{ T' /ₛᵈ SX } T" :=
  (dsubst_stv_in_dtyp T' SX T)
    ( at level 49, T' at level 50, SX at level 0
    , right associativity) : type_scope.

Notation "T ^ᵈ X" := (open_dtyp_wrt_dtyp T (dtyp_var_f X))
  (at level 48, left associativity) : type_scope.

Notation "T1 ^^ᵈ T2" := (open_dtyp_wrt_dtyp T1 T2)
  (at level 48, left associativity) : type_scope.


Notation "e ⟼ e'" := 
  (dexp_red e e')
    (at level 65, no associativity).


Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dworklist.
Bind Scope dworklist_scope with dworklist.


Notation " x ~ T ; W " :=
  (dworklist_consvar W x (dbind_typ T))
      (at level 58, T at next level, right associativity) : dworklist_scope.
    
Notation " X ~ ▪ ; W " :=
  (dworklist_constvar W X dbind_tvar_empty)
      (at level 58, right associativity) : dworklist_scope.

Notation " SX ~ ~▪ ; W " :=
  (dworklist_consstvar W SX dbind_stvar_empty)
      (at level 58, right associativity) : dworklist_scope.

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