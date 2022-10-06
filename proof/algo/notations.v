Require Export algo.ln_inf.


Declare Scope la_type_scope.
Delimit Scope la_type_scope with la_type.
Bind Scope la_type_scope with la_type.


Notation "`′ x" :=
  (la_t_tvar_f x) (at level 0, x at level 0, no associativity) : la_type_scope.

Notation "↑′ n" :=
  (la_t_tvar_b n) (at level 0, n at level 0) : la_type_scope.

Notation "e ^ᵃ x" :=
  (open_la_type_wrt_la_type e (la_t_tvar_f x)) (at level 48, left associativity) : la_type_scope.

Notation "e1 ^^ᵃ e2" :=
  (open_la_type_wrt_la_type e1 e2) (at level 48, left associativity) : la_type_scope.

Notation "[ t /ᵃ x ] A" :=
  (subst_la_type t x A)
    (at level 49, t at level 50, x at level 0, right associativity) : la_type_scope.

Notation "`^ x" :=
  (la_t_evar x) (at level 0, x at level 0, no associativity) : la_type_scope.


Open Scope la_type_scope.
