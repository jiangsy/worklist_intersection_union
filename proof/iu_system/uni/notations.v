Require Export Coq.Unicode.Utf8.

Require Export uni.def_ott.
Require Export uni.def_extra.
(* Require Export uni.worklist.def. *)
Require Export uni.prop_ln.


Notation "⊢ E" :=
  (d_wf_env E)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ T" :=
  (d_wf_typ E T)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ₛ T" :=
  (d_wf_typ_s E T)
    (at level 65, no associativity) : type_scope.

Notation "E ⊢ S1 <: T1" :=
  (d_sub E S1 T1)
    (at level 65, S1 at next level, no associativity) : type_scope.

(* Notation "E ⊢ e ⇐ T" :=
    (d_typing E e typingmode_chk T) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "E ⊢ e ⇒ T" := 
    (d_typing E e d_typingmode_inf T) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "E ⊢ T1 ○ T2 ⇒⇒ T3" :=
    (d_inftapp E T1 T2 T3) 
      (at level 65, T1 at next level, T2 at next level, no associativity) : type_scope. 

Notation "E ⊢ T1 ▹ T2 → T3" :=
  (d_infabs E T1 T2 T3) 
    (at level 65, T1 at next level, T2 at next level, no associativity) : type_scope.  *)


Notation "▫" := dbind_tvar_empty.
Notation "▪" := dbind_stvar_empty.

Notation "X ~ ▫ ∈ E" := (binds X (dbind_tvar_empty) E)
  (at level 50, no associativity) : type_scope.

Notation "X ~ ▪ ∈ E" := (binds X (dbind_stvar_empty) E)
  (at level 50, no associativity) : type_scope.

Notation "x ~ T ∈ E" := (binds x (dbind_typ T) E)
  (at level 50, T at next level, no associativity) : type_scope.

Notation "`ᵈ X" := (typ_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.
Notation "↑ n" := (typ_var_b n)
  (at level 0, n at level 0, no associativity) : type_scope.

Notation "{ T' /ᵈ X } T" :=
  (subst_tvar_in_typ T' X T)
    ( at level 49, T' at level 50, X at level 0
    , right associativity) : type_scope.

Notation "T ^ᵈ X" := (open_typ_wrt_typ T (typ_var_f X))
  (at level 48, left associativity) : type_scope.

Notation "T1 ^^ᵈ T2" := (open_typ_wrt_typ T1 T2)
  (at level 48, left associativity) : type_scope.

(* 
Notation "e ⟼ e'" := 
  (dexp_red e e')
    (at level 65, no associativity). *)

Declare Scope dworklist_scope.
Delimit Scope dworklist_scope with dworklist.
Bind Scope dworklist_scope with dworklist.


Notation " x ~ T ; Ω " :=
  (dworklist_consvar Ω x (dbind_typ T))
      (at level 58, T at next level, right associativity) : dworklist_scope.
    
Notation " X ~ ▪ ; Ω " :=
  (dworklist_constvar Ω X dbind_tvar_empty)
      (at level 58, right associativity) : dworklist_scope.

Notation " W ⫤ Ω " :=
  (dworklist_conswork Ω W)
      (at level 58, right associativity) : dworklist_scope.

(* Notation " Ω ⟶ₐ⁎⋅ " :=
  (d_wl_red Ω)
      (at level 58, no associativity) : type_scope.

Notation " Ω ⟶⁎⋅ " :=
  (d_wl_del_red Ω)
      (at level 58, no associativity) : type_scope. *)