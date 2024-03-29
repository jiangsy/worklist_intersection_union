Require Export Coq.Unicode.Utf8.

Require Export uni.def_ott.
Require Export uni.def_extra.
Require Export uni.decl.def_extra.
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

Notation "E ⊢ e ⇐ T" :=
    (d_typing E e typingmode__chk T) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "E ⊢ e ⇒ T" := 
    (d_typing E e typingmode__inf T) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "E ⊢ T1 ○ T2 ⇒⇒ T3" :=
    (d_inftapp E T1 T2 T3) 
      (at level 65, T1 at next level, T2 at next level, no associativity) : type_scope. 

Notation "E ⊢ T1 ▹ T2 → T3" :=
  (d_infabs E T1 T2 T3) 
    (at level 65, T1 at next level, T2 at next level, no associativity) : type_scope. 


Notation "□" := dbind_tvar_empty.
Notation "■" := dbind_stvar_empty.


Notation "X ~ □ ∈ E" := (binds X (dbind_tvar_empty) E)
  (at level 50, no associativity) : type_scope.

Notation "X ~ ■ ∈ E" := (binds X (dbind_stvar_empty) E)
  (at level 50, no associativity) : type_scope.

Notation "x ~ T ∈ E" := (binds x (dbind_typ T) E)
  (at level 50, T at next level, no associativity) : type_scope.

Notation "` X" := (typ_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.
Notation "↑ n" := (typ_var_b n)
  (at level 0, n at level 0, no associativity) : type_scope.

Notation "{ T' /ᵗ X } T" :=
  (subst_tvar_in_typ T' X T)
    ( at level 49, T' at level 50, X at level 0
    , right associativity) : type_scope.

Notation "{ e' /ᵉₑ x } e" :=
  (subst_var_in_exp e' x e)
    ( at level 49, e' at level 50, x at level 0
    , right associativity) : type_scope.

Notation "{ b' /ᵇₑ x } b" :=
  (subst_var_in_body b' x b)
    ( at level 49, b' at level 50, x at level 0
    , right associativity) : type_scope.


Notation "{ A /ᶜˢₜ X } cs" :=
  (subst_tvar_in_conts A X cs)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "{ A /ᶜᵈₜ X } cd" :=
  (subst_tvar_in_contd A X cd)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "{ A /ʷₜ X } w" :=
  (subst_tvar_in_work A X w)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "T ^ᵗ X" := (open_typ_wrt_typ T (typ_var_f X))
  (at level 48, left associativity) : type_scope.

Notation "T1 ^^ᵗ T2" := (open_typ_wrt_typ T1 T2)
  (at level 48, left associativity) : type_scope.

Notation "e1 ^ᵉₑ e2" := (open_exp_wrt_exp e1 e2)
  (at level 48, left associativity) : type_scope.

Notation "e ^ᵉₜ A" := (open_exp_wrt_typ e A)
  (at level 48, left associativity) : type_scope.


