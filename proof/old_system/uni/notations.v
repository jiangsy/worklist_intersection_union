Require Export Coq.Unicode.Utf8.

Require Export uni.def_ott.
Require Export uni.def_extra.
Require Export uni.decl.def_extra.
Require Export uni.prop_ln.


Notation "⊢ Ψ" :=
  (d_wf_env Ψ)
    (at level 65, no associativity) : type_scope.

Notation "Ψ ⊢ A" :=
  (d_wf_typ Ψ A)
    (at level 65, no associativity) : type_scope.
    
Notation "Ψ ⊢ₘ T" :=
  (d_mono_typ Ψ T)
    (at level 65, no associativity) : type_scope.

Notation "Ψ ⊢ A <: B" :=
  (d_sub Ψ A B)
    (at level 65, A at next level, no associativity) : type_scope.

Notation "Ψ ⊢ e ⇐ A" :=
    (d_chk_inf Ψ e typingmode__chk A) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "Ψ ⊢ e ⇒ A" := 
    (d_chk_inf Ψ e typingmode__inf A) 
      (at level 65, e at next level, no associativity) : type_scope.

Notation "Ψ ⊢ A ○ B ⇒⇒ C" :=
    (d_inftapp Ψ A B C) 
      (at level 65, A at next level, B at next level, no associativity) : type_scope. 

Notation "Ψ ⊢ A ▹ B → C" :=
  (d_infabs Ψ A B C) 
    (at level 65, A at next level, B at next level, no associativity) : type_scope. 


Notation "X ~ □ ∈ᵈ E" := (binds X (dbind_tvar_empty) E)
  (at level 50, no associativity) : type_scope.

Notation "X ~ ■ ∈ᵈ E" := (binds X (dbind_stvar_empty) E)
  (at level 50, no associativity) : type_scope.

Notation "x ~ T ∈ᵈ E" := (binds x (dbind_typ T) E)
  (at level 50, T at next level, no associativity) : type_scope.

Notation "` X" := (typ_var_f X)
  (at level 0, X at level 0, no associativity) : type_scope.
Notation "↑ n" := (typ_var_b n)
  (at level 0, n at level 0, no associativity) : type_scope.

Notation "{ T' ᵗ/ₜ X } T" :=
  (subst_tvar_in_typ T' X T)
    ( at level 49, T' at level 50, X at level 0
    , right associativity) : type_scope.

Notation "{ e' ᵉ/ₑ x } e" :=
  (subst_var_in_exp e' x e)
    ( at level 49, e' at level 50, x at level 0
    , right associativity) : type_scope.

Notation "{ b' ᵇ/ₑ x } b" :=
  (subst_var_in_body b' x b)
    ( at level 49, b' at level 50, x at level 0
    , right associativity) : type_scope.


Notation "{ A ᶜˢ/ₜ X } cs" :=
  (subst_tvar_in_conts A X cs)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "{ A ᶜᵈ/ₜ X } cd" :=
  (subst_tvar_in_contd A X cd)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "{ A ʷ/ₜ X } w" :=
  (subst_tvar_in_work A X w)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "{ A ᵃʷ/ₜ X } Γ" :=
  (subst_tvar_in_aworklist A X Γ)
    ( at level 49, A at level 50, X at level 0
    , right associativity) : type_scope. 

Notation "T ^ₜ X" := (open_typ_wrt_typ T (typ_var_f X))
  (at level 48, left associativity) : type_scope.

Notation "T1 ^^ₜ T2" := (open_typ_wrt_typ T1 T2)
  (at level 48, left associativity) : type_scope.

Notation "e1 ᵉ^ₑ e2" := (open_exp_wrt_exp e1 e2)
  (at level 48, left associativity) : type_scope.

Notation "e ᵉ^ₜ A" := (open_exp_wrt_typ e A)
  (at level 48, left associativity) : type_scope.


Declare Scope dbind_scope.
Delimit Scope dbind_scope with dbind.
Bind Scope dbind_scope with dbind.

Notation "□" := dbind_tvar_empty : dbind_scope.
Notation "■" := dbind_stvar_empty : dbind_scope.
  
Declare Scope abind_scope.
Delimit Scope abind_scope with abind.
Bind Scope abind_scope with abind.

Notation "□" := abind_tvar_empty : abind_scope.
Notation "■" := abind_stvar_empty : abind_scope.
Notation "⬒" := abind_etvar_empty : abind_scope.
