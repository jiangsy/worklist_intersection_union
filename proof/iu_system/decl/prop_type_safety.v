Require Import Coq.Program.Equality.

(* Require Import properties. *)
Require Import decl.notations.
Require Import ln_utils.

Hint Constructors dexp_red : core.

Lemma dwf_typ_lc_dtyp : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
Admitted.

Hint Resolve dwf_typ_lc_dtyp : core.

Fixpoint var_dom (e : denv) : atoms :=
  match e with 
  | nil => empty
  | ((x, dbind_typ T) :: e') => add x (var_dom e')
  | (_ :: e') => var_dom e'
  end.

(* Lemma canonical_form_abs : forall E e m,
  dtyping E e m dtyp_bot -> 
  var_dom E = empty ->
  is_dvalue_of_dexp e = true ->
  False.
Proof.
  intros. induction H.
  - admit.
  - inversion H1. auto.
  - admit.
  - inversion H1.
  - inversion H1. *)



Theorem progress : forall E e m T,
  dtyping E e m T ->
  var_dom E = empty ->
  is_dvalue_of_dexp e \/ exists e', dexp_red e e'.
Proof.
  intros. dependent induction H; intros; auto.
  - admit. (* easy : impossible *)
  - specialize (IHdtyping H1).
    inversion IHdtyping.
    + right. exists e. econstructor. admit. admit. (* easy : lc *)
    + right. destruct H2 as [e']. exists e. constructor; admit.
  - specialize (IHdtyping1 H1). 
    specialize (IHdtyping2 H1). 
    inversion IHdtyping1.
    + inversion IHdtyping2.
      * admit.
      * destruct H3 as [e2']. right. exists (dexp_app e1 e2'). apply dexpred_app2; auto. rewrite H2. constructor. admit.
    + right. destruct H2 as [e1'].
      exists (dexp_app e1' e2). constructor; auto.
      admit.
  (* e => BOT *)
  - specialize (IHdtyping H1). inversion IHdtyping.
    + induction e; try solve [inversion H2].
      * inversion H0.
      * inversion H0.
      * inversion H0.
      * inversion H0.
    + right. destruct H2 as [e']. eauto.
  (* e => ∀ X . T *)
  - specialize (IHdtyping H1).
    inversion IHdtyping.
    + admit.
    + right. destruct H2 as [e1']. eauto.
  (* app *)
  - inst_cofinites_by L.
    apply H1. simpl. auto.
Qed.

