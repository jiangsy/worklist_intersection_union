Require Import Coq.Program.Equality.


Require Import decl.notations.
Require Import ln_utils.

Hint Constructors dexp_red : core.

Lemma dwf_typ_lc_dtyp : forall E T,
  E ⊢ T -> lc_dtyp T.
Proof.
Admitted.

Hint Resolve dwf_typ_lc_dtyp : core.

Inductive empty_var_dom : denv -> Prop :=
  | evd_empty : empty_var_dom nil
  | evd_empty_tvar : forall E X, empty_var_dom E -> empty_var_dom ((X , dbind_tvar_empty) :: E)
  | evd_empty_stvar : forall E SX, empty_var_dom E -> empty_var_dom  ((SX , dbind_stvar_empty) :: E)
.


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

Hint Constructors empty_var_dom : core.

Theorem bind_var_var_dom_not_empty : forall E x T,
  binds x (dbind_typ T) E -> empty_var_dom E -> False.
Proof.
  intros. induction E.
  - inversion H.
  - destruct a. destruct b.
    + inversion H.
      * inversion H1.
      * inversion H0. auto.
    + inversion H.
      * inversion H1.
      * inversion H0. auto.
    + inversion H0. 
Qed.


Theorem progress' : forall E e m T,
  dtyping E e m T ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true \/ exists e', dexp_red e e'.
Proof.
  intros. dependent induction H; intros; auto.
  - exfalso; eapply bind_var_var_dom_not_empty; eauto.
  - specialize (IHdtyping H1).
    inversion IHdtyping.
    + left. auto.
    + right. destruct H2 as [e']. eauto.
  (* e1 e2 *)
  - specialize (IHdtyping1 H1). 
    specialize (IHdtyping2 H1). 
    inversion IHdtyping1.
    + inversion IHdtyping2.
      * admit. (* medium : inversion lemma of app *)
      * destruct H3 as [e2']. right. exists (dexp_app e1 e2'). 
        apply dexpred_app2; auto. 
        rewrite H2. constructor. admit. (* easy : lc *)
    + right. destruct H2 as [e1'].
      exists (dexp_app e1' e2). 
      constructor; auto.
      admit. (* easy : lc *)
  (* e => BOT *)
  - specialize (IHdtyping H1). inversion IHdtyping.
    + destruct e; try solve [inversion H2; inversion H0].
      * dependent destruction H0. inversion H3.
        right. exists (dexp_anno e dtyp_bot).  constructor.
        rewrite H5. constructor.
        admit. admit. (* easy : lc *)
    + right. destruct H2 as [e']. eauto.
  (* e @ T *)
  - specialize (IHdtyping H1).
    inversion IHdtyping.
    + admit. (* medium : inversion lemma of tapp *)
    + right. destruct H2 as [e1']. eauto.
  (* e => ∀ X . T *)
  - inst_cofinites_by L.
    apply H1. simpl. auto.
Admitted.


Theorem progress : forall e m T,
  dtyping nil e m T ->
  is_dvalue_of_dexp e = true \/ exists e', dexp_red e e'.
Proof.
  intros. eapply progress'; eauto.
Qed.




