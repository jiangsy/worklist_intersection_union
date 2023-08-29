(* 
e -> e'
------------------ 
e : T -> e : T 

is incorrect 

(/\ a, \ x. x : a -> a) : ∀ a. a -> a

 *)
Require Import Coq.Program.Equality.


Require Import decl.notations.
Require Import decl.prop_basic.
Require Import decl.prop_subtyping.
Require Import ln_utils.

Hint Constructors dexp_red : core.


Hint Resolve dwf_typ_lc_dtyp : core.

Inductive empty_var_dom : denv -> Prop :=
  | evd_empty : empty_var_dom nil
  | evd_empty_tvar : forall E X, empty_var_dom E -> empty_var_dom ((X , dbind_tvar_empty) :: E)
  | evd_empty_stvar : forall E SX, empty_var_dom E -> empty_var_dom  ((SX , dbind_stvar_empty) :: E)
.

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

Theorem typing_all_inversion : forall E e T,
  d_typing E e d_typingmode_inf (dtyp_all T) ->
  empty_var_dom E ->
  d_isval e ->
  (exists e1 T1, e = dexp_tabs (dbody_anno e1 T1)) \/ (exists e1 T1, e = dexp_anno (dexp_abs e1) (dtyp_all T1)).
Proof.
  intros.
  dependent induction H; try solve [inversion H2]; eauto.
  - dependent destruction H2; eauto.
Qed.

Theorem progress' : forall E e m T,
  d_typing E e m T ->
  empty_var_dom E ->
  d_isval e \/ exists e', dexp_red e e'.
Proof.
  intros. dependent induction H; intros; auto.
  - exfalso; eapply bind_var_var_dom_not_empty; eauto.
  - specialize (IHd_typing H1).
    inversion IHd_typing.
    + admit.
    + right. destruct H2 as [e']. eauto.
  (* e1 e2 *)
  - specialize (IHd_typing1 H1). 
    specialize (IHd_typing2 H1). 
    inversion IHd_typing1.
    + inversion IHd_typing2.
      * dependent destruction H2.
        -- dependent destruction H. inversion H0.
        -- dependent destruction H.
        -- dependent destruction H.
        -- right. exists (dexp_app e e2). admit.
        -- admit.
      * destruct H3 as [e2']. right. exists (dexp_app e1 e2'). 
        apply dexpred_app2; auto. 
    + right. destruct H2 as [e1'].
      exists (dexp_app e1' e2). 
      constructor; auto.
      admit. (* easy : lc *)
  - left; admit. (* easy : lc *)
  (* e => BOT *)
  - specialize (IHd_typing H1). inversion IHd_typing.
  
    + destruct e; try solve [inversion H2; inversion H0].
      * dependent destruction H0. dependent destruction H3.
        right. exists (dexp_anno (dexp_abs e0) dtyp_bot).  
        apply dexpred_tappbot; auto.
        admit. (* easy : lc *)
    + right. destruct H2 as [e']. eauto.
  (* e @ T *)
  - specialize (IHd_typing H1).
    inversion IHd_typing.
    + specialize (typing_all_inversion _ _ _ H0 H1 H2).
      intros. inversion H3.
      * destruct H4 as [e3 [T3]]. rewrite H4.
        right. exists (dexp_anno (open_dexp_wrt_dtyp e3 T2) (open_dtyp_wrt_dtyp T3 T2)).
        econstructor; admit. (* easy : lc *)
      * destruct H4 as [e3 [T3]]. rewrite H4.
        right. exists (dexp_anno (dexp_abs e3) (open_dtyp_wrt_dtyp T3 T2)).
        econstructor; admit. (* easy : lc *)
    + destruct H2 as [e']. eauto.
  (* e => ∀ X . T *)
  - left. econstructor. admit. (* easy : lc *)
Admitted.


Theorem progress : forall e m T,
  d_typing nil e m T ->
  d_isval e \/ exists e', dexp_red e e'.
Proof.
  intros. eapply progress'; eauto.
Qed.

Hint Constructors d_typing : type_safety.

Lemma check_top_false : forall E T,
  d_typing E dexp_top d_typingmode_chk T -> E ⊢ dtyp_top <: T.
Proof.
  intros; dependent induction H; eauto...
  - inversion H. inst_cofinites_by (L `union` L0). 
    exfalso. eapply dsub_top_fv_false; eauto.
  - dependent destruction H; auto.
Qed.

Lemma check_unit_false : forall E T,
  d_typing E dexp_unit d_typingmode_chk T -> E ⊢ dtyp_unit <: T.
Proof.
  intros; dependent induction H; eauto...
  - inversion H. inst_cofinites_by (L `union` L0). 
    exfalso. eapply dsub_unit_fv_false; eauto.
  - dependent destruction H; auto.
Qed.
(* 
Theorem chk_inf_sub : forall E e T1 T2,
  d_typing E e d_typingmode_inf T1 ->
  d_typing E e d_typingmode_chk T2 ->
  E ⊢ T1 <: T2.
Proof.
  intros. dependent induction H0.
  - econstructor; admit.
  -
  
Qed. *)


(* E |- e <= T 
[t2 / x] E |- [t2 / x] e <= [t2 / x] T *)
Theorem preservation : forall E e e' m T,
  d_typing E e m T -> 
  dexp_red e e' -> 
  d_typing E e' m T.
Proof with eauto with type_safety.
  intros. generalize dependent e'.
  induction H; intros e' Hred; try solve [inversion Hred]; eauto...
  - dependent destruction Hred; eauto...
    + dependent destruction H3.
      * admit.
      * admit.
      * inversion H2.
      * admit.
      * dependent destruction H0; admit.
  - dependent destruction Hred; eauto...
    inversion H. admit.
  - dependent destruction Hred; eauto...
    + inversion H0.
    + inversion H0.
  - dependent destruction Hred.
    + eauto...
    + dependent destruction H0. 
      replace (open_dexp_wrt_dtyp (dexp_anno e T1) T2) with 
              (dexp_anno (open_dexp_wrt_dtyp e T2) (open_dtyp_wrt_dtyp T1 T2)) by auto.
      econstructor.
      * dependent destruction H0.
        inst_cofinites_by (L0 `union` ftv_in_dtyp T1).
        replace (T1 ^^ᵈ T2) with ({T2 /ᵈ x} T1 ^ᵈ x).
        assert (x ~ dbind_tvar_empty ++ E ⊢ {T2 /ᵈ x} T1 ^ᵈ x). {
          apply wft_all_open_wfdtyp_wft; eauto.
          apply dwf_typ_weakening_cons. auto.
        }
        admit.
        simpl. admit. 
      * inst_cofinites_by L. admit.
    + dependent destruction H0. eapply d_typing_infanno.
      admit. admit.
    + inversion H0.
Admitted.
