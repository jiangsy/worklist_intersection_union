(* 
e -> e'
------------------ 
e : T -> e : T 

is incorrect 

(/\ a, \ x. x : a -> a) : ∀ a. a -> a

 *)
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

(* Theorem typing_all_inversion : forall E e m T,
  dtyping E e m (dtyp_all T) ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true ->
  (exists e1 T, e = dexp_tabs (dbody_anno e1 T)) \/ (exists e1 T, e = dexp_anno (dexp_tabs (dbody_anno e1 T)) (dtyp_all T)).
Proof.
  intros.
  dependent induction H.
  - admit.
  - admit.
  - inversion H2.
  - admit.
  - admit.
  - admit.
  - admit.
  - eauto. 
Admitted. *)


Theorem typing_all_inversion1 : forall E e T,
  dtyping E e dtypingmode_inf (dtyp_all T) ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true ->
  exists e1 T, e = dexp_tabs (dbody_anno e1 T).
Proof.
  intros.
  dependent induction H; try solve [inversion H2].
  - admit. (* impossible *)
Admitted.


Theorem typing_all_inversion : forall E e T,
  dtyping E e dtypingmode_inf (dtyp_all T) ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true ->
  (exists e1 T, e = dexp_tabs (dbody_anno e1 T)) \/ (exists e1 T, e = dexp_anno (dexp_tabs (dbody_anno e1 T)) (dtyp_all T)).
Proof.
  intros.
  dependent induction H; try solve [inversion H2].
  - admit.
  -
Admitted.

Fixpoint anno_nfold (n:nat) (e:dexp) (T T1:dtyp) :=
  match n with
  | 0 =>  (dexp_tabs (dbody_anno e T)) 
  | S n' => dexp_anno (anno_nfold n' e T T1) (dtyp_all T1)
  end.

Theorem typing_all_inversion3 : forall E e m T,
  dtyping E e m (dtyp_all T) ->
  m = dtypingmode_chk \/ m = dtypingmode_inf ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true ->
  (exists e1 T1, e = dexp_tabs (dbody_anno e1 T1)) \/ (exists e1 T1, e = dexp_anno (dexp_tabs (dbody_anno e1 T1)) (dtyp_all T)).
Proof.
  intros.
  dependent induction H; try solve [inversion H3]; 
  try solve [inversion H1].
  - assert 
    (dtypingmode_chk = dtypingmode_chk ∨ dtypingmode_chk = dtypingmode_inf) by auto. 
    simpl in H3.
    specialize (IHdtyping T (eq_refl _) H4 H2 H3).
    inversion IHdtyping.
    + destruct H5 as [e1 [T1]]. right.
      rewrite H5. eauto.
    + admit. (* should allow n'fold anno, exists n e1 t1, e = dexp_anno^n ((dexp_tabs (dbody_anno e1 T1))) *)
  - eauto.
  - admit.
  - admit.
  - inversion H1. inversion H4. inversion H4.
  - inversion H3. inversion H6. inversion H6.
  - inversion H0. inversion H3. inversion H3.
  - inversion H0. inversion H3. inversion H3.
  - inversion H1. inversion H4. inversion H4.
Admitted.


 Theorem typing_all_inversion5 : forall E e m S T,
  dtyping E e m S ->
  dsub E S (dtyp_all T) ->
  m = dtypingmode_chk \/ m = dtypingmode_inf ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true ->
  (exists e1 T1, e = dexp_tabs (dbody_anno e1 T1)) \/ (exists e1 T1, e = dexp_anno (dexp_tabs (dbody_anno e1 T1)) (dtyp_all T)).
Proof.
  intros E e m S T Htyping Hsub Heqm Hemp Heqv.
  generalize dependent T.
  dependent induction Htyping; intros T0 Hsub; try solve [inversion Heqv]; try solve [inversion Hsub].
  (* - assert 
  (dtypingmode_chk = dtypingmode_chk ∨ dtypingmode_chk = dtypingmode_inf) by auto. 
  simpl in H3.
  specialize (IHdtyping T (eq_refl _) H4 H2 H3).
  inversion IHdtyping.
  + destruct H5 as [e1 [T1]]. right.
    rewrite H5. eauto.
  + admit. should allow n'fold anno, exists n e1 t1, e = dexp_anno^n ((dexp_tabs (dbody_anno e1 T1))) *)
  - admit.
  - eauto. 
  - admit.
  - apply IHHtyping; auto. admit.
  - dependent destruction Hsub; eauto.
  - dependent destruction Hsub; eauto.
  - dependent destruction Hsub; eauto.
  - inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
  - inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
  - inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
  - inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
  - inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
  - inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
Admitted. 



Theorem typing_all_inversion6 : forall E e m S T L,
  dtyping E e m S ->
  (forall X, X `notin` L -> dsub E S (open_dtyp_wrt_dtyp T (dtyp_var_f X))) ->
  m = dtypingmode_chk \/ m = dtypingmode_inf ->
  empty_var_dom E ->
  is_dvalue_of_dexp e = true ->
  (exists e1 T1 n, e = anno_nfold n e1 T T1).
Proof.
intros E e m S T L Htyping Hsub Heqm Hemp Heqv.
generalize dependent T.
generalize dependent L.
(* generalize dependent X. *)
dependent induction Htyping; intros L0 T0 Hsub; try solve [inversion Heqv]; try solve [inversion Hsub].
(* - assert 
(dtypingmode_chk = dtypingmode_chk ∨ dtypingmode_chk = dtypingmode_inf) by auto. 
simpl in H3.
specialize (IHdtyping T (eq_refl _) H4 H2 H3).
inversion IHdtyping.
+ destruct H5 as [e1 [T1]]. right.
  rewrite H5. eauto.
+ admit. should allow n'fold anno, exists n e1 t1, e = dexp_anno^n ((dexp_tabs (dbody_anno e1 T1))) *)
- assert (dtypingmode_chk = dtypingmode_chk ∨ dtypingmode_chk = dtypingmode_inf) by auto.
  specialize (IHHtyping H0 Hemp Heqv L0 T0 Hsub).
  


- eauto. 
- inversion Hsub. inst_cofinites_by L. admit.
- apply IHHtyping; auto. admit.
- dependent destruction Hsub; eauto.
- dependent destruction Hsub; eauto.
- dependent destruction Hsub; eauto.
- inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
- inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
- inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
- inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
- inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
- inversion Heqm as [Heqm1 | Heqm2]. inversion Heqm1. inversion Heqm2.
Admitted. 

Theorem typing_all_inversion4 : forall e m T,
  dtyping nil e m (dtyp_all T) ->
  m = dtypingmode_chk \/ m = dtypingmode_inf ->
  is_dvalue_of_dexp e = true ->
  (exists e1 T1, e = dexp_tabs (dbody_anno e1 T1)) \/ (exists e1 T1, e = dexp_anno (dexp_tabs (dbody_anno e1 T1)) (dtyp_all T)).
Proof.
  intros.
  dependent induction H; try solve [inversion H2].
  - assert
    (dtypingmode_chk = dtypingmode_chk ∨ dtypingmode_chk = dtypingmode_inf) by auto. 
    simpl in H2.
    specialize (IHdtyping T (JMeq_refl _) (eq_refl _) H3 H2).
    inversion IHdtyping.
    + destruct H4 as [e1 [T1]]. right.
      rewrite H4. eauto.
    + admit. (* should allow n'fold anno, exists n e1 t1, e = dexp_anno^n ((dexp_tabs (dbody_anno e1 T1))) *)
  - eauto.
  - admit.
  - admit.
  - inversion H1. inversion H4. inversion H4.
  - inversion H3. inversion H6. inversion H6.
  - inversion H0. inversion H3. inversion H3.
  - inversion H0. inversion H3. inversion H3.
  - inversion H1. inversion H4. inversion H4.
Admitted. 


Theorem progress1 : forall e m T,
  dtyping nil e m T ->
  is_dvalue_of_dexp e = true \/ exists e', dexp_red e e'.
Proof.
  intros. dependent induction H; intros; auto.
  - specialize (IHdtyping (JMeq_refl _)).
    inversion IHdtyping.
    + left. auto.
    + right. destruct H1 as [e']. eauto.
  (* e1 e2 *)
  - specialize (IHdtyping1 (JMeq_refl _)). 
    specialize (IHdtyping2 (JMeq_refl _)). 
    inversion IHdtyping1.
    + inversion IHdtyping2.
      * admit. (* medium : inversion lemma of app *)
      * destruct H2 as [e2']. right. exists (dexp_app e1 e2'). 
        apply dexpred_app2; auto. 
        rewrite H1. constructor. admit. (* easy : lc *)
    + right. destruct H1 as [e1'].
      exists (dexp_app e1' e2). 
      constructor; auto.
      admit. (* easy : lc *)
  (* e => BOT *)
  - specialize (IHdtyping  (JMeq_refl _)). inversion IHdtyping.
    + destruct e; try solve [inversion H1; inversion H0].
      * dependent destruction H0. inversion H2.
        right. exists (dexp_anno e dtyp_bot).  constructor.
        rewrite H4. constructor.
        admit. admit. (* easy : lc *)
    + right. destruct H1 as [e']. eauto.
  (* e @ T *)
  - specialize (IHdtyping  (JMeq_refl _)).
    inversion IHdtyping.
    + admit. (* medium : inversion lemma of tapp *)
    + right. destruct H1 as [e1']. eauto.
  (* e => ∀ X . T *)
  - inst_cofinites_by L.
    apply H1. simpl. auto.
Admitted.


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
    + inversion IHdtyping.
      * right.,ç
      * destruct H3 as [e']. eauto.
    admit. (* medium : inversion lemma of tapp *)
    + right. destruct H2 as [e1']. eauto.
  (* e => ∀ X . T *)
  - inst_cofinites_by L.
    apply H1. simpl. auto.
Admitted.

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




