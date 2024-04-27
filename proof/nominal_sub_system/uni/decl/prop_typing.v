Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.


Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import ln_utils.


(* Definition wf_dom : forall {Ψ}, ⊢ Ψ -> atoms.
Proof.
  intros.
  set (x := dom Ψ). exact x.
Defined. *)


Hint Constructors d_wf_typ: core.
Hint Constructors d_wf_env: core.
Hint Constructors d_wf_typ_s: core.
Hint Constructors d_typing : typing.



Inductive d_subenv : denv -> denv -> Prop :=
| d_subenv_empty: d_subenv nil nil
| d_subenv_tvar : forall Ψ Ψ' X,
    d_subenv Ψ' Ψ ->
    d_subenv (X ~ dbind_tvar_empty  ++  Ψ')
        (X ~ dbind_tvar_empty  ++  Ψ)
| d_subenv_stvar : forall Ψ Ψ' X,
    d_subenv Ψ' Ψ ->
    d_subenv (X ~ dbind_stvar_empty  ++  Ψ')
        (X ~ dbind_stvar_empty  ++  Ψ)
| d_subenv_var : forall Ψ Ψ' x A A',
    d_subenv Ψ' Ψ ->
    d_sub Ψ A A' ->
    d_subenv (x ~ dbind_typ A ++ Ψ')
        (x ~ dbind_typ A' ++ Ψ)
.

Hint Constructors d_subenv: typing.

Lemma d_subenv_refl: forall Ψ,
  ⊢ Ψ -> d_subenv Ψ Ψ.
Proof with auto with typing.
  intros. induction H; auto...
  econstructor; auto.
  apply dsub_refl; auto.
Qed.

Lemma d_subenv_same_dom : forall Ψ Ψ',
  d_subenv Ψ' Ψ ->
  dom Ψ = dom Ψ'.
Proof.
  intros. induction H; simpl; auto; rewrite IHd_subenv; auto.
Qed.

Lemma d_subenv_same_tvar : forall Ψ Ψ' X,
  d_subenv Ψ' Ψ ->
  binds X dbind_tvar_empty Ψ ->
  binds X dbind_tvar_empty Ψ'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.


Lemma d_subenv_same_var : forall Ψ Ψ' A x,
  ⊢ Ψ ->
  d_subenv Ψ' Ψ ->
  x ~ A ∈ Ψ ->
  exists A', x ~ A' ∈ Ψ' /\ Ψ ⊢ A' <: A.
Proof.
  intros. induction H0; simpl; intros; auto.
  - inversion H1; auto.
  - inversion H1; auto.
    + inversion H2.
    + dependent destruction H.
      specialize (IHd_subenv H H3).
      destruct IHd_subenv as [A'].
      exists A'; intuition.
      eapply d_sub_weaken_cons; eauto.
  - inversion H1; auto.
    + inversion H2.
    + dependent destruction H. specialize (IHd_subenv H H3).
      destruct IHd_subenv as [A'].
      exists A'; intuition.
      eapply d_sub_weaken_cons; eauto.
  - inversion H1; auto.
    + dependent destruction H3.
      exists A0; intuition.
      eapply d_sub_weaken_cons; eauto.
    + dependent destruction H. specialize (IHd_subenv H H5).
      destruct IHd_subenv as [A''].
      exists A''; intuition.
      eapply d_sub_weaken_cons; eauto.
Qed.


Lemma d_subenv_same_stvar : forall Ψ Ψ' X,
  d_subenv Ψ' Ψ ->
  binds X dbind_stvar_empty Ψ ->
  binds X dbind_stvar_empty Ψ'.
Proof.
  intros. induction H; simpl; intros; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    + inversion H1; auto.
  - inversion H0; auto.
    inversion H2.
Qed.


Lemma d_subenv_wf_typ : forall Ψ Ψ' T,
  Ψ ⊢ T -> d_subenv Ψ' Ψ -> Ψ' ⊢ T.
Proof.
  intros * H. generalize dependent Ψ'. induction H; intros; auto.
  - econstructor.
    eapply d_subenv_same_tvar; eauto.
  - eapply d_wf_typ__stvar.
    eapply d_subenv_same_stvar; eauto.
  - eapply d_wf_typ__all with (L:=L).
    + intros. inst_cofinites_with X. auto.
    + intros. inst_cofinites_with X. eapply H1.
      econstructor. auto.
Qed.

#[local] Hint Resolve d_subenv_wf_typ : core.

Lemma d_subenv_wf_env : forall Ψ,
  ⊢ Ψ ->
  forall Ψ',
    d_subenv Ψ' Ψ ->
    ⊢ Ψ'.
Proof.
  intros Ψ H. induction H; intros.
  - inversion H. auto.
  - dependent destruction H1.
    econstructor; auto.
    erewrite <- d_subenv_same_dom; auto.
  - dependent destruction H1.
    econstructor; auto.
    erewrite <- d_subenv_same_dom; auto.
  - dependent destruction H2.
    econstructor; auto.
    + apply d_sub_dwft in H3. destruct H3.
      eapply d_subenv_wf_typ; eauto. auto. intuition.
    + erewrite <- d_subenv_same_dom; auto.
Qed.

Lemma d_subenv_wf_env_inv : forall Ψ',
  ⊢ Ψ' ->
  forall Ψ,
    d_subenv Ψ' Ψ ->
    ⊢ Ψ.
Proof with subst; try solve_notin; eauto using d_sub_dwft_2.
  intros * HW Ψ HS. induction* HS.
  all: forwards HE: d_subenv_same_dom HS;
    forwards*: d_wf_env_strenthening_head HW;
    inverts HW;
    econstructor; try rewrite HE...
Qed.


Ltac solve_wf_subenv := match goal with
  | H : d_subenv ?Ψ' ?Ψ |- ?Ψ' ⊢ ?T => eapply d_subenv_wf_typ; eauto
  | H : d_subenv ?Ψ' ?Ψ |- ⊢ ?Ψ' => eapply d_subenv_wf_env; eauto
end.

Lemma binds_subenv: forall Ψ X Ψ',
    X ~ ▫ ∈ Ψ -> d_subenv Ψ' Ψ -> X ~ ▫ ∈ Ψ'.
Proof with try solve_by_invert.
  intros* HD HS. induction* HS.
  - forwards* [?|?]: binds_app_1 HD.
  - forwards* [?|?]: binds_app_1 HD.
  - forwards* [(?&?)|?]: binds_cons_1 HD...
Qed.

Lemma d_mono_typ_subenv: forall Ψ A Ψ',
    d_mono_typ Ψ A -> d_subenv Ψ' Ψ -> d_mono_typ Ψ' A.
Proof with eauto using binds_subenv.
  intros* HD HS. gen HS.
  induction HD; intros...
Qed.

Lemma d_sub_subenv: forall Ψ A B,
  Ψ ⊢ A <: B -> forall Ψ', d_subenv Ψ' Ψ -> Ψ' ⊢ A <: B.
Proof with eauto using d_mono_typ_subenv.
  intros Ψ A B Hsub.
  induction Hsub; try solve [econstructor; solve_wf_subenv].
  - econstructor; auto.
  - intros. econstructor; auto. intros. inst_cofinites_with X.
    specialize (H2 (X ~ dbind_stvar_empty ++ Ψ')).
    assert (d_subenv (X ~ dbind_stvar_empty ++ Ψ') (X ~ dbind_stvar_empty ++ Ψ)). {
      constructor. auto. }
    specialize (H2 H5).
    auto.
  - intros. forwards: IHHsub H2.
    pick fresh X and apply d_sub__alll; try applys H3...
Qed.


Hint Resolve d_subenv_wf_typ : typing.
Hint Resolve d_subenv_wf_env : typing.
Hint Resolve d_wft_typ_subst : typing.
Hint Resolve d_wf_env_subst_tvar_typ : typing.
Hint Resolve bind_typ_subst : typing.
Hint Resolve d_wf_typ_dlc_type : typing.


(* for the e <= forall a. A, not used now*)
Theorem d_chkinf_subst_mono: forall Ψ1 Ψ2 X e m A T,
  d_typing (Ψ2 ++ X ~ dbind_tvar_empty ++ Ψ1) e m A ->
  d_mono_typ Ψ1 T ->
  d_typing (map (subst_tvar_in_dbind T X) Ψ2  ++ Ψ1) (subst_tvar_in_exp T X e) m ({T /ᵗ X} A).
Proof with auto with typing.
  (* intros.
  generalize dependent T2.
  dependent induction H; intros; try solve [simpl in *; eauto 5 with typing].
  - simpl in *. eapply d_typing__inftabs with (L:=L `union` singleton X).
    + replace (typ_all ({T2 /ᵗ X} T1)) with ({T2 /ᵗ X}  typ_all T1) by auto.
      auto...
    + intros. specialize (notin_union_1 _ _ _ H4). intros.
      specialize (H1 _ H5 Ψ (X0 ~ dbind_tvar_empty ++ F) X (JMeq_refl _) T2 H2 H3).
      assert (lc_typ T2) by eauto...
      specialize (d_subst_tv_in_exp_open_exp_wrt_typ e T2 (typ_var_f X0) X H6).
      intros. simpl in H7. unfold eq_dec in H7.
      destruct (EqDec_eq_of_X X0 X) in H7.
      * subst. apply notin_union_2 in H4. apply notin_singleton_1 in H4.
        contradiction.
      * rewrite <- H7. rewrite typ_subst_open_comm; auto.
  - simpl in *. rewrite d_subst_tv_in_typ_open_typ_wrt_typ; eauto...
  - simpl in *. apply d_typing__chkabstop with (L:=L).
    intros x Hfr. inst_cofinites_with x.
    replace (exp_var_f x) with (d_subst_tv_in_exp T2 X (exp_var_f x)) by auto.
    rewrite <-  d_subst_tv_in_exp_open_exp_wrt_exp.
    replace (x ~ dbind_typ typ_bot ++ map (d_subst_tv_in_binding T2 X) F ++ Ψ) with
    ((map (d_subst_tv_in_binding T2 X) (x ~ dbind_typ typ_bot ++ F)) ++ Ψ) by auto.
    auto...
  - simpl in *. eapply d_typing__chkabs with (L:=L); eauto...
    intros X1 Hfr.
    inst_cofinites_with X1.
    specialize (H1 Ψ ((X1, dbind_typ T1) :: F ) X (JMeq_refl _) T0 H2 H3).
    replace (exp_var_f X1) with (d_subst_tv_in_exp T0 X (exp_var_f X1)) by (simpl; auto).
    rewrite <- d_subst_tv_in_exp_open_exp_wrt_exp; eauto...
  - simpl in *. eapply d_typing__chkall with (L:=L `union` singleton X); eauto...
    + replace (typ_all ({T2 /ᵗ X} T1)) with ({T2 /ᵗ X} typ_all T1) by auto.
      auto...
    + intros. inst_cofinites_with X0.
      rewrite typ_subst_open_comm; eauto...
      replace (X0 ~ dbind_tvar_empty ++ map (d_subst_tv_in_binding T2 X) F ++ Ψ) with
      (map (d_subst_tv_in_binding T2 X) (X0 ~ dbind_tvar_empty ++ F) ++ Ψ) by auto.
      auto.
  - simpl in *.
    apply d_typing__chksub with (S1:=({T2 /ᵗ X} S1)); eauto.
    eapply d_sub_subst_mono; eauto.
  - simpl in *. eapply d_typing__infappall with (T3:={T0 /ᵗ X} T3); eauto...
    + apply d_mono_typ_subst_mono_mono; auto.
    + replace (typ_all ({T0 /ᵗ X} T1)) with ({T0 /ᵗ X} typ_all T1) by auto.
      auto...
    + rewrite <- d_subst_tv_in_typ_open_typ_wrt_typ; eauto... *)
Abort.


Definition dmode_size (mode : typing_mode) : nat :=
  match mode with
  | typingmode__inf => 0
  | typingmode__chk => 1
  end.


Fixpoint
  exp_size (e:exp) : nat :=
    match e with
    | exp_unit => 1
    | exp_var_f _ => 1
    | exp_var_b _ => 1
    | exp_abs e1 => 1 + exp_size e1
    | exp_app e1 e2 => 1 + exp_size e1 + exp_size e2
    | exp_anno e1 _ => 1 + exp_size e1
    | exp_tapp e1 _ => 1 + exp_size e1
    | exp_tabs b => 1 + body_size b
    end with
  body_size (b:body) :=
    match b with
    | body_anno e T => 1 + exp_size e
    end
  .



Hint Constructors d_inftapp : inftapp.


Lemma d_inftapp_wft : forall Ψ A B C,
  d_inftapp Ψ A B C ->
  ⊢ Ψ /\ Ψ ⊢ A /\ Ψ ⊢ B /\ Ψ ⊢ C.
Proof.
  intros. induction H; intuition.
  - eapply d_wft_all_open; eauto.
Qed.

Hint Resolve d_inftapp_wft : typing.

Theorem d_inftapp_subsumption_same_env : forall Ψ A B C A',
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ⊢ A' <: A ->
  exists C', Ψ ⊢ C' <: C /\ Ψ ⊢ A' ○ B ⇒⇒ C'.
Proof with auto with typing.
  intros. generalize dependent A'. dependent induction H.
  - intros. dependent induction H1.
    + exists typ_bot. split; auto... constructor; auto.
    + eapply d_sub_open_mono_bot_false in H4; eauto. contradiction.
  - intros. dependent induction H2.
    + exists typ_bot. intuition...
      econstructor...
      dependent destruction H0. pick fresh X.
      inst_cofinites_with X.
      erewrite <- typ_subst_open_var; eauto...
      rewrite_env ((map (subst_tvar_in_dbind B X) nil) ++ Ψ).
      eapply d_wft_typ_subst; eauto...
      econstructor; eauto.
    + exists (A0 ^^ᵈ B). split; auto...
      pick fresh X. inst_cofinites_with X.
      erewrite <- typ_subst_open_var; eauto.
      erewrite <- typ_subst_open_var with (A:=A); eauto.
      rewrite_env ((map (subst_tvar_in_dbind B X) nil) ++ Ψ).
      apply d_sub_subst_stvar; auto...
      econstructor; eauto.
      inst_cofinites_for d_wf_typ__all; intros.
      * inst_cofinites_with X. auto.
      * inst_cofinites_with X.
        apply d_wf_typ_subst_tvar_stvar_cons; eauto...
        apply d_sub_dwft in H5; intuition.
    + inversion H3.
Qed.

Corollary d_inftapp_wft_0 : forall Ψ A B C,
    d_inftapp Ψ A B C -> ⊢ Ψ.
Proof with eauto.
  intros. forwards*: d_inftapp_wft.
Qed.

Corollary d_inftapp_wft_1 : forall Ψ A B C,
    d_inftapp Ψ A B C -> Ψ ⊢ A.
Proof with eauto.
  intros. forwards*: d_inftapp_wft.
Qed.

Corollary d_inftapp_wft_2 : forall Ψ A B C,
    d_inftapp Ψ A B C -> Ψ ⊢ B.
Proof with eauto.
  intros. forwards*: d_inftapp_wft.
Qed.

Corollary d_inftapp_wft_3 : forall Ψ A B C,
    d_inftapp Ψ A B C -> Ψ ⊢ C.
Proof with eauto.
  intros. forwards*: d_inftapp_wft.
Qed.

#[export] Hint Immediate d_inftapp_wft_0 d_inftapp_wft_1 d_inftapp_wft_2 d_inftapp_wft_3 : core.

#[local] Hint Constructors d_inftapp : core.

Lemma d_inftapp_subenv : forall Ψ Ψ' A B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  d_subenv Ψ' Ψ ->
  Ψ' ⊢ A ○ B ⇒⇒ C.
Proof with auto with typing;
eauto using d_subenv_wf_env, d_subenv_wf_typ.
  intros * HA HE.
  induction HA; intuition eauto...
Qed.

Corollary d_inftapp_subsumption: forall Ψ Ψ' A A' B C,
  Ψ ⊢ A ○ B ⇒⇒ C ->
  Ψ ⊢ A' <: A ->
  d_subenv Ψ' Ψ ->
  exists C', Ψ ⊢ C' <: C /\ Ψ' ⊢ A' ○ B ⇒⇒ C'.
Proof with eauto.
  intros * HA HS HE.
  forwards (?&?&HA'): d_inftapp_subsumption_same_env HA HS.
  forwards : d_inftapp_subenv HA' HE.
  exists*.
Qed.

Hint Constructors d_infabs : typing.


Lemma d_infabs_wft : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C ->
  ⊢ Ψ /\ Ψ ⊢ A /\ Ψ ⊢ B /\ Ψ ⊢ C.
Proof.
  intros. induction H; intuition.
Qed.

Corollary d_infabs_wft_0 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> ⊢ Ψ.
Proof.
  intros. forwards*: d_infabs_wft H.
Qed.

Corollary d_infabs_wft_1 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> Ψ ⊢ A.
Proof.
  intros. forwards*: d_infabs_wft H.
Qed.

Corollary d_infabs_wft_2 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> Ψ ⊢ B.
Proof.
  intros. forwards*: d_infabs_wft H.
Qed.

Corollary d_infabs_wft_3 : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> Ψ ⊢ C.
Proof.
  intros. forwards*: d_infabs_wft H.
Qed.

#[export] Hint Immediate d_infabs_wft_0 d_infabs_wft_1 d_infabs_wft_2 d_infabs_wft_3 : core.

(* @shengyi:todo *** *)
Theorem d_infabs_subsumption_same_env : forall Ψ A A' B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ⊢ A' <: A ->
  exists B' C', Ψ ⊢ typ_arrow B' C' <: typ_arrow B C /\ Ψ ⊢ A' ▹ B' → C'.
Proof with auto using d_mono_typ_d_wf_typ with typing.
  intros. generalize dependent A'. induction H; intros.
  - dependent induction H0...
    + exists typ_top typ_bot. auto...
    + exfalso. eapply d_sub_open_mono_bot_false; eauto.
  - dependent induction H2...
    + exists typ_top typ_bot. dependent destruction H2.
      eauto...
    + exists A1 A2. intuition...
      apply d_sub_dwft in H2_.
      apply d_sub_dwft in H2_0.
      intuition...
    + specialize (IHd_sub _ _ H H0 H1 (eq_refl _)).
      destruct IHd_sub as [B2 [C2]].
      exists B2 C2; intuition...
      econstructor. eauto. auto...
      * pick fresh Y and apply d_wf_typ__all.
         ** forwards: H4 Y...
         ** forwards: d_sub_dwft_1 H2.
            rewrite_env (nil++Ψ) in H6.
            forwards*: d_wf_typ_open_tvar_subst_mono H6.
      * eauto.
  - dependent induction H3.
    + exists typ_top typ_bot.
      econstructor; eauto...
    + assert (Ψ ⊢ A0 ^^ᵈ T <: A ^^ᵈ T). {
        pick fresh SZ. forwards*: H5 SZ.
        rewrite_env (nil++ (SZ, ▪) :: Ψ ) in H7.
        forwards*: d_sub_subst_stvar T H7.
        simpl in H8.
        rewrite subst_tvar_in_typ_open_typ_wrt_typ in H8...
        simpl in H8. case_if in H8.
        rewrite subst_tvar_in_typ_fresh_eq in H8...
        rewrite subst_tvar_in_typ_open_typ_wrt_typ in H8...
        simpl in H8. case_if in H8...
        rewrite subst_tvar_in_typ_fresh_eq in H8...
        all: eauto.
      }
      specialize (IHd_infabs _ H7).
      destruct IHd_infabs as [B2 [C2]].
      exists B2 C2. intuition...
      eapply d_infabs__all with (T:=T). eauto. eauto.
      pick fresh Y and apply d_wf_typ__all.
      ** forwards: H3 Y...
      ** forwards: d_sub_dwft_1 H7.
         rewrite_env (nil++Ψ) in H8.
         forwards*: d_wf_typ_open_tvar_subst_mono Y H8 H.
      ** eauto...
    + inversion H6.
Qed.


Lemma d_infabs_subenv : forall Ψ Ψ' A B C,
  Ψ ⊢ A ▹ B → C ->
  d_subenv Ψ' Ψ ->
  Ψ' ⊢ A ▹ B → C.
Proof with eauto using d_subenv_wf_env, d_subenv_wf_typ with typing.
  intros * HA HE.
  induction HA; intuition eauto...
  eapply d_infabs__all with (T:=T); eauto using d_mono_typ_subenv.
Qed.

Corollary d_infabs_subsumption: forall Ψ Ψ' A A' B C,
  Ψ ⊢ A ▹ B → C ->
  Ψ ⊢ A' <: A ->
  d_subenv Ψ' Ψ ->
  exists B' C', Ψ ⊢ typ_arrow B' C' <: typ_arrow B C /\ Ψ' ⊢ A' ▹ B' → C'.
Proof with eauto.
  intros * HA HS HE.
  forwards (?&?&HA'): d_infabs_subsumption_same_env HA HS.
  forwards : d_infabs_subenv HA' HE.
  exists*.
Qed.

Hint Extern 1 (_ < _) => lia : typing.
Hint Extern 1 (_ ⊢ _) => eapply d_subenv_wf_typ; eauto : typing.


Lemma d_exp_size_open_var_rec : forall e x n,
  exp_size e = exp_size (open_exp_wrt_exp_rec n (exp_var_f x) e)
with d_body_size_open_var_rec: forall b x n,
  body_size b = body_size (open_body_wrt_exp_rec n (exp_var_f x) b).
Proof.
  - intros. generalize dependent n. induction e; simpl; auto.
    + intros. destruct (lt_eq_lt_dec n n0).
      * destruct s; auto.
      * auto.
  - intros. generalize dependent n. induction b; simpl; auto.
Qed.


Lemma d_exp_size_open_var: forall e x,
  exp_size e = exp_size (open_exp_wrt_exp e (exp_var_f x)).
Proof.
  intros. unfold open_exp_wrt_exp.
  apply d_exp_size_open_var_rec.
Qed.


Lemma d_exp_size_open_typ_rec : forall e A n,
  exp_size e = exp_size (open_exp_wrt_typ_rec n A e)
with d_body_size_open_typ_rec: forall b A n,
  body_size b = body_size (open_body_wrt_typ_rec n A b).
Proof.
  - intros. generalize dependent n. induction e; simpl; auto.
  - intros. generalize dependent n. induction b; simpl; auto.
Qed.


Lemma d_exp_size_open_typ: forall e A,
  exp_size e = exp_size (open_exp_wrt_typ e A).
Proof.
  intros. unfold open_exp_wrt_exp.
  apply d_exp_size_open_typ_rec.
Qed.


Lemma d_chk_inf_wf_env: forall Ψ e mode A,
  d_typing Ψ e mode A ->
  ⊢ Ψ.
Proof.
  intros. induction H; auto.
  - inst_cofinites_by L. inversion H1; auto.
  - inst_cofinites_by L. inversion H1; auto.
  - inst_cofinites_by L. inversion H0; auto.
  - inst_cofinites_by L. inversion H1; auto.
Qed.

Lemma d_chk_inf_wft: forall Ψ e mode A,
  d_typing Ψ e mode A ->
  Ψ ⊢ A.
Proof.
  intros. induction~ H.
  - induction H; try solve_by_invert.
    all: forwards[(?&Heq)|?]: binds_cons_1 H0; try inverts Heq; subst; eauto.
  - apply d_infabs_wft in H0; intuition.
  - apply d_inftapp_wft in H1; intuition.
  - apply d_mono_typ_d_wf_typ; auto.
  - pick fresh X. forwards*: H1 X.
    rewrite_env (nil ++ (X, dbind_typ A1) :: Ψ ) in H2.
    forwards*: d_wf_typ_strengthen_var H2.
  - eauto using d_sub_dwft_2.
Qed.

#[export] Hint Resolve d_sub_dwft_0 d_sub_dwft_1 d_sub_dwft_2 : subtyping.

Theorem d_chk_inf_rename : forall Ψ1 Ψ2 x y T e A mode, 
  d_typing (Ψ2 ++ x ~ T ++ Ψ1) e mode A ->
  y `notin` (dom Ψ1 `union` dom Ψ2) ->
  d_typing (Ψ2 ++ y ~ T ++ Ψ1) (subst_var_in_exp (exp_var_f y) x e) mode A 
  .
Proof.
  intros. dependent induction H.
  - simpl. case_if; admit.
  - simpl. econstructor. admit.
    apply IHd_typing; auto.
  - simpl. apply d_typing__inf_unit. admit.
  - simpl. eapply d_typing__infapp; eauto.
    apply IHd_typing1; auto.
    admit.
    apply IHd_typing2; auto.
  - simpl. eapply d_typing__inftabs with (L:=L `union` singleton y); eauto.
    admit.
    intros. inst_cofinites_with X.
    rewrite_env ((X ~ ▫ ++ Ψ2) ++ (y, T) :: Ψ1).
    replace (exp_anno (open_exp_wrt_typ ({exp_var_f y /ᵉ x} e) ` X) (A ^ᵈ X)) with 
            ({exp_var_f y /ᵉ x} exp_anno (open_exp_wrt_typ e ` X) (A ^ᵈ X)).
    eapply H1; auto.
    simpl. rewrite subst_var_in_exp_open_exp_wrt_typ; auto.
  - simpl. eapply d_typing__inftapp; eauto.
    admit.
    eapply IHd_typing; eauto.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.


Theorem d_chk_inf_rename_cons : forall Ψ1 x y T e A mode, 
  d_typing (x ~ T ++ Ψ1) e mode A ->
  y `notin` (dom Ψ1) ->
  d_typing (y ~ T ++ Ψ1) (subst_var_in_exp (exp_var_f y) x e) mode A 
  .
Proof.
  intros.
  rewrite_env (nil ++ y ~ T ++ Ψ1).
  eapply  d_chk_inf_rename; eauto.
Qed.



Theorem d_chk_inf_subsumption : forall n1 n2 Ψ Ψ' e A mode,
  exp_size e < n1 ->
  dmode_size mode < n2 ->
  d_typing Ψ e mode A ->
  d_subenv Ψ' Ψ ->
    match mode with
    | typingmode__chk => forall A', Ψ ⊢ A <: A' -> Ψ' ⊢ e ⇐ A'
    | typingmode__inf => exists A', Ψ ⊢ A' <: A /\ Ψ' ⊢ e ⇒ A'
    end.
Proof with auto with typing.
  intro n1; induction n1; intro n2; induction n2; intros * Hn1 Hn2 Hty Hsubenv.
  - inversion Hn1.
  - inversion Hn1.
  - inversion Hn2.
  - destruct mode.
    (* e => A *)
    + dependent destruction Hty; simpl in Hn1, Hn2.
      * eapply d_subenv_same_var in Hsubenv as Hsubenvvar; eauto.
        destruct Hsubenvvar as [S1 [Hbind Hsub]]. exists S1; intuition.
        constructor. auto...
        eapply d_subenv_wf_env with (Ψ:=Ψ); eauto.
        auto.
      (* e : A => A *)
      * exists A. split; auto. apply dsub_refl; auto.
        now eauto using d_chk_inf_wf_env.
        econstructor. eapply d_subenv_wf_typ; eauto.
        refine (IHn1 _ _ _ _ _ _ _ _ Hty _ _ _); eauto... simpl in *...
        apply dsub_refl; auto.
        now eauto using d_chk_inf_wf_env.
      (* () => 1 *)
      * exists typ_unit. split; auto.
        econstructor. eapply d_subenv_wf_env; eauto.
      (* e1 e2 => A *)
      * eapply IHn1 in Hty1; eauto...
        destruct Hty1 as [A2]. inversion H0.
        eapply d_infabs_subsumption in H; eauto.
        destruct H as [B2 [C2]].
        exists C2; intuition.
        dependent destruction H0...
        dependent destruction H0...
        econstructor; eauto...
        refine (IHn1 _ _ _ _ _ _ _ _  Hty2 _ _ _); eauto...
      (* d_infabs_subsumption @shengyi:todo *** *)
      (* /\ a. e : A => forall a. A *)
      * exists (typ_all A); split.
        -- eapply dsub_refl; auto.
           now eauto using d_chk_inf_wf_env.
        -- dependent destruction H.
           pick fresh X and apply d_typing__inftabs.
           ++ econstructor. now applys H.
              intros. eapply d_subenv_wf_typ. now applys H0.
              auto...
           ++ intros. inst_cofinites_with X.
              refine (IHn1 _ _ _ _ _ _ _ _ H1 _ _ _); eauto...
              simpl. rewrite <- d_exp_size_open_typ; lia.
              apply dsub_refl.
              now applys d_chk_inf_wf_env H1. auto.
      (* e @T *)
      * eapply IHn1 in Hty; eauto...
        destruct Hty as [A1 [Hsuba1 Hinfa1]].
        eapply d_inftapp_subsumption in H0; eauto.
        destruct H0 as [C2 Hc2].
        exists C2. intuition...
        econstructor; eauto...
      * exists (typ_arrow A B).
        inst_cofinites_by (L `union` dom Ψ `union` fvar_in_exp e).
        eapply IHn1 with (Ψ':=x ~ dbind_typ A ++ Ψ') in H0 as Hty; eauto... 
        -- split. eapply dsub_refl; auto.
           ++ assert (x ~ dbind_typ A ++ Ψ ⊢ B <: B). 
              apply dsub_refl...
              now apply d_chk_inf_wf_env in H0.
              dependent destruction H.
              apply d_mono_typ_d_wf_typ in H0.
              apply d_wf_typ_weaken_cons...
              apply d_chk_inf_wf_env in H0. dependent destruction H0...
           ++ apply d_mono_typ_d_wf_typ...
           ++ eapply d_typing__infmonoabs with (L:=L `union` dom Ψ').
              eapply d_mono_typ_subenv; eauto.
              intros.
              replace (open_exp_wrt_exp e (exp_var_f x0)) with ({exp_var_f x0 /ᵉ x} open_exp_wrt_exp e (exp_var_f x)).
              apply d_chk_inf_rename_cons. apply Hty; eauto. 
              ** apply dsub_refl. eapply d_chk_inf_wf_env; eauto.
                 dependent destruction H. apply d_mono_typ_d_wf_typ in H0.
                 apply d_wf_typ_weaken_cons...
              ** solve_notin. 
              ** simpl. rewrite subst_var_in_exp_open_exp_wrt_exp...
                 rewrite (subst_var_in_exp_fresh_eq e); eauto...
                 simpl. case_if; auto...
        -- rewrite <- d_exp_size_open_var. lia.
        -- econstructor...
           apply dsub_refl...
           apply d_chk_inf_wf_env in H0. dependent destruction H0...
           apply d_mono_typ_d_wf_typ in H. dependent destruction H...
    (* e <= *)
    + dependent destruction Hty; simpl in Hn1, Hn2.
      (* \x. e <= Top *)
      * intros.
        dependent induction H0; eauto...
        -- eapply d_typing__chkabstop with (L:=L `union` dom Ψ)... intros.
           inst_cofinites_with x.
           simpl in H.
           refine (IHn1 _ _ _ _ _ _ _ _ H _ _ _); eauto...
           rewrite <- d_exp_size_open_var. lia.
           econstructor; auto.
           econstructor. econstructor; eauto.
           econstructor.
      (* \x. e <= T1 -> T2 *)
      * intros. dependent destruction H1.
        -- inst_cofinites_for d_typing__chkabstop. intros.
          inst_cofinites_with x.
          refine (IHn1 _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
          rewrite <- d_exp_size_open_var. lia.
          econstructor; eauto.
          inverts H2. eauto using d_wf_typ_weaken_cons.
        -- inst_cofinites_for d_typing__chkabs.
          eauto using d_subenv_wf_typ, d_sub_dwft_1.
          intros. inst_cofinites_with x.
          refine (IHn1 _ _ _ _ _ _ _ _ H0 _ _ _); eauto...
          rewrite <- d_exp_size_open_var. lia.
          applys~ d_sub_weaken_cons.
          applys d_chk_inf_wf_env H0.
      (* e <= forall a. A *)
      (*  * admit. ignore for now *** *)
      (* e <= A *)
      * intros.
        eapply IHn2 in Hty; eauto.
        destruct Hty as [A'' [Hsub Hinf]].
        apply d_typing__chksub with (B := A''); auto.
        apply sub_transitivity with (B := B); auto...
        eapply d_sub_subenv; eauto. apply sub_transitivity with (B := A); auto...
        eapply d_sub_subenv; eauto.
        eapply d_sub_subenv; eauto.
        simpl. lia.
Qed.

Corollary d_chk_subsumption : forall Ψ e A A',
  ⊢ Ψ ->
  Ψ ⊢ e ⇐ A ->
  Ψ ⊢ A <: A' ->
  Ψ ⊢ e ⇐ A'.
Proof.
  intros.
  refine (d_chk_inf_subsumption _ _ _ _ _ _ _ _ _ H0 _ _ _); eauto.
  now apply d_subenv_refl.
Qed.