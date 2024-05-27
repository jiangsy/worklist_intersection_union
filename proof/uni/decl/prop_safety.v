Require Import Coq.Program.Equality.

Require Import systemf.def_ott.
Require Import systemf.prop_ln.
Require Import systemf.prop_basic.

Require Import uni.def_ott.
Require Import uni.decl.def_extra.
Require Import uni.prop_basic.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.
Require Import uni.notations.
Require Import uni.ltac_utils.

Open Scope dbind.

Notation "Ψ ⊢ e : A" :=
  (f_typing Ψ e A) 
    (at level 65, e at next level, no associativity) : type_scope.

Fixpoint trans_typ (A : typ) : ftyp :=
  match A with
  | typ_unit => ftyp_unit
  | typ_top => ftyp_unit
  | typ_bot => ftyp_all (ftyp_var_b 0)
  | typ_var_b n => ftyp_var_b n
  | typ_var_f X => ftyp_var_f X
  | typ_arrow A1 A2 => ftyp_arrow (trans_typ A1) (trans_typ A2)
  | typ_all A => ftyp_all (trans_typ A)
  | typ_union A1 A2 => ftyp_sum (trans_typ A1) (trans_typ A2)
  | typ_intersection A1 A2 => ftyp_prod (trans_typ A1) (trans_typ A2) 
  end.

Notation "ᵗ⟦  A  ⟧" := (trans_typ A) (at level 0, no associativity) : type_scope.

Fixpoint trans_env (Ψ : denv) : fenv :=
  match Ψ with
  | nil => nil
  | (X, dbind_tvar_empty) :: Ψ' => (X, fbind_tvar_empty) :: trans_env Ψ'
  | (X, dbind_stvar_empty) :: Ψ' => (X, fbind_tvar_empty) :: trans_env Ψ'
  | (X, (dbind_typ T)) :: Ψ' => (X, (fbind_typ (trans_typ T))) :: trans_env Ψ'
  end.

Notation "⟦ Ψ ⟧" := (trans_env Ψ) (at level 0, no associativity) : type_scope.

Lemma trans_typ_open_typ_wrt_typ_rec : forall A1 A2 n,
  trans_typ (open_typ_wrt_typ_rec n A2 A1) = open_ftyp_wrt_ftyp_rec n ᵗ⟦ A2 ⟧ ᵗ⟦ A1 ⟧.
Proof.
  intros A1. induction A1; auto; intros; simpl.
  - destruct (lt_eq_lt_dec n n0) as [[? | ?] | ?] eqn:Ψ; auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
  - rewrite IHA1. auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
  - rewrite IHA1_1. rewrite IHA1_2. auto.
Qed.


Theorem trans_typ_open_typ_wrt_typ : forall A1 A2,
  trans_typ (A1 ᵗ^^ₜ A2) = open_ftyp_wrt_ftyp (trans_typ A1) (trans_typ A2).
Proof.
  unfold open_typ_wrt_typ. unfold open_ftyp_wrt_ftyp.
  intros. apply trans_typ_open_typ_wrt_typ_rec.
Qed.

Theorem trans_typ_lc_ftyp : forall (A:typ),
  lc_typ A -> lc_ftyp (trans_typ A).
Proof.
  intros. induction H; simpl; eauto.
  - apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. eauto.
  - apply lc_ftyp_all. intros.
    rewrite <- trans_typ_open_typ_wrt_typ with (A2 := (typ_var_f X)).
    auto.
Qed.

#[local] Hint Resolve trans_typ_lc_ftyp : core.

Theorem trans_env_notin_dom : forall Ψ X,
  X `notin` dom Ψ -> X `notin` dom ⟦ Ψ ⟧.
Proof.
  intros Ψ. induction Ψ; auto.
  intros X H. destruct a. destruct d; simpl in *; auto.
Qed.

#[local] Hint Resolve trans_env_notin_dom : core.

Theorem trans_env_tvar_in : forall (Ψ:denv) X,
  X ~ □ ∈ᵈ Ψ -> binds X fbind_tvar_empty (trans_env Ψ).
Proof.
  intros. induction Ψ; auto.
  destruct a; destruct d; destruct_binds; auto.
Qed.


Theorem trans_env_stvar_in : forall (Ψ:denv) X,
  X ~ ■ ∈ᵈ Ψ -> binds X fbind_tvar_empty (trans_env Ψ).
Proof.
  intros. induction Ψ; auto.
  destruct a; destruct d; destruct_binds; auto.
Qed.


Theorem trans_typ_wf : forall Ψ A,
  Ψ ᵗ⊢ᵈ A -> f_wf_typ (trans_env Ψ) (trans_typ A).
Proof.
  intros. induction H; simpl; eauto...
  - apply f_wf_typ__all with (L:=dom Ψ).
    intros. apply trans_env_notin_dom in H.
    unfold open_ftyp_wrt_ftyp. simpl. auto.
  - apply f_wf_typ__tvar. apply trans_env_tvar_in. auto.
  - apply f_wf_typ__tvar. apply trans_env_stvar_in. auto.
  - apply f_wf_typ__all with (L:= L `union` dom Ψ). 
    intros. inst_cofinites_with X.
    rewrite trans_typ_open_typ_wrt_typ in H1. auto.
Qed.

Theorem trans_env_wf_tenv_wf_fenv : forall Ψ,
  ⊢ᵈₜ Ψ -> f_wf_env ⟦ Ψ ⟧.
Proof with eauto using trans_typ_wf.
  intros. induction H; simpl; eauto...
  constructor...
  constructor... 
Qed.

Theorem trans_env_wf_env_wf_fenv : forall Ψ,
  ⊢ᵈ Ψ -> f_wf_env ⟦ Ψ ⟧.
Proof with eauto using trans_env_wf_tenv_wf_fenv.
  intros. induction H; simpl; eauto;
  try solve [apply trans_env_notin_dom in H0; apply wf_env_sub; auto]...
  constructor...
Qed.


Inductive d_sub_elab : denv -> typ -> typ -> fexp -> Prop :=
  | d_sub_elab__top : forall (Ψ:denv) (A:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ A ->
      d_sub_elab Ψ A typ_top (fexp_abs (trans_typ A) fexp_unit)
  | d_sub_elab__bot : forall (Ψ:denv) (B:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ B ->
      d_sub_elab Ψ typ_bot B (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_tapp (fexp_var_b 0) (trans_typ B)))
  | d_sub_elab__unit : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_sub_elab Ψ typ_unit typ_unit (fexp_abs ftyp_unit (fexp_var_b 0))
  | d_sub_elab__tvar : forall (Ψ:denv) (X:typvar),
      d_wf_env Ψ ->
      d_wf_typ Ψ (typ_var_f X) ->
      d_sub_elab Ψ (typ_var_f X) (typ_var_f X) (fexp_abs (ftyp_var_f X) (fexp_var_b 0))
  | d_sub_elab__arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ) (co1ᶠ co2ᶠ:fexp),
      d_sub_elab Ψ B1 A1 co1ᶠ ->
      d_sub_elab Ψ A2 B2 co2ᶠ ->
      d_sub_elab Ψ (typ_arrow A1 A2) (typ_arrow B1 B2)
        (fexp_abs (ftyp_arrow (trans_typ A1) (trans_typ A2))
                  (fexp_abs (trans_typ B1)
                            (fexp_app co2ᶠ
                                      (fexp_app (fexp_var_b 1)
                                                (fexp_app co1ᶠ (fexp_var_b 0))))))
  | d_sub_elab__all : forall (L:vars) (Ψ:denv) (A B:typ) (coᶠ:fexp),
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  B   (typ_var_f X) ) ) ->
      ( forall X , X \notin L -> d_sub_elab  ( X ~ dbind_stvar_empty  ++  Ψ )   (open_typ_wrt_typ  A   (typ_var_f X) )   (open_typ_wrt_typ  B   (typ_var_f X) ) (open_fexp_wrt_ftyp coᶠ (ftyp_var_f X)) ) ->
      d_sub_elab Ψ (typ_all A) (typ_all B)
        (fexp_abs (trans_typ (typ_all A)) (fexp_tabs (fexp_app coᶠ (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0)))))
  | d_sub_elab__alll : forall (L:vars) (Ψ:denv) (A B T:typ) (coᶠ:fexp),
      neq_all B ->
      neq_intersection B ->
      neq_union B -> 
      ( forall X , X \notin L -> s_in X  (open_typ_wrt_typ  A   (typ_var_f X) ) ) ->
      d_mono_typ Ψ T ->
      d_sub_elab Ψ  (open_typ_wrt_typ  A   T )  B coᶠ ->
      d_sub_elab Ψ (typ_all A) B
        (fexp_abs (trans_typ (typ_all A)) (fexp_app coᶠ (fexp_tapp (fexp_var_b 0) (trans_typ T))))
  | d_sub_elab__intersection1 : forall (Ψ:denv) (A B1 B2:typ) (co1ᶠ co2ᶠ:fexp),
      d_sub_elab Ψ A B1 co1ᶠ ->
      d_sub_elab Ψ A B2 co2ᶠ ->
      d_sub_elab Ψ A (typ_intersection B1 B2)
        (fexp_abs (trans_typ A)
                  (fexp_pair (fexp_app co1ᶠ (fexp_var_b 0))
                          (fexp_app co2ᶠ (fexp_var_b 0))))
  | d_sub_elab__intersection2 : forall (Ψ:denv) (A1 A2 B:typ) (coᶠ:fexp),
      d_sub_elab Ψ A1 B coᶠ ->
      d_wf_typ Ψ A2 ->
      d_sub_elab Ψ (typ_intersection A1 A2) B
        (fexp_abs (trans_typ (typ_intersection A1 A2)) (fexp_app coᶠ (fexp_proj1 (fexp_var_b 0))))
  | d_sub_elab__intersection3 : forall (Ψ:denv) (A1 A2 B:typ) (coᶠ:fexp),
      d_sub_elab Ψ A2 B coᶠ ->
      d_wf_typ Ψ A1 ->
      d_sub_elab Ψ (typ_intersection A1 A2) B
        (fexp_abs (trans_typ (typ_intersection A1 A2)) (fexp_app coᶠ (fexp_proj2 (fexp_var_b 0))))
  | d_sub_elab__union1 : forall (Ψ:denv) (A B1 B2:typ) (coᶠ:fexp),
      d_sub_elab Ψ A B1 coᶠ ->
      d_wf_typ Ψ B2 ->
      d_sub_elab Ψ A (typ_union B1 B2)
        (fexp_abs (trans_typ A) (fexp_inl (fexp_app coᶠ (fexp_var_b 0))))
  | d_sub_elab__union2 : forall (Ψ:denv) (A B1 B2:typ) (coᶠ:fexp),
      d_sub_elab Ψ A B2 coᶠ ->
      d_wf_typ Ψ B1 ->
      d_sub_elab Ψ A (typ_union B1 B2)
        (fexp_abs (trans_typ A) (fexp_inr (fexp_app coᶠ (fexp_var_b 0))))
  | d_sub_elab__union3 : forall (Ψ:denv) (A1 A2 B:typ) (co1ᶠ co2ᶠ:fexp),
      d_sub_elab Ψ A1 B co1ᶠ ->
      d_sub_elab Ψ A2 B co2ᶠ ->
      d_sub_elab Ψ (typ_union A1 A2) B
        (fexp_abs (trans_typ (typ_union A1 A2)) (fexp_case (fexp_var_b 0) (fexp_app co1ᶠ (fexp_var_b 0)) (fexp_app co2ᶠ (fexp_var_b 0)))).

Notation "Ψ ⊢ A <: B ↪ coᶠ" := (d_sub_elab Ψ A B coᶠ) (at level 65, A at next level, B at next level, no associativity) : type_scope.

Inductive d_infabs_elab : denv -> typ -> typ -> typ -> fexp -> Prop := 
  | infabs_elab_bot : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_infabs_elab Ψ typ_bot typ_top typ_bot
        (fexp_abs (ftyp_all (ftyp_var_b 0))
              (fexp_tapp (fexp_var_b 0) (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0)))))
  | infabs_elab_arr : forall (Ψ:denv) (A B:typ),
      d_wf_env Ψ ->
      d_wf_typ Ψ A ->
      d_wf_typ Ψ B ->
      d_infabs_elab Ψ (typ_arrow A B) A B
        (fexp_abs (trans_typ (typ_arrow A B)) (fexp_var_b 0))
  | infabs_elab_all : forall (Ψ:denv) (A B C T:typ) (coᶠ:fexp),
      d_mono_typ Ψ T -> 
      d_wf_typ Ψ (typ_all A) ->
      d_infabs_elab Ψ  (open_typ_wrt_typ  A   T ) B C coᶠ ->
      d_infabs_elab Ψ (typ_all A) B C
        (fexp_abs (trans_typ (typ_all A))
                  (fexp_app coᶠ (fexp_tapp (fexp_var_b 0) (trans_typ T))))
  | infabs_elab_intersection1 : forall (Ψ:denv) (A1 A2 B C:typ) (coᶠ:fexp),
      d_wf_typ Ψ A2 ->
      d_infabs_elab Ψ A1 B C coᶠ ->
      d_infabs_elab Ψ (typ_intersection A1 A2) B C
        (fexp_abs (trans_typ (typ_intersection A1 A2))
                  (fexp_app coᶠ (fexp_proj1 (fexp_var_b 0))))
  | infabs_elab_intersection2 : forall (Ψ:denv) (A1 A2 B C:typ) (coᶠ:fexp),
      d_wf_typ Ψ A1 ->
      d_infabs_elab Ψ A2 B C coᶠ ->
      d_infabs_elab Ψ (typ_intersection A1 A2) B C
        (fexp_abs (trans_typ (typ_intersection A1 A2))
                  (fexp_app coᶠ (fexp_proj2 (fexp_var_b 0))))
  | infabs_elab_union : forall (Ψ:denv) (A1 A2 B1 C1 B2 C2:typ) (co1ᶠ co2ᶠ:fexp),
      d_infabs_elab Ψ A1 B1 C1 co1ᶠ ->
      d_infabs_elab Ψ A2 B2 C2 co2ᶠ ->
      d_infabs_elab Ψ (typ_union A1 A2) (typ_intersection B1 B2) (typ_union C1 C2)
        (fexp_abs (trans_typ (typ_union A1 A2))
                  (fexp_abs (trans_typ (typ_intersection B1 B2))
                            (fexp_case (fexp_var_b 1)
                                      (fexp_inl (fexp_app co1ᶠ (fexp_proj1 (fexp_var_b 1))))
                                      (fexp_inr (fexp_app co2ᶠ (fexp_proj2 (fexp_var_b 1))))))).

Notation "Ψ ⊢ A ▹ B → C ↪ coᶠ" :=   (d_infabs_elab Ψ A B C coᶠ) 
  (at level 65, A at next level, B at next level, C at next level, no associativity) : type_scope.
                            
Inductive d_inftapp_elab : denv -> typ -> typ -> typ -> fexp -> fexp -> Prop := 
  | inftapp_elab_bot : forall (Ψ:denv) (B:typ),
      d_wf_env Ψ -> 
      d_wf_typ Ψ B ->
      d_inftapp_elab Ψ typ_bot B typ_bot
        (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_var_b 0))
        (fexp_abs (ftyp_all (ftyp_var_b 0)) (fexp_var_b 0))
  | inftapp_elab_all : forall (Ψ:denv) (A B:typ),
      d_wf_env Ψ -> 
      d_wf_typ Ψ (typ_all A) ->
      d_wf_typ Ψ B ->
      d_inftapp_elab Ψ (typ_all A) B (open_typ_wrt_typ  A   B )  
        (fexp_abs (trans_typ (typ_all A)) (fexp_var_b 0))
        (fexp_abs (trans_typ (typ_all A)) (fexp_tapp (fexp_var_b 0) (trans_typ B)))
  | inftapp_elab_intersection1 : forall (Ψ:denv) (A1 A2 B C1:typ) (co1ᶠ co2ᶠ:fexp),
      d_wf_typ Ψ A2 ->
      d_inftapp_elab Ψ A1 B C1 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ (typ_intersection A1 A2) B C1
        (fexp_abs (trans_typ (typ_intersection A1 A2))
                  (fexp_app co1ᶠ (fexp_proj1 (fexp_var_b 0))))
        co2ᶠ
  | inftapp_elab_intersection2 : forall (Ψ:denv) (A1 A2 B C2:typ) (co1ᶠ co2ᶠ:fexp),
      d_wf_typ Ψ A1 ->
      d_inftapp_elab Ψ A2 B C2 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ (typ_intersection A1 A2) B C2
        (fexp_abs (trans_typ (typ_intersection A1 A2))
                  (fexp_app co1ᶠ (fexp_proj2 (fexp_var_b 0))))
        co2ᶠ
  | inftapp_elab_intersection3 : forall (Ψ:denv) (A1 A2 B C1 C2:typ) (co1ᶠ co2ᶠ co3 co4:fexp),
      d_inftapp_elab Ψ A1 B C1 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ A2 B C2 co3 co4 ->
      d_inftapp_elab Ψ (typ_intersection A1 A2) B (typ_intersection C1 C2)
        (fexp_abs (trans_typ (typ_intersection A1 A2))
                  (fexp_pair (fexp_app co2ᶠ (fexp_app co1ᶠ (fexp_proj1 (fexp_var_b 0))))
                              (fexp_app co4 (fexp_app co3 (fexp_proj2 (fexp_var_b 0))))))
        (fexp_abs (trans_typ ((typ_intersection C1 C2))) (fexp_var_b 0))
  | inftapp_elab_union : forall (Ψ:denv) (A1 A2 B C1 C2:typ) (co1ᶠ co2ᶠ co3 co4:fexp),
      d_inftapp_elab Ψ A1 B C1 co1ᶠ co2ᶠ ->
      d_inftapp_elab Ψ A2 B C2 co3 co4 ->
      d_inftapp_elab Ψ (typ_union A1 A2) B (typ_union C1 C2)
        (fexp_abs (trans_typ (typ_union A1 A2))
                  (fexp_case (fexp_var_b 0)
                              (fexp_inl (fexp_app co2ᶠ (fexp_app co1ᶠ (fexp_var_b 0))))
                              (fexp_inr (fexp_app co4 (fexp_app co3 (fexp_var_b 0))))))
        (fexp_abs (trans_typ (typ_union C1 C2)) (fexp_var_b 0)).

Notation "Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ" :=
    (d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ) 
      (at level 65, A at next level, B at next level, C at next level, no associativity) : type_scope. 


Inductive d_chk_inf_elab : denv -> exp -> typing_mode -> typ -> fexp -> Prop :=
  | d_chk_inf_elab__inf_var : forall (Ψ:denv) (x:expvar) (A:typ),
      d_wf_env Ψ ->
      binds ( x )  ( (dbind_typ A) ) ( Ψ )  ->
      d_chk_inf_elab Ψ (exp_var_f x) typingmode__inf A
        (fexp_var_f x)
  | d_chk_inf_elab__inf_anno : forall (Ψ:denv) (e:exp) (B1:typ) (eᶠ:fexp),
      d_wf_typ Ψ B1 ->
      d_chk_inf_elab Ψ e typingmode__chk B1 eᶠ ->
      d_chk_inf_elab Ψ  ( (exp_anno e B1) )  typingmode__inf B1 eᶠ
  | d_chk_inf_elab__inf_unit : forall (Ψ:denv),
      d_wf_env Ψ ->
      d_chk_inf_elab Ψ exp_unit typingmode__inf typ_unit
        fexp_unit
  | d_chk_inf_elab__inf_app : forall (Ψ:denv) (e1 e2:exp) (A B C:typ) (e1ᶠ coᶠ e2ᶠ:fexp),
      d_chk_inf_elab Ψ e1 typingmode__inf A e1ᶠ ->
      d_infabs_elab Ψ A B C coᶠ ->
      d_chk_inf_elab Ψ e2 typingmode__chk B e2ᶠ ->
      d_chk_inf_elab Ψ  ( (exp_app e1 e2) ) typingmode__inf C
        (fexp_app (fexp_app coᶠ e1ᶠ) e2ᶠ)
  | d_chk_inf_elab__inf_abs_mono : forall (L:vars) (Ψ:denv) (e:exp) (A B:typ) (eᶠ:fexp),
      d_mono_typ Ψ (typ_arrow A B) ->
      ( forall x , x \notin  L  -> d_chk_inf_elab  ( x ~ (dbind_typ A)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk B (open_fexp_wrt_fexp eᶠ (fexp_var_f x)))  ->
      d_chk_inf_elab Ψ (exp_abs e) typingmode__inf (typ_arrow A B)
        (fexp_abs (trans_typ A) eᶠ)
  | d_chk_inf_elab__inf_tabs : forall (L:vars) (Ψ:denv) (e:exp) (A:typ) (eᶠ:fexp),
      ( forall X , X \notin  L  -> s_in X (open_typ_wrt_typ A (typ_var_f X)))  ->
      ( forall X , X \notin  L  -> d_chk_inf_elab  ( X ~ dbind_tvar_empty  ++  Ψ ) (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) )  ( open_typ_wrt_typ A (typ_var_f X) ) ) typingmode__chk ( open_typ_wrt_typ A (typ_var_f X) ) (open_fexp_wrt_ftyp eᶠ (ftyp_var_f X)))  ->
      d_chk_inf_elab Ψ (exp_tabs (exp_anno e A)) typingmode__inf (typ_all A)
        (fexp_tabs eᶠ)
  | d_chk_inf_elab__inf_tapp : forall (Ψ:denv) (e:exp) (A B C:typ) (eᶠ co1ᶠ co2ᶠ:fexp),
      d_wf_typ Ψ B ->
      d_chk_inf_elab Ψ e typingmode__inf A eᶠ ->
      d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ ->
      d_chk_inf_elab Ψ (exp_tapp e B) typingmode__inf C
        (fexp_app co2ᶠ (fexp_app co1ᶠ eᶠ))
  | d_chk_inf_elab__chk_abs_top : forall (L:vars) (Ψ:denv) (e:exp) (eᶠ:fexp),
      ( forall x , x \notin  L  -> d_chk_inf_elab  ( x ~ (dbind_typ typ_bot)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk typ_top (open_fexp_wrt_fexp eᶠ (fexp_var_f x)))  ->
      d_chk_inf_elab Ψ (exp_abs e) typingmode__chk typ_top fexp_unit
  | d_chk_inf_elab__chk_abs : forall (L:vars) (Ψ:denv) (e:exp) (A B:typ) (eᶠ:fexp),
      d_wf_typ Ψ A ->
      ( forall x , x \notin  L  -> d_chk_inf_elab  ( x ~ (dbind_typ A)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk B (open_fexp_wrt_fexp eᶠ (fexp_var_f x)))  ->
      d_chk_inf_elab Ψ (exp_abs e) typingmode__chk (typ_arrow A B)
        (fexp_abs (trans_typ A) eᶠ)
  | d_chk_inf_elab__chk_sub : forall (Ψ:denv) (e:exp) ( A B:typ) (eᶠ coᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__inf A eᶠ ->
      d_sub_elab Ψ A B coᶠ ->
      d_chk_inf_elab Ψ e typingmode__chk B
        (fexp_app coᶠ eᶠ)
  | d_chk_inf_elab__chk_intersection : forall (Ψ:denv) (e:exp) (A1 A2:typ) (e1ᶠ e2ᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__chk A1 e1ᶠ ->
      d_chk_inf_elab Ψ e typingmode__chk A2 e2ᶠ ->
      d_chk_inf_elab Ψ e typingmode__chk (typ_intersection A1 A2)
        (fexp_pair e1ᶠ e2ᶠ)
  | d_chk_inf_elab__chk_union1 : forall (Ψ:denv) (e:exp) (A1 A2:typ) (eᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__chk A1 eᶠ ->
      d_wf_typ Ψ A2 ->
      d_chk_inf_elab Ψ e typingmode__chk (typ_union A1 A2)
        (fexp_inl eᶠ)
  | d_chk_inf_elab__chk_union2 : forall (Ψ:denv) (e:exp) (A1 A2:typ) (eᶠ:fexp),
      d_chk_inf_elab Ψ e typingmode__chk A2 eᶠ ->
      d_wf_typ Ψ A1 ->
      d_chk_inf_elab Ψ e typingmode__chk (typ_union A1 A2)
        (fexp_inr eᶠ).


#[local] Hint Constructors d_sub_elab d_inftapp_elab d_infabs_elab d_chk_inf_elab : core.
#[local] Hint Constructors f_typing : core.


Theorem d_sub_elab_sound: forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> Ψ ⊢ A <: B.
Proof.
  intros. induction H; eauto.
Qed.

Lemma trans_typ_rename_tvar : forall A X Y,
  subst_typ_in_ftyp (ftyp_var_f Y) X ᵗ⟦ A ⟧ = ᵗ⟦ {`Y ᵗ/ₜ X} A ⟧.
Proof.
  intros. induction A; simpl; eauto.
  - destruct_eq_atom; auto.
  - rewrite IHA1. rewrite IHA2. auto.
  - rewrite IHA. auto.
  - rewrite IHA1. rewrite IHA2. auto.
  - rewrite IHA1. rewrite IHA2. auto. 
Qed.


Lemma d_sub_elab_rename_dtvar : forall Ψ1 Ψ2 A B b X Y coᶠ,
  b = □ \/ b = ■ ->
  Ψ2 ++ (X , b) :: Ψ1  ⊢ A <: B ↪ coᶠ ->
  Y ∉ (dom (Ψ2 ++ (X, b) :: Ψ1)) ->
  (map (subst_tvar_in_dbind `Y X) Ψ2) ++ (Y , b) :: Ψ1  ⊢ {`Y ᵗ/ₜ X} A <: {`Y ᵗ/ₜ X} B ↪ subst_typ_in_fexp (ftyp_var_f Y) X coᶠ.
Proof with eauto 6 using d_wf_typ_rename_dtvar, d_wf_env_rename_dtvar.
  intros. dependent induction H0; eauto; try solve [simpl; repeat rewrite trans_typ_rename_tvar; eauto 6 using d_wf_typ_rename_dtvar, d_wf_env_rename_dtvar].
  - simpl. destruct_eq_atom; auto.
    + econstructor; eauto... destruct H; eauto.
    + econstructor; eauto... admit.
  - simpl. repeat rewrite trans_typ_rename_tvar.
    replace (ftyp_all ᵗ⟦ {` Y ᵗ/ₜ X} A ⟧) with (ᵗ⟦ typ_all ( {` Y ᵗ/ₜ X} A ) ⟧) by auto.
    inst_cofinites_for d_sub_elab__all; intros; inst_cofinites_with X0; auto.
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      admit.
  - simpl. repeat rewrite trans_typ_rename_tvar.
    inst_cofinites_for d_sub_elab__alll; intros; inst_cofinites_with X0; eauto...
    + rewrite subst_tvar_in_typ_open_typ_wrt_typ_fresh2...
      apply s_in_subst_inv...
    + eapply d_mono_typ_rename_dtvar...
      apply d_sub_elab_sound in H4. apply d_sub_d_wf_env in H4...
    + rewrite <- subst_tvar_in_typ_open_typ_wrt_typ...
  - simpl; repeat rewrite trans_typ_rename_tvar... econstructor...
  - simpl; repeat rewrite trans_typ_rename_tvar... econstructor...
  - simpl; repeat rewrite trans_typ_rename_tvar... econstructor...
Admitted.

Lemma d_sub_elab_rename_tvar_cons : forall Ψ A B X Y coᶠ b,
  b = □ \/ b = ■ ->
  Y `notin` dom ((X, b) :: Ψ) ->
  (X , b) :: Ψ ⊢ A <: B ↪ coᶠ ->
  (Y , b) :: Ψ ⊢ {`Y ᵗ/ₜ X} A <: {`Y ᵗ/ₜ X} B ↪ subst_typ_in_fexp (ftyp_var_f Y) X coᶠ.
Proof.
  intros. rewrite_env ((map (subst_tvar_in_dbind `Y X) nil) ++ (Y , b) :: Ψ). 
  eapply d_sub_elab_rename_dtvar; eauto.
Qed.

Theorem d_sub_elab_complete: forall Ψ A B,
  Ψ ⊢ A <: B -> exists coᶠ, Ψ ⊢ A <: B ↪ coᶠ.
Proof with auto.
  intros. induction H; eauto 4; try solve [destruct_conj; eauto 4].
  - pick fresh X. inst_cofinites_with_keep X.
    destruct H3 as [coᶠ ?].
    exists 
      (fexp_abs (trans_typ (typ_all A)) (fexp_tabs (fexp_app (close_fexp_wrt_ftyp X coᶠ) (fexp_tapp (fexp_var_b 0) (ftyp_var_b 0))))).
    inst_cofinites_for d_sub_elab__all; intros; inst_cofinites_with X0; auto.
    erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2 with (X:=X)...
    erewrite <- subst_tvar_in_typ_open_typ_wrt_typ_tvar2 with (X:=X) (A:=B)...
    erewrite (subst_typ_in_fexp_intro X (close_fexp_wrt_ftyp X coᶠ)) by apply close_fexp_wrt_ftyp_notin.
    + rewrite open_fexp_wrt_ftyp_close_fexp_wrt_ftyp.
      eapply d_sub_elab_rename_tvar_cons; eauto.
Qed.
      
Theorem sub_elab_lc_fexp : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> lc_fexp coᶠ.
Proof with eauto 4.
  intros. induction H...
  - apply lc_fexp_abs...
    + apply lc_ftyp_all. intros.
      unfold open_ftyp_wrt_ftyp. simpl. auto.
    + intros. unfold open_fexp_wrt_fexp. simpl...
  - apply lc_fexp_abs; auto. 
    intros. unfold open_fexp_wrt_fexp. simpl. auto. 
  (* 
  - apply lc_fexp_abs...
    + apply lc_ftyp_all. intros.
      unfold open_ftyp_wrt_ftyp. simpl. auto.
    + intros. unfold open_fexp_wrt_fexp. simpl...

  - apply lc_fexp_abs; auto. 
    intros. unfold open_fexp_wrt_fexp. simpl. auto.
  - apply lc_fexp_abs; auto. 
    intros. unfold open_fexp_wrt_fexp. simpl. auto.
  - apply sub_elab_sound in H. apply sub_elab_sound in H0.
    apply d_sub_d_wf in H. apply d_sub_d_wf in H0.
    destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
    apply lc_fexp_abs.
    + apply lc_ftyp_arrow; eauto with safety.
    + intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - admit.
  - admit.
  - apply sub_elab_sound in H. apply sub_elab_sound in H0.
    apply d_sub_d_wf in H. apply d_sub_d_wf in H0.
    destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H.
    apply d_sub_d_wf in H.
    destruct H as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply sub_elab_sound in H. apply sub_elab_sound in H0.
    apply d_sub_d_wf in H. apply d_sub_d_wf in H0.
    destruct H as [_ [? ?]]. destruct H0 as [_ [? ?]].
    apply lc_fexp_abs; eauto with safety.
    intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply lc_fexp_case; eauto with safety; intros;
    unfold open_fexp_wrt_fexp; simpl;
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto. *)
Admitted.
      
Theorem d_sub_elab_sound_f : forall Ψ A B coᶠ,
  Ψ ⊢ A <: B ↪ coᶠ -> ⟦ Ψ ⟧ ⊢ coᶠ : ftyp_arrow ᵗ⟦ A ⟧ ᵗ⟦ B ⟧.
Proof with eauto 4.
  intros. induction H...
Admitted.


Theorem d_infabs_complete : forall Ψ A B C,
  Ψ ⊢ A ▹ B → C -> exists coᶠ, Ψ ⊢ A ▹ B → C ↪ coᶠ.
Proof.
Admitted.


Theorem d_infabs_elab_sound_f : forall Ψ A B C coᶠ,
  Ψ ⊢ A ▹ B → C ↪ coᶠ -> 
  ⟦ Ψ ⟧ ⊢ coᶠ : ftyp_arrow ᵗ⟦ A ⟧ (ftyp_arrow ᵗ⟦ B ⟧ ᵗ⟦ C ⟧).
Proof.
Admitted.


Theorem d_inftapp_elab_complete : forall Ψ A B C,
  Ψ ⊢ A ○ B ⇒⇒ C -> exists co1ᶠ co2ᶠ, Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ.
Proof.
Admitted.

Theorem d_inftapp_elab_sound_f : forall Ψ A B C co1ᶠ co2ᶠ,
  Ψ ⊢ A ○ B ⇒⇒ C ↪ co1ᶠ | co2ᶠ ->
  exists D : ftyp, ⟦ Ψ ⟧ ⊢ co1ᶠ : ftyp_arrow ᵗ⟦ A ⟧ D /\ ⟦ Ψ ⟧ ⊢ co2ᶠ : ftyp_arrow D ᵗ⟦ C ⟧.
Proof.
Admitted.

Theorem d_chk_inf_elab_lc_fexp : forall Ψ e A eᶠ mode,
  d_chk_inf_elab Ψ e mode A eᶠ -> lc_fexp eᶠ.
Proof.
  intros. induction H; eauto; simpl.
Admitted.


Theorem d_chk_inf_elab_complete : forall Ψ e mode A,
  d_chk_inf Ψ e mode A -> exists eᶠ, d_chk_inf_elab Ψ e mode A eᶠ.
Proof.
Admitted. 


Theorem d_chk_inf_elab_sound_f : forall Ψ e A eᶠ mode,
  d_chk_inf_elab Ψ e mode A eᶠ -> ⟦ Ψ ⟧ ⊢ eᶠ : ᵗ⟦ A ⟧.
Proof.
Admitted.

(* 


Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_tapp with (B1:=ftyp_var_b 0); eauto with safety.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
    apply trans_typ_wf with (Ψ:=Ψ) (T:=typ_all (typ_var_b 0)).
    apply dwftyp_all with (L:=dom Ψ); unfold open_typ_wrt_typ; simpl; auto.
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
    apply trans_typ_wf with (T:=typ_var_f X); auto.
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; eauto.
    apply wf_env_typ; eauto with safety.
    apply trans_typ_wf with (T:=typ_var_f SX); auto.
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_abs with (L:=dom Ψ `union` singleton x).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc1: lc_fexp C1).
    { apply sub_elab_lc_fexp in H. auto. }
    assert (Hlc2: lc_fexp C2).
    { apply sub_elab_lc_fexp in H0. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A2).
    + admit. (* weaken *)
    + apply typing_app with (B1:=trans_typ A1).
    * apply typing_var; auto.
      admit. (* wf *)
    * apply typing_app with (B1:=trans_typ B1).
      -- admit. (* weaken *)
      -- apply typing_var; auto.
       admit. (* wf *)
  - apply typing_abs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_tabs with (L:=L `union` dom Ψ `union` singleton x).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H1. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    repeat rewrite open_fexp_wrt_ftyp_rec_lc_fexp;
    try rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    replace (ftyp_var_f X) with (trans_typ (typ_var_f X)); auto.
    apply typing_app with (B1:=trans_typ (A1 ᵗ^^ₜ typ_var_f X)).
    + rewrite <- trans_typ_open_typ_wrt_typ with (B1:=B1) (B2:=typ_var_f X).
    admit. (* weaken *)
    + rewrite trans_typ_open_typ_wrt_typ.
    apply typing_tapp; eauto with safety.
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H5. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ (A1 ᵗ^^ₜ B2)).
    + admit. (* weaken *)
    + rewrite trans_typ_open_typ_wrt_typ.
    apply typing_tapp; eauto with safety.
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc1: lc_fexp C1).
    { apply sub_elab_lc_fexp in H. auto. }
    assert (Hlc2: lc_fexp C2).
    { apply sub_elab_lc_fexp in H0. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_pair.
    + apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_var; auto.
        admit. (* wf *)
    + apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_var; auto.
        admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A1).
    + admit. (* weaken *) 
    + apply typing_proj1 with (B2:=trans_typ A2).
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A2).
    + admit. (* weaken *) 
    + apply typing_proj2 with (B1:=trans_typ A1).
    apply typing_var; auto.
    admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_inl.
    + eapply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_var; auto.
        admit. (* wf *)
    + admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc: lc_fexp C).
    { apply sub_elab_lc_fexp in H. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_inr.
    + eapply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_var; auto.
        admit. (* wf *)
    + admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    intros. unfold open_fexp_wrt_fexp. simpl.
    assert (Hlc1: lc_fexp C1).
    { apply sub_elab_lc_fexp in H. auto. }
    assert (Hlc2: lc_fexp C2).
    { apply sub_elab_lc_fexp in H0. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp;
    try rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_case with (B1:=trans_typ A1) (B2:=trans_typ A2)
               (L:=dom Ψ `union` singleton x).
    + apply typing_var; auto. admit. (* wf *) 
    + intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *) 
      * apply typing_var; auto.
        admit. (* wf *) 
    + intros. unfold open_fexp_wrt_fexp. simpl.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ A2).
      * admit. (* weaken *) 
      * apply typing_var; auto.
        admit. (* wf *) 
Admitted.


Lemma lc_ftyp_all_id : lc_ftyp (ftyp_all (ftyp_var_b 0)).
Proof.
  apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. auto.
Qed.

Hint Resolve lc_ftyp_all_id : safety.

Theorem infabs_elab_lc_fexp : forall Ψ A B C Co,
  d_infabs_elab Ψ A B C Co -> lc_fexp Co.
Proof.
  intros. induction H; eauto with safety;
  apply lc_fexp_abs; eauto with safety; simpl.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_tapp; eauto with safety.
  - unfold open_fexp_wrt_fexp. simpl. auto.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_app; eauto with safety.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply lc_ftyp_prod.
    + admit.
    + apply trans_typ_lc_ftyp. apply d_wf_typ_lc_typ with (Ψ:=Ψ); auto.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_app; eauto with safety.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
  - apply lc_ftyp_prod.
    + apply trans_typ_lc_ftyp. apply d_wf_typ_lc_typ with (Ψ:=Ψ); auto.
    + admit.
  - unfold open_fexp_wrt_fexp. simpl. intros.
    apply lc_fexp_app; eauto with safety.
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
Admitted.

Theorem infabs_sound_f : forall Ψ A B C Co,
  d_infabs_elab Ψ A B C Co ->
  typing (trans_env Ψ) Co (ftyp_arrow (trans_typ A) (ftyp_arrow (trans_typ B) (trans_typ C))).
Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    replace (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0))) with
        (open_ftyp_wrt_ftyp (ftyp_var_b 0)
                  (ftyp_arrow ftyp_unit (ftyp_all (ftyp_var_b 0)))) at 2; auto.
    apply typing_tapp.
    + apply lc_ftyp_arrow; auto.
    apply lc_ftyp_all. unfold open_ftyp_wrt_ftyp. simpl. auto.
    + apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp Co).
    { apply infabs_elab_lc_fexp in H2. auto. }
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ (open_typ_wrt_typ B1 B2)).
    + admit. (* weaken *)
    + rewrite trans_typ_open_typ_wrt_typ. apply typing_tapp.
      * apply trans_typ_lc_ftyp; auto.
      * apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp Co).
    { apply infabs_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ B1); auto.
    + admit. (* weaken *)
    + apply typing_proj1 with (B2:=trans_typ B2).
      apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc: lc_fexp Co).
    { apply infabs_elab_lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_app with (B1:=trans_typ B2); auto.
    + admit. (* weaken *)
    + apply typing_proj2 with (B1:=trans_typ B1).
      apply typing_var; auto. admit. (* wf *)
  - apply typing_abs with (L:=dom Ψ).
    unfold open_fexp_wrt_fexp. simpl. intros.
    assert (Hlc1: lc_fexp co1ᶠ).
    { apply infabs_elab_lc_fexp in H. auto. }
    assert (Hlc2: lc_fexp co2ᶠ).
    { apply infabs_elab_lc_fexp in H0. auto. }
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_abs with (L:=dom Ψ `union` singleton x).
    intros. unfold open_fexp_wrt_fexp. simpl.
    repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
    apply typing_case with
      (L:=dom Ψ `union` singleton x `union` singleton x0)
      (B1:=trans_typ B1) (B2:=trans_typ B2).
    + apply typing_var; auto. admit. (* wf *)
    + unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_inl.
      * apply typing_app with (B1:=trans_typ T3).
        -- admit. (* weaken *)
        -- apply typing_proj1 with (B2:=trans_typ T5).
           apply typing_var; auto. admit. (* wf *)
      * admit. (* wf *)
    + unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_inr.
      * apply typing_app with (B1:=trans_typ T5).
        -- admit. (* weaken *)
        -- apply typing_proj2 with (B1:=trans_typ T3).
           apply typing_var; auto. admit. (* wf *)
      * admit. (* wf *)
Admitted.



Theorem inftapp_elab_lc_fexp : forall Ψ A B C co1ᶠ co2ᶠ,
  d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ -> lc_fexp co1ᶠ /\ lc_fexp co2ᶠ.
Proof.
  intros. induction H; eauto with safety; simpl.
  - split; apply lc_fexp_abs; eauto with safety;
    unfold open_fexp_wrt_fexp; simpl; auto.
  - split; apply lc_fexp_abs; eauto with safety.
    + replace (ftyp_all (trans_typ B1)) with (trans_typ (typ_all B1)); eauto.
      apply trans_typ_lc_ftyp. eauto.
    + unfold open_fexp_wrt_fexp. simpl. auto.
    + replace (ftyp_all (trans_typ B1)) with (trans_typ (typ_all B1)); eauto.
      apply trans_typ_lc_ftyp. eauto.
    + unfold open_fexp_wrt_fexp. simpl. intros.
      apply lc_fexp_tapp; eauto. apply trans_typ_lc_ftyp. eauto. 
Admitted.

Theorem inftapp_sound_f : forall Ψ A B C co1ᶠ co2ᶠ,
  d_inftapp_elab Ψ A B C co1ᶠ co2ᶠ -> exists D,
  typing (trans_env Ψ) co1ᶠ (ftyp_arrow (trans_typ A) D) /\
    typing (trans_env Ψ) co2ᶠ (ftyp_arrow D (trans_typ C)).
Proof with eauto with safety.
  intros. induction H; simpl; eauto.
  - exists (ftyp_all (ftyp_var_b 0)). split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
  - exists (ftyp_all (trans_typ B1)). split.
    + apply typing_abs with (L:=dom Ψ).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      rewrite trans_typ_open_typ_wrt_typ.
      apply typing_tapp.
      * apply trans_typ_lc_ftyp. eauto.
      * apply typing_var; auto. admit. (* wf *)
  - inversion IHinftapp_elab. destruct H2.
    exists x. split.
    + apply typing_abs with (L:=dom Ψ).  
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply inftapp_elab_lc_fexp in H1. auto. }
      destruct Hlc as [Hlc1 Hlc2].
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (B1:=trans_typ A1).
      * admit. (* weaken *)
      * apply typing_proj1 with (B2:=trans_typ A2).
        apply typing_var; auto. admit. (* wf *)
    + auto.
  - inversion IHinftapp_elab. destruct H2.
    exists x. split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply inftapp_elab_lc_fexp in H1. auto. }
      destruct Hlc as [Hlc1 Hlc2].
      rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_app with (B1:=trans_typ A2).
      * admit. (* weaken *)
      * apply typing_proj2 with (B1:=trans_typ A1).
        apply typing_var; auto.  admit. (* wf *)
    + auto.
  - inversion IHinftapp_elab1. inversion IHinftapp_elab2.
    destruct H1. destruct H2.
    exists (trans_typ (typ_intersection C1 C2)). split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc12: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply inftapp_elab_lc_fexp in H. auto. }
      destruct Hlc12 as [Hlc1 Hlc2].
      assert (Hlc34: lc_fexp co3 /\ lc_fexp co4).
      { apply inftapp_elab_lc_fexp in H0. auto. }
      destruct Hlc34 as [Hlc3 Hlc4].
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_pair.
      * apply typing_app with (B1:=x).
        -- admit. (* weaken *) 
        -- apply typing_app with (B1:=trans_typ A1).
           ++ admit. (* weaken *)
           ++ apply typing_proj1 with (B2:=trans_typ A2).
              apply typing_var; auto. admit. (* wf *)
      * apply typing_app with (B1:=x0).
        -- admit. (* weaken *) 
        -- apply typing_app with (B1:=trans_typ A2).
           ++ admit. (* weaken *)
           ++ apply typing_proj2 with (B1:=trans_typ A1).
              apply typing_var; auto. admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)
  - inversion IHinftapp_elab1. inversion IHinftapp_elab2.
    destruct H1. destruct H2.
    exists (trans_typ (typ_union C1 C2)). split.
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      assert (Hlc12: lc_fexp co1ᶠ /\ lc_fexp co2ᶠ).
      { apply inftapp_elab_lc_fexp in H. auto. }
      destruct Hlc12 as [Hlc1 Hlc2].
      assert (Hlc34: lc_fexp co3 /\ lc_fexp co4).
      { apply inftapp_elab_lc_fexp in H0. auto. }
      destruct Hlc34 as [Hlc3 Hlc4].
      repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
      apply typing_case with (L:=dom Ψ `union` singleton x1)
        (B1:=trans_typ A1) (B2:=trans_typ A2).
      * apply typing_var; auto. admit. (* wf *)
      * unfold open_fexp_wrt_fexp. simpl. intros.
        repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_inl.
        -- apply typing_app with (B1:=x).
           ++ admit. (* weaken *) 
           ++ apply typing_app with (B1:=trans_typ A1).
              ** admit. (* weaken *)
              ** apply typing_var; auto. admit. (* wf *)
        -- admit. (* wf *)
      * unfold open_fexp_wrt_fexp. simpl. intros.
        repeat rewrite open_fexp_wrt_fexp_rec_lc_fexp; auto.
        apply typing_inr.
        -- apply typing_app with (B1:=x0).
           ++ admit. (* weaken *) 
           ++ apply typing_app with (B1:=trans_typ A2).
              ** admit. (* weaken *)
              ** apply typing_var; auto. admit. (* wf *)
        -- admit. (* wf *)
    + apply typing_abs with (L:=dom Ψ).
      unfold open_fexp_wrt_fexp. simpl. intros.
      apply typing_var; auto. admit. (* wf *)  
Admitted.


Theorem trans_binds : forall Ψ x T,
  binds x (dbind_typ T) Ψ -> binds x (bind_typ (trans_typ T)) (trans_env Ψ).
Proof.
  intros. induction Ψ; auto.
  inversion H.
  - subst. simpl. auto.
  - apply IHE in H0. destruct a.
    destruct b; simpl; auto.
Qed.

Theorem d_chk_inf_elab_lc_fexp : forall Ψ e A eᶠ mode,
  d_chk_inf_elab Ψ e mode A eᶠ -> lc_fexp eᶠ.
Proof.
  intros. induction H; eauto with safety; simpl.
Admitted.

Theorem typing_sound_f : forall Ψ e T C mode,
  d_chk_inf_elab Ψ e mode T C -> typing (trans_env Ψ) C (trans_typ T).
Proof.
  intros. induction H; simpl; eauto.
  - apply typing_var; auto. admit. (* wf *)
    apply trans_binds. auto.
  - apply typing_app with (B1:=trans_typ B2); auto.
    apply typing_app with (B1:=trans_typ B1); auto.
    apply infabs_sound_f; auto.
  - apply typing_tabs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X. assert (Hlc: lc_fexp C).
    { apply d_chk_inf_elab__lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    rewrite <- trans_typ_open_typ_wrt_typ with (B2:=typ_var_f X). auto.
  - apply inftapp_sound_f in H1. destruct H1. destruct H1.
    apply typing_app with (B1:=x); auto.
    apply typing_app with (B1:=trans_typ B1); auto.
  - apply typing_abs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with x. assert (Hlc: lc_fexp C).
    { apply d_chk_inf_elab__lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_fexp_lc_fexp; auto.
  - apply typing_tabs with (L:=L `union` dom Ψ).
    unfold open_fexp_wrt_ftyp. simpl. intros.
    inst_cofinites_with X. assert (Hlc: lc_fexp C).
    { apply d_chk_inf_elab__lc_fexp in H0. auto. }
    rewrite open_fexp_wrt_ftyp_rec_lc_fexp; auto.
    rewrite <- trans_typ_open_typ_wrt_typ with (B2:=typ_var_f X). auto.
  - eapply typing_app with (B1:=trans_typ A1); auto.
    apply sub_sound_f. auto.
Admitted. *)
