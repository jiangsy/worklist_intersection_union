(* Require Import Coq.Program.Equality.
Require Import Program.Tactics.
Require Import Lia.
Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import ln_utils.
Require Import uni.notations.
Require Import uni.decl.prop_basic.
Require Import uni.decl.prop_subtyping.

Inductive d_sub_alt : denv -> typ -> typ -> Prop :=    (* d_sub plus more side conditions *)
 | d_sub_alt__top : forall (Ψ:denv) (A:typ),
     d_wf_env Ψ ->
     d_wf_typ Ψ A ->
     d_sub_alt Ψ A typ_top
 | d_sub_alt__bot : forall (Ψ:denv) (B:typ),
     d_wf_env Ψ ->
     d_wf_typ Ψ B ->
     d_sub_alt Ψ typ_bot B
 | d_sub_alt__unit : forall (Ψ:denv),
     d_wf_env Ψ ->
     d_sub_alt Ψ typ_unit typ_unit
 | d_sub_alt__tvar : forall (Ψ:denv) (X:typvar),
     d_wf_env Ψ ->
     d_wf_typ Ψ (typ_var_f X) ->
     d_sub_alt Ψ (typ_var_f X) (typ_var_f X)
 | d_sub_alt__arrow : forall (Ψ:denv) (A1 A2 B1 B2:typ),
     d_sub_alt Ψ B1 A1 ->
     d_sub_alt Ψ A2 B2 ->
     d_sub_alt Ψ (typ_arrow A1 A2) (typ_arrow B1 B2)
 | d_sub_alt__all : forall (L:vars) (Ψ:denv) (A B:typ),
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ B (typ_var_f X) )  )  ->
      ( forall X , X \notin  L  -> d_sub_alt  ( X ~ dbind_stvar_empty  ++  Ψ )   ( open_typ_wrt_typ A (typ_var_f X) )   ( open_typ_wrt_typ B (typ_var_f X) )  )  ->
     d_sub_alt Ψ (typ_all A) (typ_all B)
 | d_sub_alt__alll : forall (L:vars) (Ψ:denv) (A B T:typ),
     B <> typ_top ->
     neq_all B ->
     neq_intersection B ->
     neq_union B ->
      ( forall X , X \notin  L  -> s_in X  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
     d_mono_typ Ψ T ->
     d_sub_alt Ψ  (open_typ_wrt_typ  A   T )  B ->
     d_sub_alt Ψ (typ_all A) B
 | d_sub_alt__intersection1 : forall (Ψ:denv) (A B1 B2:typ),
     A <> typ_bot ->
     d_sub_alt Ψ A B1 ->
     d_sub_alt Ψ A B2 ->
     d_sub_alt Ψ A (typ_intersection B1 B2)
 | d_sub_alt__intersection2 : forall (Ψ:denv) (A1 A2 B:typ),
     B <> typ_top ->
     d_sub_alt Ψ A1 B ->
     d_wf_typ Ψ A2 ->
     d_sub_alt Ψ (typ_intersection A1 A2) B
 | d_sub_alt__intersection3 : forall (Ψ:denv) (A1 A2 B:typ),
     B <> typ_top ->
     d_sub_alt Ψ A2 B ->
     d_wf_typ Ψ A1 ->
     d_sub_alt Ψ (typ_intersection A1 A2) B
 | d_sub_alt__union1 : forall (Ψ:denv) (A B1 B2:typ),
     A <> typ_bot ->
     d_sub_alt Ψ A B1 ->
     d_wf_typ Ψ B2 ->
     d_sub_alt Ψ A (typ_union B1 B2)
 | d_sub_alt__union2 : forall (Ψ:denv) (A B1 B2:typ),
     A <> typ_bot ->
     d_sub_alt Ψ A B2 ->
     d_wf_typ Ψ B1 ->
     d_sub_alt Ψ A (typ_union B1 B2)
 | d_sub_alt__union3 : forall (Ψ:denv) (A1 A2 B:typ),
     B <> typ_top ->
     d_sub_alt Ψ A1 B ->
     d_sub_alt Ψ A2 B ->
     d_sub_alt Ψ (typ_union A1 A2) B.


(* d_chk_inf plus more side conditions *)
Inductive d_typing_alt : denv -> exp -> typing_mode -> typ -> Prop :=
| d_typing_alt__infvar : forall (Ψ:denv) (x:expvar) (A:typ),
    d_wf_env Ψ ->
    binds ( x )  ( (dbind_typ A) ) ( Ψ )  ->
    d_typing_alt Ψ (exp_var_f x) typingmode__inf A
| d_typing_alt__infanno : forall (Ψ:denv) (e:exp) (A:typ),
    d_wf_typ Ψ A ->
    d_typing_alt Ψ e typingmode__chk A ->
    d_typing_alt Ψ  ( (exp_anno e A) )  typingmode__inf A
| d_typing_altinf_unit : forall (Ψ:denv),
    d_wf_env Ψ ->
    d_typing_alt Ψ exp_unit typingmode__inf typ_unit
| d_typing_alt__infapp : forall (Ψ:denv) (e1 e2:exp) (A B C:typ),
    d_typing_alt Ψ e1 typingmode__inf A ->
    d_infabs Ψ A B C ->
    d_typing_alt Ψ e2 typingmode__chk B ->
    d_typing_alt Ψ  ( (exp_app e1 e2) ) typingmode__inf C
| d_typing_alt__inftabs : forall (L:vars) (Ψ:denv) (e:exp) (A:typ),
    d_wf_typ Ψ (typ_all A) ->
    ( forall X , X \notin  L  -> d_typing_alt  ( X ~ dbind_tvar_empty  ++  Ψ ) (exp_anno  ( open_exp_wrt_typ e (typ_var_f X) )  ( open_typ_wrt_typ A (typ_var_f X) ) ) typingmode__chk ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
    d_typing_alt Ψ (exp_tabs (body_anno e A)) typingmode__inf (typ_all A)
| d_typing_alt__inftapp : forall (Ψ:denv) (e1:exp) (A B C:typ),
    d_wf_typ Ψ B ->
    d_typing_alt Ψ e1 typingmode__inf A ->
    d_inftapp Ψ A B C ->
    d_typing_alt Ψ (exp_tapp e1 B) typingmode__inf C
| d_typing_alt__chkabstop : forall (L:vars) (Ψ:denv) (e:exp),
    ( forall x , x \notin  L  -> d_typing_alt  ( x ~ (dbind_typ typ_bot)  ++  Ψ )   ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk typ_top )  ->
    d_typing_alt Ψ (exp_abs e) typingmode__chk typ_top
| d_typing_alt__chkabs : forall (L:vars) (Ψ:denv) (e:exp) (A1 A2:typ),
    d_wf_typ Ψ A1 ->
    ( forall x , x \notin  L  -> d_typing_alt  ( x ~ (dbind_typ A1)  ++  Ψ )  ( open_exp_wrt_exp e (exp_var_f x) ) typingmode__chk A2 )  ->
    d_typing_alt Ψ (exp_abs e) typingmode__chk (typ_arrow A1 A2)
(* | d_typing_alt__chkall : forall (L:vars) (Ψ:denv) (e:exp) (T1:typ),
    d_wf_typ Ψ (typ_all T1) ->
    ( forall X , X \notin  L  -> d_typing_alt  ( X ~ dbind_tvar_empty  ++  Ψ )  e  typingmode__chk ( open_typ_wrt_typ T1 (typ_var_f X) )  )  ->
    d_typing_alt Ψ e typingmode__chk (typ_all T1) *)
| d_typing_alt__chksub : forall (Ψ:denv) (e:exp) (A B:typ),
    neq_intersection A ->
    neq_union A ->
    (~ exists e', e = exp_abs e') ->
    d_typing_alt Ψ e typingmode__inf B ->
    d_sub_alt Ψ B A ->
    d_typing_alt Ψ e typingmode__chk A
| d_typing_alt__chkintersection : forall (Ψ:denv) (e:exp) (A1 A2:typ),
    d_typing_alt Ψ e typingmode__chk A1 ->
    d_typing_alt Ψ e typingmode__chk A2 ->
    d_typing_alt Ψ e typingmode__chk (typ_intersection A1 A2)
| d_typing_alt__chkunion1 : forall (Ψ:denv) (e:exp) (A1 A2:typ),
    d_typing_alt Ψ e typingmode__chk A1 ->
    d_wf_typ Ψ A2 ->
    d_typing_alt Ψ e typingmode__chk (typ_union A1 A2)
| d_typing_alt__chkunion2 : forall (Ψ:denv) (e:exp) (A1 A2:typ),
    d_typing_alt Ψ e typingmode__chk A2 ->
    d_wf_typ Ψ A1 ->
    d_typing_alt Ψ e typingmode__chk (typ_union A1 A2)
.

#[local] Hint Constructors d_sub_alt d_typing_alt : core.

Lemma d_sub_alt_sound : forall Ψ A B,
    d_sub_alt Ψ A B -> d_sub Ψ A B.
Proof with eauto.
  intros * HS. induction* HS.
Qed.

Lemma d_sub_alt_complete : forall Ψ A B,
    d_sub Ψ A B -> d_sub_alt Ψ A B.
Proof with eauto using d_sub_dwft_0, d_sub_dwft_1, d_sub_dwft_2.
  intros * HS. induction* HS.
  - (* forall l *)
    destruct B;
      try solve [ applys* d_sub_alt__alll;
                  intro HF; inverts HF ].
    + applys d_sub_alt__top...
  - (* intersection r *)
    destruct A;
      try solve [ applys* d_sub_alt__intersection1;
                  intro HF; inverts HF ].
    + applys d_sub_alt__bot...
  - (* intersection l *)
    destruct B;
      try solve [ applys* d_sub_alt__intersection2;
                  intro HF; inverts HF ].
    + applys d_sub_alt__top...
  - (* intersection l *)
    destruct B;
      try solve [ applys* d_sub_alt__intersection3;
                  intro HF; inverts HF ].
    + applys d_sub_alt__top...
  - (* union r *)
    destruct A;
      try solve [ applys* d_sub_alt__union1;
                  intro HF; inverts HF ].
    + applys d_sub_alt__bot...
  - (* union r *)
    destruct A;
      try solve [ applys* d_sub_alt__union2;
                  intro HF; inverts HF ].
    + applys d_sub_alt__bot...
  - (* union l *)
    destruct B;
      try solve [ applys* d_sub_alt__union3;
                  intro HF; inverts HF ].
    + applys d_sub_alt__top...
Qed.

Lemma d_typing_alt_sound : forall Ψ e dir A,
    d_typing_alt Ψ e dir A -> d_chk_inf Ψ e dir A.
Proof with eauto using d_sub_alt_sound.
  intros * HT. induction HT...
Qed.

Lemma d_sub_alt_dwft_1 : forall Ψ A B,
    d_sub_alt Ψ A B -> Ψ ⊢ A.
Proof with eauto using d_sub_alt_sound.
  intros. applys d_sub_dwft_1...
Qed.

Lemma d_sub_alt_dwft_2 : forall Ψ A B,
    d_sub_alt Ψ A B -> Ψ ⊢ B.
Proof with eauto using d_sub_alt_sound.
  intros. applys d_sub_dwft_2...
Qed.

Lemma d_sub_alt_union_l_inv : forall Ψ A1 A2 B,
    d_sub_alt Ψ (typ_union A1 A2) B ->
    d_sub_alt Ψ A1 B /\ d_sub_alt Ψ A2 B.
Proof with eauto.
  intros. apply d_sub_alt_sound in H.
  splits; applys d_sub_alt_complete; forwards * : dsub_union_inversion H.
Qed.

Lemma d_sub_alt_union_r_inv : forall Ψ A1 A2 B,
    d_sub_alt Ψ B (typ_union A1 A2) ->
    d_sub_alt Ψ B A1 \/ d_sub_alt Ψ B A2.
Proof with eauto.
  intros * HS. inductions HS.
Admitted.

Lemma d_sub_alt_intersection_r_inv : forall Ψ S1 T1 T2,
  d_sub_alt Ψ S1 (typ_intersection T1 T2) ->
  d_sub_alt Ψ S1 T1 /\ d_sub_alt Ψ S1 T2.
Proof with eauto.
  intros. apply d_sub_alt_sound in H.
  splits; applys d_sub_alt_complete; forwards * : dsub_intersection_inversion H.
Qed.

Lemma d_sub_alt_intersection_l_inv : forall Ψ A1 A2 B,
    d_sub_alt Ψ (typ_intersection A1 A2) B ->
    d_sub_alt Ψ A1 B /\ d_sub_alt Ψ A2 B.
Proof with eauto.
  intros * HS. inductions HS.
Admitted.

Lemma d_typing_alt_chksub_gen : forall (Ψ:denv) (e:exp) (A B:typ),
    d_typing_alt Ψ e typingmode__inf B ->
    d_sub_alt Ψ B A ->
    d_typing_alt Ψ e typingmode__chk A.
Proof with eauto using d_sub_alt_dwft_1, d_sub_alt_dwft_2.
  intros * HT HS.
  gen A B. induction A; intros.
  8: { (* union *)
    forwards: d_sub_alt_dwft_2 HS. inverts H.
    forwards [?|?]: d_sub_alt_union_r_inv HS.
    - forwards*: IHA1.
    - forwards*: IHA2.
  }
  8: { (* intersection *)
    forwards: d_sub_alt_dwft_2 HS. inverts H.
    forwards* (?&?): d_sub_alt_intersection_r_inv HS.
  }
  all: try solve [destruct e;
                  try solve [inverts HT];
                  try solve [applys* d_typing_alt__chksub; intro HF; inverts HF; inverts H];
                  applys* d_typing_alt__chksub; intro HF; inverts HF; inverts H].
  - (* ↑ n *)
    exfalso.
    forwards: d_sub_alt_dwft_2 HS. inverts H.
  - (* arrow *)
    forwards: d_sub_alt_dwft_2 HS. inverts H.
    destruct e.
    all: try solve [inverts HT];
      try solve [applys* d_typing_alt__chksub; intro HF; inverts HF; inverts H].
  - (* forall *)
    forwards: d_sub_alt_dwft_2 HS. inverts H.
    pick fresh x. inst_cofinites_with x.
    destruct e.
    all: try solve [inverts HT];
      try solve [applys* d_typing_alt__chksub;
                 try econstructor;
                 try eapply lc_typ_all_exists; eauto; intro HF; inverts HF; inverts H].
Qed.


Lemma d_typing_alt_complete : forall Ψ e dir A,
    d_chk_inf Ψ e dir A -> d_typing_alt Ψ e dir A.
Proof with eauto using d_sub_alt_complete.
  intros * HT. induction HT.
  9: applys* d_typing_alt_chksub_gen...
  all: now eauto.
Qed. *)
