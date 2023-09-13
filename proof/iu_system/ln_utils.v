
Require Export Metalib.Metatheory.

Require Import decl.notations.
(* Require Import algo.notations. *)


Notation "x ∉ L" := (x `notin` L)
  (at level 65, no associativity).


Ltac inst_cofinite_impl H x :=
  match type of H with
  | forall x, x `notin` ?L -> _ =>
      let Fr := fresh "Fr" in
      assert (x `notin` L) as Fr by auto;
      specialize (H x Fr); clear Fr
  end
.


Ltac inst_cofinites_with x :=
  repeat
    match goal with
    | H : forall x0, x0 `notin` ?L -> _ |- _ =>
      inst_cofinite_impl H x
    end
.

Ltac inst_cofinites :=
  match goal with
  | x : atom |- _ => inst_cofinites_with x
  end.

Ltac inst_cofinites_with_new :=
  let x := fresh "x" in
  pick fresh x; inst_cofinites_with x.

Ltac inst_cofinites_by F :=
  let L := F in
  let x := fresh "x" in
  pick fresh x for L; inst_cofinites_with x.
  
Tactic Notation "inst_cofinites_by" constr(F) :=
  let x := fresh "x" in let L:=F in pick fresh x for L; inst_cofinites_with x.
Tactic Notation "inst_cofinites_by" constr(L) "use_name" ident(x) := 
  pick fresh x for L; inst_cofinites_with x.


(* Ltac rewrite_la_subst_open_var :=
  repeat
    match goal with 
      | _ : _ |-  context [ ([?e /ᵃ ?x] ?A) ^ᵃ ?x' ] => 
        replace (`ᵃ x') with ([ e /ᵃ x ] (`ᵃ x')) by (apply subst_la_type_fresh_eq; auto)
    end; repeat rewrite <- subst_la_type_open_la_type_wrt_la_type by auto.


Ltac rewrite_ld_subst_open_var :=
  repeat
    match goal with 
      | _ : _ |-  context [ ([?e /ᵈ ?x] ?A) ^ᵈ ?x' ] => 
        replace (`ᵈ x') with ([ e /ᵈ x ] `ᵈ x') by (apply subst_ld_type_fresh_eq; auto)
    end; repeat rewrite <- subst_ld_type_open_ld_type_wrt_ld_type by auto. *)
