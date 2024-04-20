
Require Export Metalib.Metatheory.

Require Import uni.notations.
Require Export LibTactics.
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
Tactic Notation "inst_cofinites_by" constr(L) "using_name" ident(x) := 
  let x := fresh x in pick fresh x for L; inst_cofinites_with x.

Ltac solve_notin_eq X :=
  let H := fresh "H" in
    assert (H: X `notin` singleton X) by auto;
    apply notin_singleton_1 in H; contradiction.

  
Ltac destruct_eq_atom :=
  unfold eq_dec in *;
  repeat
    lazymatch goal with
    | H : context [EqDec_eq_of_X ?X ?X] |- _ => destruct (EqDec_eq_of_X X X); [ idtac | contradiction]
    | H : _ |- context [EqDec_eq_of_X ?X ?X] => destruct (EqDec_eq_of_X X X); [ idtac | contradiction]
    | H : context [EqDec_eq_of_X ?X0 ?X] |- _ => destruct (EqDec_eq_of_X X0 X); subst;
        try contradiction; try solve_notin_eq X0; try solve_notin_eq X
    | H : _ |- context [EqDec_eq_of_X ?X0 ?X] => destruct (EqDec_eq_of_X X0 X); subst;
        try contradiction; try solve_notin_eq X0; try solve_notin_eq X
    end.

Ltac auto_apply :=
  match goal with
  | H : context [ ?P -> ?Q ] |- ?Q => apply H
  end.


Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C1 := gather_atoms_with (fun x : denv => dom x) in
  let C2 := gather_atoms_with (fun x : aenv => dom x) in
  (* let C2 := gather_atoms_with (fun x : list (atom * dbind) => dom x) in *)
  let D1 := gather_atoms_with (fun x => ftvar_in_typ x) in
  let D2 := gather_atoms_with (fun x => ftvar_in_exp x) in
  let D3 := gather_atoms_with (fun x => ftvar_in_conts x) in
  let D4 := gather_atoms_with (fun x => ftvar_in_contd x) in
  let D5 := gather_atoms_with (fun x => ftvar_in_work x) in
  let D6 := gather_atoms_with (fun x => favar_in_aworklist x) in

  let E1 := gather_atoms_with (fun x => fvar_in_exp x) in

  let F1 :=  gather_atoms_with (fun x => dom (awl_to_aenv x)) in
  let F2 :=  gather_atoms_with (fun x => dom (dwl_to_denv x)) in
  (* let D3 := gather_atoms_with (fun x => fv_typ_in_binding x) in *)
  (* let D4 := gather_atoms_with (fun x => fv_exp_in_exp x) in *)
  constr:(A \u B \u C1 \u C2 \u D1 \u D2 \u D3 \u D4 \u D5 \u D6 \u E1 \u F1 \u F2).

Ltac solve_wf_twl_sub_false :=
  match goal with
  | H : (∃ A B : typ, work_sub ?A' ?B' = work_sub A B) → False |- _ => exfalso; eauto
  | _ : _ |- _ => idtac
  end.
(* Ltac apply_fresh_base_fixed H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  let x := fresh atom_name in
  pick fresh x excluding L and apply H. *) 

Tactic Notation "inst_cofinites_for" constr(H) := 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1).

Tactic Notation "inst_cofinites_for" constr(H) ident(name)":="constr(Args1) := 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1) (name:=Args1).

Tactic Notation "inst_cofinites_for" constr(H) ident(argname1)":="constr(arg1) "," ident(argname2) ":=" constr(arg2):= 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1) (argname1:=arg1) (argname2:=arg2).

(* destruct conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
                         lazymatch T with
                         | exists _ , _ => destruct H
                         | _ /\ _ => destruct H
                         end
    end.


Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Create HintDb FalseHd.
Ltac solve_false := let HF := fresh "HF" in
                    try solve [ try intro HF; destruct_conj; try solve_by_invert;
                                false; eauto 3 with FalseHd ].

                              
(* 

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weaken" :=
  apply_fresh_base_fixed H gather_for_weaken x. *)
