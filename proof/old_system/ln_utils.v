
Require Export Metalib.Metatheory.

Require Import uni.notations.
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



Fixpoint ftvar_in_aworklist' (aW_5:aworklist) : vars :=
  match aW_5 with
  | aworklist_empty => {}
  | (aworklist_consvar aW x ab) => (ftvar_in_aworklist' aW) \u (ftvar_in_abind ab)
  | (aworklist_constvar aW X ab) => (ftvar_in_aworklist' aW) \u (ftvar_in_abind ab) \u (singleton X)
  | (aworklist_conswork aW w) => (ftvar_in_aworklist' aW) \u (ftvar_in_work w)
end.


Fixpoint fvar_in_aworklist' (aW_5:aworklist) : vars :=
  match aW_5 with
  | aworklist_empty => {}
  | (aworklist_consvar aW x ab) => (fvar_in_aworklist' aW) \u (singleton x) (* no var in abind *)
  | (aworklist_constvar aW X ab) => (fvar_in_aworklist' aW) (* no var in abind *)
  | (aworklist_conswork aW w) => (fvar_in_aworklist' aW) \u (fvar_in_work w)
end.
  

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x : denv => dom x) in
  (* let C2 := gather_atoms_with (fun x : list (atom * dbind) => dom x) in *)
  let D1 := gather_atoms_with (fun x => ftvar_in_typ x) in
  let D2 := gather_atoms_with (fun x => ftvar_in_cont x) in
  let D3 := gather_atoms_with (fun x => ftvar_in_work x) in
  let D4 := gather_atoms_with (fun x => ftvar_in_aworklist' x) in
  (* let D3 := gather_atoms_with (fun x => fv_typ_in_binding x) in *)
  (* let D4 := gather_atoms_with (fun x => fv_exp_in_exp x) in *)
  constr:(A \u B \u C \u D1 \u D2 \u D3 \u D4).

  
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

(* 

Tactic Notation "pick" "fresh" ident(x) "and" "apply" constr(H) "for" "weaken" :=
  apply_fresh_base_fixed H gather_for_weaken x. *)
