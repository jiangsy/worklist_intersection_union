Require Import FSets.
Require Import Bool.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
Require Import List.

Require Import algo_new.ott.


Ltac solve_eq_or_not :=
  match goal with
  | e : eq ?x1 ?x2 |- _ => left; rewrite e; auto
  | e : ~ eq ?x1 ?x2 |- _ => right; unfold not; intros Hcontra; dependent destruction Hcontra; contradiction
  end.

Lemma type_eq_dec : forall t1 t2 : la_type, {t1 = t2} + {t1 <> t2}.
Proof.
  intros.
  dependent induction t1; dependent induction t2; auto;
  try (right; unfold not; intros Hcontra; inversion Hcontra; fail).
  - specialize (IHt1 t2). destruct IHt1; solve_eq_or_not.
  - specialize (IHt1_1 t2_1). destruct IHt1_1.
    + specialize (IHt1_2 t2_2). destruct IHt1_2.
      * left. rewrite e. rewrite e0. auto.
      * right. intro. inversion H. contradiction.
    + solve_eq_or_not. 
  - destruct (n == n0); solve_eq_or_not.
  - destruct (x5 == x0); solve_eq_or_not.
  - destruct (ex5 == ex0); solve_eq_or_not.
Qed.

Module LAType_as_DT <: DecidableType.
  Definition t := la_type.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec := type_eq_dec.
  
End LAType_as_DT.

Module B := FSetExtra.Make LAType_as_DT.

