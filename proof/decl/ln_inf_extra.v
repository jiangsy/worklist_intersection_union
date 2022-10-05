Require Import decl.ott.
Require Export decl.notations.


Lemma ld_type_open_r_close_l : forall t1 t2 x
  , x `notin` fv_ld_type t2
  -> t1 = open_ld_type_wrt_ld_type t2 `x -> close_ld_type_wrt_ld_type x t1 = t2.
Proof.
  intros * Fr H.
  assert (close_ld_type_wrt_ld_type x t1 = close_ld_type_wrt_ld_type x (open_ld_type_wrt_ld_type t2 `x)) by now rewrite H.
  now rewrite close_ld_type_wrt_ld_type_open_ld_type_wrt_ld_type in H0.
Qed.