Require Import decl.def_ott.
Require Import decl.worklist.def.

Theorem d_wl_red_sound: forall W, 
    d_wf_wl W -> d_wl_red W -> d_wl_del_red W.
Proof.
  intros. induction H0.
  - inversion H.
Admitted.

Theorem d_wl_red_complete: forall W, 
    d_wf_wl W -> d_wl_del_red W -> d_wl_red W.
Proof.
Admitted.


