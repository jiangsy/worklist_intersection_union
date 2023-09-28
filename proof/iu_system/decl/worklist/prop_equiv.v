Require Import Coq.Program.Equality.

Require Import decl.def_ott.
Require Import decl.worklist.def.


Hint Constructors d_wl_red : dworklist.
Hint Constructors d_wl_del_red : dworklist.

Theorem d_wl_red_sound: forall W, 
    d_wf_wl W -> d_wl_red W -> d_wl_del_red W.
Proof with auto with dworklist.
  intros. induction H0; try solve [dependent destruction H; auto with dworklist].
Admitted.

Theorem d_wl_red_complete: forall W, 
    d_wf_wl W -> d_wl_del_red W -> d_wl_red W.
Proof.
Admitted.


