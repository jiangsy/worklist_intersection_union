
Require Import uni.decl.prop_typing.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.prop_soundness.
Require Import uni.algo_worklist.prop_completeness.
(* Require Import uni.algo_worklist.prop_decidability. *)

(* Prop of decl system *)
Check d_chk_inf_subsumption.
Print Assumptions d_chk_inf_subsumption.

(* Prop of decl worklist system *)
Check d_wl_red_sound.
Print Assumptions d_wl_red_sound.
Check d_wl_red_complete.
Print Assumptions d_wl_red_complete.

(* Prop of algo worklist system *)
Check a_wl_red_soundness.
Print Assumptions a_wl_red_soundness.
Check a_wl_red_completeness.
Print Assumptions a_wl_red_completeness.
