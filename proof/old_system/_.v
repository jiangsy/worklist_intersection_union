Require Import ln_utils.
Require Import uni.def_ott.
Require Import uni.decl.def_extra.
Require Import uni.notations.
Require Import uni.prop_basic.
Require Import uni.decl.prop_typing.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.transfer.
Require Import uni.algo_worklist.def_extra.

Require Import uni.algo_worklist.prop_soundness.
Require Import uni.algo_worklist.prop_completeness.
Require Import uni.algo_worklist.prop_decidability.

(* Prop of decl system *)
Print Assumptions d_chk_inf_subsumption.

(* Prop of decl worklist system *)
Print Assumptions d_wl_red_complete.
Print Assumptions d_wl_red_sound.

(* Prop of algo worklist system *)
Print Assumptions a_wl_red_completeness.