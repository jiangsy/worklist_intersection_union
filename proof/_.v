(*      *)
(* Base *)
(*      *)
Require Import uni.decl.prop_subtyping.
Require Import uni.decl.prop_typing.
Require Import uni.decl.prop_safety.
Require Import uni.decl_worklist.prop_equiv.
Require Import uni.algo_worklist.prop_soundness.
Require Import uni.algo_worklist.prop_completeness.
Require Import uni.algo_worklist.prop_decidability.

(* Prop of decl system *)
Check uni.decl.prop_subtyping.d_sub_transitivity.
Print Assumptions uni.decl.prop_subtyping.d_sub_transitivity.
Check uni.decl.prop_typing.d_chk_inf_subsumption.
Print Assumptions uni.decl.prop_typing.d_chk_inf_subsumption.
Check uni.decl.prop_safety.d_chk_inf_elab_sound_f.
Print Assumptions uni.decl.prop_safety.d_chk_inf_elab_sound_f.

(* Prop of decl worklist system *)
Check uni.decl_worklist.prop_equiv.d_wl_red_sound.
Print Assumptions uni.decl_worklist.prop_equiv.d_wl_red_sound.
Check uni.decl_worklist.prop_equiv.d_wl_red_complete.
Print Assumptions uni.decl_worklist.prop_equiv.d_wl_red_complete.

(* Prop of algo worklist system *)
Check uni.algo_worklist.prop_soundness.a_wl_red_soundness.
Print Assumptions uni.algo_worklist.prop_soundness.a_wl_red_soundness.
Check uni.algo_worklist.prop_completeness.a_wl_red_completeness.
Print Assumptions uni.algo_worklist.prop_completeness.a_wl_red_completeness.
Check uni.algo_worklist.prop_decidability.a_wf_wl_red_decidable.
Print Assumptions uni.algo_worklist.prop_decidability.a_wf_wl_red_decidable.


(*                  *)
(* Record Extension *)
(*                  *)
Require Import uni_rec.decl.prop_subtyping.
Require Import uni_rec.decl.prop_typing.
Require Import uni_rec.decl_worklist.prop_equiv.
Require Import uni_rec.algo_worklist.prop_soundness.
Require Import uni_rec.algo_worklist.prop_completeness.

(* Prop of decl system *)
Check uni_rec.decl.prop_subtyping.d_sub_transitivity.
Print Assumptions uni_rec.decl.prop_subtyping.d_sub_transitivity.
Check uni_rec.decl.prop_typing.d_chk_inf_subsumption.
Print Assumptions uni_rec.decl.prop_typing.d_chk_inf_subsumption.

(* Prop of decl worklist system *)
Check uni_rec.decl_worklist.prop_equiv.d_wl_red_sound.
Print Assumptions uni_rec.decl_worklist.prop_equiv.d_wl_red_sound.
Check uni_rec.decl_worklist.prop_equiv.d_wl_red_complete.
Print Assumptions uni_rec.decl_worklist.prop_equiv.d_wl_red_complete.

(* Prop of algo worklist system *)
Check uni_rec.algo_worklist.prop_soundness.a_wl_red_soundness.
Print Assumptions uni_rec.algo_worklist.prop_soundness.a_wl_red_soundness.
Check uni_rec.algo_worklist.prop_completeness.a_wl_red_completeness.
Print Assumptions uni_rec.algo_worklist.prop_completeness.a_wl_red_completeness.


(*                                                      *)
(* Record Extension and Instantiable Intersection/union *)
(*                                                      *)
Require Import uni_monoiu.decl.prop_subtyping.
Require Import uni_monoiu.decl.prop_typing.
Require Import uni_monoiu.decl_worklist.prop_equiv.
Require Import uni_monoiu.algo_worklist.prop_soundness.

(* Prop of decl system *)
Check uni_monoiu.decl.prop_subtyping.d_sub_transitivity.
Print Assumptions uni_monoiu.decl.prop_subtyping.d_sub_transitivity.
Check uni_monoiu.decl.prop_typing.d_chk_inf_subsumption.
Print Assumptions uni_monoiu.decl.prop_typing.d_chk_inf_subsumption.

(* Prop of decl worklist system *)
Check uni_monoiu.decl_worklist.prop_equiv.d_wl_red_sound.
Print Assumptions uni_monoiu.decl_worklist.prop_equiv.d_wl_red_sound.
Check uni_monoiu.decl_worklist.prop_equiv.d_wl_red_complete.
Print Assumptions uni_monoiu.decl_worklist.prop_equiv.d_wl_red_complete.

(* Prop of algo worklist system *)
Check uni_monoiu.algo_worklist.prop_soundness.a_wl_red_soundness.
Print Assumptions uni_monoiu.algo_worklist.prop_soundness.a_wl_red_soundness.