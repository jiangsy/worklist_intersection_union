Require uni.notations.
Require uni.decl.prop_subtyping.
Require uni.decl.prop_typing.
Require uni.decl.prop_safety.
Require uni.decl_worklist.prop_equiv.
Require uni.algo_worklist.prop_soundness.
Require uni.algo_worklist.prop_completeness.
Require uni.algo_worklist.prop_decidability.

Require uni_rcd.notations.
Require uni_rcd.decl.prop_subtyping.
Require uni_rcd.decl.prop_typing.
Require uni_rcd.decl_worklist.prop_equiv.
Require uni_rcd.algo_worklist.prop_soundness.
Require uni_rcd.algo_worklist.prop_completeness.

Require uni_monoiu.notations.
Require uni_monoiu.decl.prop_subtyping.
Require uni_monoiu.decl.prop_typing.
Require uni_monoiu.decl_worklist.prop_equiv.
Require uni_monoiu.algo_worklist.prop_soundness.


(*      *)
(* Base *)
(*      *)
Section Base.

    Import uni.notations.
    Import uni.decl.prop_subtyping.
    Import uni.decl.prop_typing.
    Import uni.decl.prop_safety.
    Import uni.decl_worklist.prop_equiv.
    Import uni.algo_worklist.prop_soundness.
    Import uni.algo_worklist.prop_completeness.
    Import uni.algo_worklist.prop_decidability.

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

End Base.


(*                  *)
(* Record Extension *)
(*                  *)
Section Rcd_Extension.

    Import uni_rcd.notations.
    Import uni_rcd.decl.prop_subtyping.
    Import uni_rcd.decl.prop_typing.
    Import uni_rcd.decl_worklist.prop_equiv.
    Import uni_rcd.algo_worklist.prop_soundness.
    Import uni_rcd.algo_worklist.prop_completeness.

    (* Prop of decl system *)
    Check uni_rcd.decl.prop_subtyping.d_sub_transitivity.
    Print Assumptions uni_rcd.decl.prop_subtyping.d_sub_transitivity.
    Check uni_rcd.decl.prop_typing.d_chk_inf_subsumption.
    Print Assumptions uni_rcd.decl.prop_typing.d_chk_inf_subsumption.

    (* Prop of decl worklist system *)
    Check uni_rcd.decl_worklist.prop_equiv.d_wl_red_sound.
    Print Assumptions uni_rcd.decl_worklist.prop_equiv.d_wl_red_sound.
    Check uni_rcd.decl_worklist.prop_equiv.d_wl_red_complete.
    Print Assumptions uni_rcd.decl_worklist.prop_equiv.d_wl_red_complete.

    (* Prop of algo worklist system *)
    Check uni_rcd.algo_worklist.prop_soundness.a_wl_red_soundness.
    Print Assumptions uni_rcd.algo_worklist.prop_soundness.a_wl_red_soundness.
    Check uni_rcd.algo_worklist.prop_completeness.a_wl_red_completeness.
    Print Assumptions uni_rcd.algo_worklist.prop_completeness.a_wl_red_completeness.
    
End Rcd_Extension.


(*                                                      *)
(* Record Extension and Instantiable Intersection/union *)
(*                                                      *)
Section Monoiu_Extension.

    Import uni_monoiu.notations.
    Import uni_monoiu.decl.prop_subtyping.
    Import uni_monoiu.decl.prop_typing.
    Import uni_monoiu.decl_worklist.prop_equiv.
    Import uni_monoiu.algo_worklist.prop_soundness.

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

End Monoiu_Extension.

