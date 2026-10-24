import S9ActualPairActiveMapV1
import S9ActualPairHelperTwoBodyCallsV1
import S9ActualPairInitialWeightsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairHelperLoopToOldV1
open AspisR1S9ActualPairOldCarrierScalarV1
abbrev WA := AspisR1S9ActualPairHelperBodyPrefixV1.W
abbrev Q := aspis_core.field.QM31
abbrev GoodArray := AspisR1S9ActualPairScalarCallbackV1.GoodArray
abbrev QC := AspisR1S9ActualPairQMHelperTransportV1.Canonical
abbrev start0 := AspisR1S9ActualPairHelperTwoBodyCallsV1.start0

/-- The two source body calls and terminal call are obtained from the same
accepted actual helper loop. Canonicality is propagated between those calls,
and the old explicit helper is shown to succeed at the same mapped result. -/
theorem actual_helper_loop_success_to_old (ap0 ap1 : WA) (extra : Array Q 2#usize)
    (initial output : WA) (hp0 : GoodArray ap0) (hp1 : GoodArray ap1)
    (hi : GoodArray initial)
    (he : ∀ i q, Array.index_usize extra i = .ok q → QC q)
    (h : _root_.AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights_loop
      start0 ap0 ap1 extra initial = .ok output) :
    GoodArray output ∧
      AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop start0
        (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra)
        (mapArray toOldW initial) = .ok (mapArray toOldW output) := by
  obtain ⟨iter1,iter2,middle,hn0,_,_,hb0,hn1,_,_,hb1,hn2,_⟩ :=
    AspisR1S9ActualPairHelperTwoBodyCallsV1.helper_success_two_body_calls ap0 ap1 extra initial output h
  have ha0 : AspisR1S9ActualPairHelperBodyPrefixV1.pairActiveBody ap0 ap1 extra 0#usize iter1 initial =
      .ok (.cont (iter1,middle)) := by
    rw [←AspisR1S9ActualPairHelperBodyPrefixV1.body_some_eq_pairActiveBody ap0 ap1 extra start0 iter1 0#usize initial hn0]
    exact hb0
  obtain ⟨middle',hmflow,hcm,hm0⟩ := AspisR1S9ActualPairActiveMapV1.actual_active_success_maps
    ap0 ap1 extra 0#usize iter1 initial (.cont (iter1,middle)) hp0 hp1 hi he ha0
  have hm : middle = middle' := congrArg Prod.snd (ControlFlow.cont.inj hmflow)
  rw [←hm] at hcm hm0
  have ha1 : AspisR1S9ActualPairHelperBodyPrefixV1.pairActiveBody ap0 ap1 extra iter1.start iter2 middle =
      .ok (.cont (iter2,output)) := by
    rw [←AspisR1S9ActualPairHelperBodyPrefixV1.body_some_eq_pairActiveBody ap0 ap1 extra iter1 iter2 iter1.start middle hn1]
    exact hb1
  obtain ⟨output',hoflow,hco,hm1⟩ := AspisR1S9ActualPairActiveMapV1.actual_active_success_maps
    ap0 ap1 extra iter1.start iter2 middle (.cont (iter2,output)) hp0 hp1 hcm he ha1
  have ho : output = output' := congrArg Prod.snd (ControlFlow.cont.inj hoflow)
  rw [←ho] at hco hm1
  have ht0 : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra)
      start0 (mapArray toOldW initial) = .ok (.cont (iter1,mapArray toOldW middle)) := by
    rw [AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
      (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra) start0 iter1 0#usize
      (mapArray toOldW initial) hn0]
    exact hm0
  have ht1 : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra)
      iter1 (mapArray toOldW middle) = .ok (.cont (iter2,mapArray toOldW output)) := by
    rw [AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
      (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra) iter1 iter2 iter1.start
      (mapArray toOldW middle) hn1]
    exact hm1
  have ht2 : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra)
      iter2 (mapArray toOldW output) = .ok (.done (mapArray toOldW output)) := by
    unfold AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
    rw [hn2]
    rfl
  refine ⟨hco,?_⟩
  unfold AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop
  rw [Aeneas.Std.loop.eq_def]
  dsimp only
  rw [ht0]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def]
  dsimp only
  rw [ht1]
  simp only [bind_tc_ok]
  rw [Aeneas.Std.loop.eq_def]
  dsimp only
  rw [ht2]

/-- Entry theorem for the complete actual helper, with its own initial ZERO
weights. No independent old helper, body or primitive success premise. -/
theorem actual_helper_success_to_old (ap0 ap1 : WA) (extra : Array Q 2#usize)
    (output : WA) (hp0 : GoodArray ap0) (hp1 : GoodArray ap1)
    (he : ∀ i q, Array.index_usize extra i = .ok q → QC q)
    (h : _root_.AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights ap0 ap1 extra = .ok output) :
    GoodArray output ∧
      AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
        (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra) =
        .ok (mapArray toOldW output) := by
  have hr : _root_.AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights_loop
      start0 ap0 ap1 extra AspisR1S9ActualPairInitialWeightsV1.initial = .ok output := h
  obtain ⟨hc,hm⟩ := actual_helper_loop_success_to_old ap0 ap1 extra
    AspisR1S9ActualPairInitialWeightsV1.initial output hp0 hp1
    AspisR1S9ActualPairInitialWeightsV1.initial_canonical he hr
  rw [AspisR1S9ActualPairInitialWeightsV1.initial_maps] at hm
  exact ⟨hc,hm⟩
#print axioms actual_helper_loop_success_to_old
#print axioms actual_helper_success_to_old
end AspisR1S9ActualPairHelperLoopToOldV1
