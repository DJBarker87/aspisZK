import S9PairAfterLowFlowV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9PairActiveFlowV1
open AspisR1S9PairCallerBodyPrefixV1

theorem active_success_preserves_iter
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (side : U) (iterNext : R) (weights : W)
    (flow : ControlFlow (R × W) W)
    (h : pairActiveBody ap0 ap1 extra side iterNext weights = .ok flow) :
    ∃ output, flow = .cont (iterNext, output) := by
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
    hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail⟩ :=
      pair_active_prefix_from_success ap0 ap1 extra side iterNext weights flow h
  exact AspisR1S9PairAfterLowFlowV1.afterlow_success_preserves_iter
    ap1 side iterNext weights q41 q8 q12 q16 low flow htail

theorem source_body_success_preserves_iter
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter iterNext : R) (side : U) (weights : W)
    (flow : ControlFlow (R × W) W)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side,iterNext))
    (h : AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter weights = .ok flow) :
    ∃ output, flow = .cont (iterNext,output) := by
  rw [body_some_eq_pairActiveBody ap0 ap1 extra iter iterNext side weights hn] at h
  exact active_success_preserves_iter ap0 ap1 extra side iterNext weights flow h

#print axioms active_success_preserves_iter
#print axioms source_body_success_preserves_iter
end AspisR1S9PairActiveFlowV1
