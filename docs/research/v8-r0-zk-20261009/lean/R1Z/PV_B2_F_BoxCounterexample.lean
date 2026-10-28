import R1Z.PV_B2_C_ConstructorSuccess
set_option autoImplicit false
namespace PV_B2_F_BoxCounterexample
open Aeneas Aeneas.Std Result PV_B2_C_WeightsNative PV_B2_C_ConstructorRows
/-- Original Box allocation is an additional effect after construction. This
control-effect model does not assert an observed native OOM or its probability. -/
def boxed (allocation : Result Unit)
    (construction : Result (core.result.Result host_weights.Weights verifier.Error)) :
    Result (core.result.Result host_weights.Weights verifier.Error) := do
  let result ← construction
  match result with
  | .Err e => ok (.Err e)
  | .Ok w => do
    let _ ← allocation
    ok (.Ok w)

/-- The current unboxed constructor cannot equal the frozen boxed constructor
for every allocation outcome. This is a counterexample to the proposed copy
transport, not a counterexample to the V259 row statement or native OOM evidence. -/
theorem allocation_counterexample (variant : transport.Variant) (alpha : Array K 10#usize)
    (z : Array Point 2#usize) :
    boxed (fail .panic) (host_weights.Weights.new variant alpha z) ≠
      host_weights.Weights.new variant alpha z := by
  obtain ⟨w,hw⟩ := PV_B2_C_ConstructorSuccess.new_total variant alpha z
  rw [hw]
  simp only [boxed,bind_tc_ok,bind_tc_fail]
  intro h
  cases h
#print axioms allocation_counterexample
end PV_B2_F_BoxCounterexample
