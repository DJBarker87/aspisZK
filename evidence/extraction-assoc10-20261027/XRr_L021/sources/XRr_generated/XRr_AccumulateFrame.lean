import XRn_Join_Funs
import XRk_ResultTools
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_AccumulateFrame
/-- The deferred source preserves its weight carrier until finish. -/
theorem weights (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (b bout : verifier.BatchedWeights)
 (h : verifier.accumulate_batched_with_node p a node value b=ok (out,bout)) :
 out.weights=a.weights := by
 unfold verifier.accumulate_batched_with_node at h
 iterate 11 obtain ⟨x,_,h⟩ := bind_success _ _ _ h
 cases Result.ok.inj h
 rfl
#print axioms weights
end XRr_AccumulateFrame
