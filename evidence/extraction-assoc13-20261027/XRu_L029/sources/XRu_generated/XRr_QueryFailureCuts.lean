import XRr_QueryFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_QueryFailureCuts
/-- Before opening/folding, a failed actual query-index read propagates. -/
theorem index_fail (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (e : Error)
 (h : Array.index_usize p.queries a.next=.fail e) :
 verifier.candidate.query_values proof p a g obs geo b=.fail e := by
 unfold verifier.candidate.query_values
 rw [h,bind_tc_fail]
#print axioms index_fail
end XRr_QueryFailureCuts
