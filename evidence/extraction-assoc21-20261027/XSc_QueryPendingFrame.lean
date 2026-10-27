import XSc_QueryCuts
import XSc_AccumulateFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryPendingFrame
/-- Raw-row sizing and the query-counter update come from THIS successful query,
including its same pending continuation. No reserve success is invented. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights)
 (run : verifier.candidate.query_values proof p a g obs geo pending=ok (.Ok (out,after))) :
 after.raw.val.length=pending.raw.val.length ∧
 (pending.terms+1#usize : Result Usize)=ok after.terms := by
 obtain ⟨query,node,value,_,hacc,_,_⟩ := XSc_QueryCuts.source proof p a out g obs geo pending after run
 exact XSc_AccumulateFrame.source p a out node value pending after hacc
#print axioms source
end XSc_QueryPendingFrame
