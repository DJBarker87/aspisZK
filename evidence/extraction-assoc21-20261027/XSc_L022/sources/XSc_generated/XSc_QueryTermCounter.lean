import XSc_QueryPendingFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryTermCounter
/-- The actual pending counter and query index advance by the SAME checked add.
Neither successful increment is supplied independently. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights) (same : pending.terms=a.next)
 (run : verifier.candidate.query_values proof p a g obs geo pending=ok (.Ok (out,after))) :
 after.terms=out.next := by
 obtain ⟨query,node,value,_,hacc,hnext,_⟩ := XSc_QueryCuts.source proof p a out g obs geo pending after run
 have hterm := (XSc_AccumulateFrame.source p a out node value pending after hacc).2
 rw [same] at hterm
 exact Result.ok.inj (hterm.symm.trans hnext)
#print axioms source
end XSc_QueryTermCounter
