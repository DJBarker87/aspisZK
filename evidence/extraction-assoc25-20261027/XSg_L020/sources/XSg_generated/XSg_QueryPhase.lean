import XSg_AccumulatePhase
import XSc_QueryCuts
import XSc_QueryNext
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_QueryPhase
/-- One actual successful query preserves the SAME pending phase domain.
Canonical basis is derived inside accumulation rather than passed by a caller. -/
theorem source (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights)
 (same : pending.terms=a.next)
 (canon : XRp_PowersQAdd.CanonicalQ a.power)
 (small : a.weights.val.length≤256) (len : pending.raw.val.length=a.weights.val.length)
 (phase : ∀ row∈pending.raw.val,XSg_RowPhase.Bound pending.terms.val row)
 (run : verifier.candidate.query_values proof p a g obs geo pending=ok (.Ok (out,after))) :
 ∀ row∈after.raw.val,XSg_RowPhase.Bound after.terms.val row := by
 obtain ⟨q,node,value,_,hacc,_,_⟩ := XSc_QueryCuts.source proof p a out g obs geo pending after run
 have bound := (XSc_QueryNext.source proof p a out g obs geo pending after run).1
 have counter : pending.terms.val<22 := by rw [same];exact bound
 exact XSg_AccumulatePhase.source p a out node value pending after counter canon small len phase hacc
#print axioms source
end XSg_QueryPhase
