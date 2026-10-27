import XRr_QueryCalls
import XRr_Initial64
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_Accepted64
/-- Length 64 and the exact ordered prefix are consequences of these SAME
initialization and query-loop executions. Pending-row materialization is OPEN. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a out : verifier.Accumulator) (b bout : verifier.BatchedWeights)
 (init : verifier.Accumulator.new .S2=ok (.Ok a))
 (run : verifier.candidate.query_loop proof p a g obs geo b end1=ok (.Ok (out,bout))) :
 XRr_QueryCalls.Calls (fun a b => verifier.candidate.query_values proof p a g obs geo b)
   end1.val a b out bout end1.val ∧ out.weights=a.weights ∧
 out.weights.val.length=64 ∧ out.next.val=end1.val := by
 obtain ⟨hlen,hzero⟩ := XRr_Initial64.init a init
 have bound : a.next.val≤end1.val := by rw [hzero]; change 0≤_; omega
 have calls := XRr_QueryCalls.source proof p g obs geo end1 a out b bout bound run
 have frame := XRr_QueryCalls.weights proof p g obs geo end1.val a out b bout _ calls
 refine ⟨?_,frame.1,?_,frame.2⟩
 · simpa only [hzero,UScalar.ofNat_val,Nat.sub_zero] using calls
 · rw [frame.1];exact hlen
#print axioms source
end XRr_Accepted64
