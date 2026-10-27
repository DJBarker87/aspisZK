import XSc_QueryPath
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryPrefixIndex
/-- Prefix indices are bounded by the actual loop endpoint, even if a later
query rejects. The initial bound is discharged by actual S2 initialization. -/
theorem reached (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a0 : verifier.Accumulator) (pending0 : verifier.BatchedWeights)
 (initial : a0.next.val≤end1.val) (state : XSc_QueryPath.State)
 (path : XSc_QueryPath.Reached proof p g obs geo end1 (.Ok (a0,pending0)) state) :
 match state with | .Err _ => True | .Ok (a,_) => a.next.val≤end1.val := by
 induction path with
 | initial => exact initial
 | next a pending out previous active run ih =>
  cases out with
  | Err e => trivial
  | Ok pair =>
   rcases pair with ⟨a1,pending1⟩
   have hn := (XRr_QueryFrame.query proof p a a1 g obs geo pending pending1 run).2.2
   change a.next.val<end1.val at active
   omega
#print axioms reached
end XSc_QueryPrefixIndex
