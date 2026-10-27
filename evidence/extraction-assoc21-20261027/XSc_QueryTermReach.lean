import XSc_QueryPath
import XSc_QueryTermCounter
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryTermReach
/-- Actual query-prefix counter provenance, including prefixes before rejection.
No independently selected term counter or successful push is assumed. -/
theorem reached (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a0 : verifier.Accumulator) (pending0 : verifier.BatchedWeights)
 (initial : pending0.terms=a0.next) (state : XSc_QueryPath.State)
 (path : XSc_QueryPath.Reached proof p g obs geo end1 (.Ok (a0,pending0)) state) :
 match state with | .Err _ => True | .Ok (a,pending) => pending.terms=a.next := by
 induction path with
 | initial => exact initial
 | next a pending out previous active run ih =>
  cases out with
  | Err e => trivial
  | Ok pair =>
   rcases pair with ⟨a1,pending1⟩
   exact XSc_QueryTermCounter.source proof p a a1 g obs geo pending pending1 ih run
#print axioms reached
end XSc_QueryTermReach
