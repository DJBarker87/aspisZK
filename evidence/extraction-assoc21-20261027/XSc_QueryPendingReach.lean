import XSc_QueryPath
import XSc_QueryPendingFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryPendingReach
/-- Every actual reached successful prefix retains the initial raw-row length.
This covers prefixes of a loop that later rejects, not only accepted endpoints. -/
theorem reached (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a0 : verifier.Accumulator) (pending0 : verifier.BatchedWeights)
 (state : XSc_QueryPath.State)
 (path : XSc_QueryPath.Reached proof p g obs geo end1 (.Ok (a0,pending0)) state) :
 match state with | .Err _ => True | .Ok (_,pending) => pending.raw.val.length=pending0.raw.val.length := by
 induction path with
 | initial => rfl
 | next a pending out previous active run ih =>
  cases out with
  | Err e => trivial
  | Ok pair =>
   rcases pair with ⟨a1,pending1⟩
   have frame := (XSc_QueryPendingFrame.source proof p a a1 g obs geo pending pending1 run).1
   exact frame.trans ih
#print axioms reached
end XSc_QueryPendingReach
