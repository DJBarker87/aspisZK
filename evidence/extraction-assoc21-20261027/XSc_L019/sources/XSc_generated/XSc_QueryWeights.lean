import XSc_QueryPath
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_QueryWeights
/-- Every reached successful prefix keeps THIS initial destination vector. -/
theorem reached (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a0 : verifier.Accumulator) (pending0 : verifier.BatchedWeights)
 (state : XSc_QueryPath.State)
 (path : XSc_QueryPath.Reached proof p g obs geo end1 (.Ok (a0,pending0)) state) :
 match state with | .Err _ => True | .Ok (a,_) => a.weights=a0.weights := by
 induction path with
 | initial => rfl
 | next a pending out previous active run ih =>
  cases out with
  | Err e => trivial
  | Ok pair =>
   rcases pair with ⟨a1,pending1⟩
   have hw := (XRr_QueryFrame.query proof p a a1 g obs geo pending pending1 run).2.1
   exact hw.trans ih
#print axioms reached
end XSc_QueryWeights
