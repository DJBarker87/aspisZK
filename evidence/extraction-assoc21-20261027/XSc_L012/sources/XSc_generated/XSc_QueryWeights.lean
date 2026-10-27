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
   have hw := (XSc_QueryNext.source proof p a a1 g obs geo pending pending1 run).2.2
   exact hw.trans ih
/-- Destination length64 is derived at the actual successful loop endpoint. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (a0 a : verifier.Accumulator) (pending0 pending : verifier.BatchedWeights)
 (initial : a0.weights.val.length=64)
 (run : verifier.candidate.query_loop proof p a0 g obs geo pending0 end1=ok (.Ok (a,pending))) :
 a.weights=a0.weights ∧ a.weights.val.length=64 := by
 have path := XSc_QueryPath.source proof p g obs geo end1 (.Ok (a0,pending0)) (.Ok (a,pending)) run
 have same := reached proof p g obs geo end1 a0 pending0 (.Ok (a,pending)) path
 exact ⟨same,by rw [same]; exact initial⟩
#print axioms reached
#print axioms source
end XSc_QueryWeights
