import XSg_QueryPhase
import XSe_QueryPower
import XSc_QueryTermCounter
import XSc_QueryPendingFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSg_QueryReached
/-- Every successful reached query prefix has the periodic row envelope.
A later rejected query does not require an invented surviving state. -/
theorem source (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (initial : verifier.Accumulator) (pending0 : verifier.BatchedWeights)
 (rho : XRp_PowersQAdd.CanonicalQ p.rho) (power : XRp_PowersQAdd.CanonicalQ initial.power)
 (counter : pending0.terms=initial.next) (width : initial.weights.val.length≤256)
 (len : pending0.raw.val.length=initial.weights.val.length)
 (phase : ∀ row∈pending0.raw.val,XSg_RowPhase.Bound pending0.terms.val row)
 (state : XSc_QueryPath.State)
 (path : XSc_QueryPath.Reached proof p g obs geo end1 (.Ok (initial,pending0)) state) :
 match state with
 | .Err _ => True
 | .Ok (a,pending) =>
  XRp_PowersQAdd.CanonicalQ a.power ∧ pending.terms=a.next ∧
  a.weights.val.length≤256 ∧ pending.raw.val.length=a.weights.val.length ∧
  ∀ row∈pending.raw.val,XSg_RowPhase.Bound pending.terms.val row := by
 induction path with
 | initial => exact ⟨power,counter,width,len,phase⟩
 | next a pending out previous active run ih =>
  cases out with
  | Err e => trivial
  | Ok pair =>
   rcases pair with ⟨out,after⟩
   rcases ih with ⟨power,counter,width,len,phase⟩
   have query := XSc_QueryNext.source proof p a out g obs geo pending after run
   have frame := XSc_QueryPendingFrame.source proof p a out g obs geo pending after run
   refine ⟨XSe_QueryPower.step proof p a out g obs geo pending after rho power run,
    XSc_QueryTermCounter.source proof p a out g obs geo pending after counter run,?_,?_,
    XSg_QueryPhase.source proof p a out g obs geo pending after counter power width len phase run⟩
   · rw [query.2.2];exact width
   · rw [frame.1,query.2.2];exact len
#print axioms source
end XSg_QueryReached
