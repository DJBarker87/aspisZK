import XSe_InitialPower
import XSc_QueryCuts
import XSc_QueryPath
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_QueryPower
/-- One actual query preserves power canonicality through its derived
accumulation cut. No independent accumulation output is assumed. -/
theorem step (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (pending after : verifier.BatchedWeights)
 (rho : XRp_PowersQAdd.CanonicalQ p.rho) (power : XRp_PowersQAdd.CanonicalQ a.power)
 (run : verifier.candidate.query_values proof p a g obs geo pending=ok (.Ok (out,after))) :
 XRp_PowersQAdd.CanonicalQ out.power := by
 obtain ⟨q,node,value,_,hacc,_,_⟩ := XSc_QueryCuts.source proof p a out g obs geo pending after run
 exact XSe_PowerCanonical.reached p a out node value pending after rho power hacc
/-- Every reached successful prefix has canonical power. The rejected terminal
case has no invented surviving arithmetic state. -/
theorem reached (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geo : verifier.QueryGeometry)
 (end1 : Usize) (initial : verifier.Accumulator) (pending0 : verifier.BatchedWeights)
 (rho : XRp_PowersQAdd.CanonicalQ p.rho) (power : XRp_PowersQAdd.CanonicalQ initial.power)
 (state : XSc_QueryPath.State)
 (path : XSc_QueryPath.Reached proof p g obs geo end1 (.Ok (initial,pending0)) state) :
 match state with | .Err _ => True | .Ok (a,_) => XRp_PowersQAdd.CanonicalQ a.power := by
 induction path with
 | initial => exact power
 | next a pending out previous active run ih =>
   cases out with
   | Err e => trivial
   | Ok pair =>
     rcases pair with ⟨a1,pending1⟩
     exact step proof p a a1 g obs geo pending pending1 rho ih run
#print axioms step
#print axioms reached
end XSe_QueryPower
