import NKO_FrameAtActual
import NKE_QueryReturn
set_option autoImplicit false
noncomputable section
namespace NKO_QueryReturnG
open Aeneas Aeneas.Std Result AspisR1 VTop_Stages
abbrev Reply := Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights) verifier.Error)
/-- Literal owned query caller destructure after the child returns; fail/div,
Err and both owned successful carriers are retained, without a success premise. -/
def G (reply : Reply) : Reply := do
 let r ← reply
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Break residual =>
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   _ (core.convert.FromSame verifier.Error) residual
 | .Continue pair => let (a,pending) := pair;ok (.Ok (a,pending))
theorem full_result (reply : Reply) : G reply=reply := by
 cases reply with
 | fail e => rfl
 | div => rfl
 | ok r => cases r with
   | Err e => rfl
   | Ok pair => cases pair;rfl
/-- Retained native return/destructure association composes on the SAME full
child result. This is a local stage theorem, never the TX2:065 parent root. -/
theorem retained_return (reply : Reply) :
 G (NKE_QueryReturn.observed reply)=reply := by
 rw [NKE_QueryReturn.observed_exact,full_result]
#print full_result
#print axioms full_result
#print retained_return
#print axioms retained_return
end NKO_QueryReturnG
