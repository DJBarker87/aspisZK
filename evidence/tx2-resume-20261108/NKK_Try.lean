import NJU_ResumeObserved
set_option autoImplicit false
namespace NKK_Try
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission

def emitted {E A B : Type} (reply : core.result.Result A verifier.Error)
 (next : A → NJU_Log.Run E (core.result.Result B verifier.Error)) :
 NJU_Log.Run E (core.result.Result B verifier.Error) := do
 let flow ← core.result.Result.Insts.CoreOpsTry.branch reply
 match flow with
 | .Continue value => next value
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual B (core.convert.FromSame verifier.Error) residual

/-- The exact emitted ?/FromSame sequence, on every error variant. -/
theorem branch {E A B : Type} (reply : core.result.Result A verifier.Error)
 (next : A → NJU_Log.Run E (core.result.Result B verifier.Error)) :
 emitted reply next=(match reply with | .Ok value=>next value | .Err err=>pure (.Err err)) := by
 cases reply <;> rfl

#print axioms branch
end NKK_Try
