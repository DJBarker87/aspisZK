import NJU_CommonObserved
set_option autoImplicit false
namespace NKE_RustBind
open Aeneas Aeneas.Std Result VTop_Stages

def bind {E A B : Type} (m : NJU_Log.Run E (core.result.Result A verifier.Error))
 (k : A → NJU_Log.Run E (core.result.Result B verifier.Error)) :
 NJU_Log.Run E (core.result.Result B verifier.Error) := do
 let reply ← m
 match reply with
 | .Ok value => k value
 | .Err e => liftM (ok (.Err e))

/-- Full writer law: no log entry is lost by lowering the emitted Try arm. -/
theorem lower {E A B : Type} (m : NJU_Log.Run E (core.result.Result A verifier.Error))
 (k : A → NJU_Log.Run E (core.result.Result B verifier.Error)) :
 (do
  let reply ← m
  let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | core.ops.control_flow.ControlFlow.Continue value => k value
  | core.ops.control_flow.ControlFlow.Break residual =>
    liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     B (core.convert.FromSame verifier.Error) residual))=bind m k := by
 cases m with
 | mk result events =>
  cases result with
  | fail e => rfl
  | div => rfl
  | ok reply => cases reply <;> rfl
#print axioms lower
end NKE_RustBind
