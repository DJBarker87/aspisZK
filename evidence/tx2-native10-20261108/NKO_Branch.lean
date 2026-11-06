import NKE_Entered
import NKE_CommonCalls
set_option autoImplicit false
namespace NKO_Branch
open Aeneas Aeneas.Std Result VTop_Stages
/-- Bind inversion from a real source equation and its entered Try branch.
This is an internal elimination lemma, not a permitted root hypothesis. -/
theorem continued {A : Type} (m : Result (core.result.Result A verifier.Error))
 (reply : core.result.Result A verifier.Error) (a : A)
 (call : m=ok reply)
 (step : core.result.Result.Insts.CoreOpsTry.branch reply=
  ok (core.ops.control_flow.ControlFlow.Continue a)) : m=ok (.Ok a) := by
 cases reply with
 | Err e => cases step
 | Ok v =>
  have same := core.ops.control_flow.ControlFlow.Continue.inj (Result.ok.inj step)
  cases same
  exact call
#print axioms continued
end NKO_Branch
