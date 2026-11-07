import NMX_Question
set_option autoImplicit false
noncomputable section
namespace NMX_QuestionValue
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_ResultSteps
/-- Normalize only the local branch/residual combinator, before rewriting
its enclosing arbitrary raw Result bind. -/
theorem branch {A : Type} (reply : core.result.Result A PE) (next : A → Final) :
 (do
  let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | .Continue value => next value
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame PE) residual) =
 (match reply with | .Ok a => next a | .Err e => ok (.Err e)) := by
 cases reply <;> rfl
#print axioms branch
end NMX_QuestionValue
end
