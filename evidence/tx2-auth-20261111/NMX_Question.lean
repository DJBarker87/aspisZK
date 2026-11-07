import NMX_ResultSteps
set_option autoImplicit false
noncomputable section
namespace NMX_Question
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_ResultSteps
/-- Symbolic normalization of one emitted `?` occurrence, including its
from_residual conversion. The child itself stays folded. -/
theorem question {A : Type} (r : Result (core.result.Result A PE)) (next : A → Final) :
 (do
  let reply ← r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch reply
  match cf with
  | .Continue value => next value
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      r1_pool_adapter.AuthenticatedAsq8Accounts (core.convert.FromSame PE) residual) =
 tryThen r next := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply <;> rfl
#print axioms question
end NMX_Question
end
