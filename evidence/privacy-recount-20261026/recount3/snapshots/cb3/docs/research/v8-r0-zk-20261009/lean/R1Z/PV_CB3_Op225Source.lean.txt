import R1Z.ProverRwP6TransitionInstall

namespace R1Z.PV_CB3_Op225Source
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
variable [ExternalTypes]
namespace Raw
abbrev Public := ProverRwP6TransitionTransport.Raw.Public
abbrev Transfer := ProverRwP6TransitionTransport.Raw.Transfer
abbrev Withdrawal := ProverRwP6TransitionTransport.Raw.Withdrawal
end Raw
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Transfer := aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1

/-- Arbitrary reverse payload adapters: the extracted projection's answer is
independent of both payloads. No representation law is required. -/
def toRaw (transfer : Transfer → Raw.Transfer) (withdrawal : Withdrawal → Raw.Withdrawal)
    (p : Public) : Raw.Public :=
  match p with
  | .Transfer x t => .Transfer (transfer x) t
  | .Withdrawal x t => .Withdrawal (withdrawal x) t

/-- The complete Result equation for EVERY callback input, rather than only
inputs in the image of a forward raw-carrier map. The arbitrary payload
adapters are data, not successful-output or representation premises. -/
theorem op225_source (ops : ExternalFuns)
    (transfer : Transfer → Raw.Transfer) (withdrawal : Withdrawal → Raw.Withdrawal)
    (p : Public) :
    (ProverRwP6TransitionInstall.selected ops).op225 p =
      ProverRwP6TransitionSource.transition (toRaw transfer withdrawal p) := by
  cases p <;> rfl

/-- Changing either adapter leaves the entire extracted Result unchanged. -/
theorem adapters_independent
    (transfer transfer' : Transfer → Raw.Transfer)
    (withdrawal withdrawal' : Withdrawal → Raw.Withdrawal) (p : Public) :
    ProverRwP6TransitionSource.transition (toRaw transfer withdrawal p) =
      ProverRwP6TransitionSource.transition (toRaw transfer' withdrawal' p) := by
  cases p <;> rfl

#print axioms op225_source
#print axioms adapters_independent
end
end R1Z.PV_CB3_Op225Source
