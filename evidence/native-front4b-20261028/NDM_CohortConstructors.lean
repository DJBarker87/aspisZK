import JHf_ReconstructionSlot
set_option autoImplicit false
namespace NDM_CohortConstructors
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct
open aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Validation := core.result.Result Unit pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def wrap (s : Statement) (r : Validation) : core.result.Result Statement solana_program_error.ProgramError :=
 match r with | .Ok _=>.Ok s | .Err _=>.Err .InvalidInstructionData

/-- The exact emitted constructor, including uniform error erasure, against
 the SAME actual emitted validator call. No native opaque validator is discharged. -/
theorem transfer (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1)
 (reply : Validation)
 (sameCall : pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.PrivateTransfer c p)=ok reply) :
 r1_pool_adapter.transfer_statement_box c p=ok (wrap (.PrivateTransfer c p) reply) := by
 unfold r1_pool_adapter.transfer_statement_box
 rw [sameCall]
 cases reply <;> rfl

theorem withdrawal (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1)
 (reply : Validation)
 (sameCall : pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.Withdrawal c p)=ok reply) :
 r1_pool_adapter.withdrawal_statement_box c p=ok (wrap (.Withdrawal c p) reply) := by
 unfold r1_pool_adapter.withdrawal_statement_box
 rw [sameCall]
 cases reply <;> rfl

#print axioms transfer
#print axioms withdrawal
end NDM_CohortConstructors
