import NDM_CohortConstructors
import NDM_StatementReference
set_option autoImplicit false
namespace NDM_CohortStatement
open Aeneas Aeneas.Std Result
open AspisR1.JHf_Carrier
abbrev RawStatement := NDM_CohortConstructors.Statement
abbrev RawReply := core.result.Result RawStatement AspisR1AdapterReconstruct.solana_program_error.ProgramError
abbrev Reply := core.result.Result NDM_StatementReference.Statement AdapterRw.solana_program_error.ProgramError

def transport (r : RawReply) : Reply := match r with
 | .Ok s=>.Ok (fromPoolV1PairForestTerminalStatementV1 s)
 | .Err e=>.Err (AspisR1.JHf_ProgramErrorCarrier.fromRaw e)

def accepted (r : NDM_CohortConstructors.Validation) : Bool :=
 match r with | .Ok _=>true | .Err _=>false

/-- Extracted safe reference to actual cohort constructor on the SAME actual
 validator invocation. The native validator abstraction remains OPEN. -/
theorem transfer (c : NDM_StatementReference.Common) (p : NDM_StatementReference.Transfer)
 (reply : NDM_CohortConstructors.Validation)
 (sameCall : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.PrivateTransfer (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1PrivateTransferPublicV1 p))=ok reply) :
 (do let r ← AspisR1AdapterReconstruct.r1_pool_adapter.transfer_statement_box
       (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1PrivateTransferPublicV1 p)
     ok (transport r))=
 NDM_StatementReference.reference (fun c p=>(.PrivateTransfer c p : NDM_StatementReference.Statement)) c p (accepted reply) := by
 rw [NDM_CohortConstructors.transfer _ _ reply sameCall]
 cases reply <;> rfl

theorem withdrawal (c : NDM_StatementReference.Common) (p : NDM_StatementReference.Withdrawal)
 (reply : NDM_CohortConstructors.Validation)
 (sameCall : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
  (.Withdrawal (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1WithdrawalPublicV1 p))=ok reply) :
 (do let r ← AspisR1AdapterReconstruct.r1_pool_adapter.withdrawal_statement_box
       (toPoolV1PairForestTerminalCommonV1 c) (toPoolV1WithdrawalPublicV1 p)
     ok (transport r))=
 NDM_StatementReference.reference (fun c p=>(.Withdrawal c p : NDM_StatementReference.Statement)) c p (accepted reply) := by
 rw [NDM_CohortConstructors.withdrawal _ _ reply sameCall]
 cases reply <;> rfl

#print axioms transfer
#print axioms withdrawal
end NDM_CohortStatement
