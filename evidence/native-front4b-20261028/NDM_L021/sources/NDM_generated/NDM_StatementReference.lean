import NDM_SnapshotRef.Funs
import NDM_CommonCarrier
set_option autoImplicit false
namespace NDM_StatementReference
open Aeneas Aeneas.Std Result AdapterRw
open aspis_statement.pool_v1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Common := NDM_CommonCarrier.Common
abbrev Transfer := payment_relation.PoolV1PrivateTransferPublicV1
abbrev Withdrawal := payment_relation.PoolV1WithdrawalPublicV1
abbrev Validation := core.result.Result Unit pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def accepted (reply : Validation) : Bool := match reply with | .Ok _=>true | .Err _=>false

def lift {C P : Type} (build : C → P → Statement)
 (reply : core.result.Result (C × P) U8) : core.result.Result Statement solana_program_error.ProgramError :=
 match reply with | .Ok (c,p)=>.Ok (build c p) | .Err _=>.Err .InvalidInstructionData

def reference {C P : Type} (build : C → P → Statement) (c : C) (p : P) (valid : Bool) := do
 let reply ← NDM_SnapshotRef.validation_ref c p valid
 ok (lift build reply)

def call (ops : Ops) (statement : Statement) : Result
 (core.result.Result Statement solana_program_error.ProgramError) := do
 let reply ← ops.op21 statement
 ok (match reply with | .Ok _=>.Ok statement | .Err _=>.Err .InvalidInstructionData)

/-- Same constructed statement and SAME validator reply. The native callback
 association and its installed semantic interpretation remain separate obligations. -/
theorem transfer (ops : Ops) (c : Common) (p : Transfer) (reply : Validation)
 (sameCall : ops.op21 (.PrivateTransfer c p)=ok reply) :
 call ops (.PrivateTransfer c p) = reference Statement.PrivateTransfer c p (accepted reply) := by
 unfold call
 rw [sameCall]
 cases reply <;> rfl

theorem withdrawal (ops : Ops) (c : Common) (p : Withdrawal) (reply : Validation)
 (sameCall : ops.op21 (.Withdrawal c p)=ok reply) :
 call ops (.Withdrawal c p) = reference Statement.Withdrawal c p (accepted reply) := by
 unfold call
 rw [sameCall]
 cases reply <;> rfl

/-- Error payloads are discarded uniformly, not only for a fixture error variant. -/
theorem error_payload (ops : Ops) (statement : Statement)
 (error : pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
 (sameCall : ops.op21 statement=ok (.Err error)) :
 call ops statement=ok (.Err .InvalidInstructionData) := by
 unfold call
 rw [sameCall]
 rfl

#print axioms transfer
#print axioms withdrawal
#print axioms error_payload
end NDM_StatementReference
