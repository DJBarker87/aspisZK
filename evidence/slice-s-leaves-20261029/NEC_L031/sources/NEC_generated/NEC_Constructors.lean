import NDM_CohortConstructors
import NDM_SnapshotRef.Funs
set_option autoImplicit false
namespace NEC_Constructors
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev Validation := NDM_CohortConstructors.Validation

def PacketDomain (_c : Common) : Prop := True

theorem caller_domain (c : Common) : PacketDomain c := True.intro

def valid (reply : Validation) : Bool := match reply with | .Ok _=>true | .Err _=>false

def reference {P : Type} (ctor : Common → P → Statement) (c : Common) (p : P)
 (reply : Validation) : Result (core.result.Result Statement solana_program_error.ProgramError) := do
 let pair ← NDM_SnapshotRef.validation_ref c p (valid reply)
 match pair with
 | .Ok (common,public1)=>ok (.Ok (ctor common public1))
 | .Err _=>ok (.Err .InvalidInstructionData)

theorem same_reply {P : Type} (ctor : Common → P → Statement) (c : Common) (p : P)
 (reply : Validation) : reference ctor c p reply=ok (NDM_CohortConstructors.wrap (ctor c p) reply) := by
 cases reply <;> rfl

theorem transfer (c : Common) (p : payment_relation.PoolV1PrivateTransferPublicV1)
 (reply : Validation)
 (child : pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
   (.PrivateTransfer c p)=ok reply) :
 r1_pool_adapter.transfer_statement_box c p=reference .PrivateTransfer c p reply := by
 rw [same_reply]
 exact NDM_CohortConstructors.transfer c p reply child

theorem withdrawal (c : Common) (p : payment_relation.PoolV1WithdrawalPublicV1)
 (reply : Validation)
 (child : pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
   (.Withdrawal c p)=ok reply) :
 r1_pool_adapter.withdrawal_statement_box c p=reference .Withdrawal c p reply := by
 rw [same_reply]
 exact NDM_CohortConstructors.withdrawal c p reply child

#print axioms caller_domain
#print axioms same_reply
#print axioms transfer
#print axioms withdrawal
end NEC_Constructors
