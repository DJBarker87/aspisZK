import NEC_PairRef.Funs
import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace NEC_WithdrawalDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1
abbrev Common := pair_forest_terminal.PoolV1PairForestTerminalCommonV1
abbrev Public := payment_relation.PoolV1WithdrawalPublicV1
abbrev Statement := pair_forest_terminal.PoolV1PairForestTerminalStatementV1
abbrev ChildError := payment_relation.PoolV1PaymentStatementFormatError
abbrev Error := pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

def reference (common : Common) (reply : core.result.Result Public ChildError) : Result (core.result.Result Statement Error) := do
 let raw ← NEC_PairRef.pair_ref common reply
 match raw with
 | .Ok (c,p) => ok (.Ok (.Withdrawal c p))
 | .Err (.Child error) => ok (.Err (.Payment error))

theorem emitted (common : Common) (bytes : Slice U8)
 (reply : core.result.Result Public ChildError)
 (child : payment_relation.decode_pool_v1_withdrawal_public_v1 bytes=ok reply) :
 pair_forest_terminal.decode_withdrawal_statement_boxed_v1 common bytes=reference common reply := by
 unfold pair_forest_terminal.decode_withdrawal_statement_boxed_v1
 rw [child]
 cases reply <;> rfl

theorem successful_fields (common : Common) (payload : Public) :
 reference common (.Ok payload)=ok (.Ok (.Withdrawal common payload)) := rfl

theorem rejection (common : Common) (error : ChildError) :
 reference common (.Err error)=ok (.Err (.Payment error)) := rfl

#print axioms emitted
#print axioms successful_fields
#print axioms rejection
end NEC_WithdrawalDecode
