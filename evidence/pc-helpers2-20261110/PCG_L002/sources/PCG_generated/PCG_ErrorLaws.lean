import PCB_ErrorLaws
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCG_ErrorLaws
open PCB_ErrorRef.pool_v1
/-- Whole-domain reference law; native concrete From is certified per enum arm. -/
theorem receipt (e : verifier_dispatch.PoolV1VerifierDispatchFormatError) :
    authorization_receipt.PCB_159.reference e = ok (.Dispatch e) := PCB_ErrorLaws.receipt e

theorem account (e : authorization_receipt.PoolV1AuthorizationReceiptError) :
    authorization_receipt_account.PCB_160.reference e = ok (.Receipt e) := PCB_ErrorLaws.account e

theorem forest (e : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) :
    pair_forest_accounts.PCB_189.reference e = ok (.Tree e) := PCB_ErrorLaws.forest e
#print axioms receipt
#print axioms account
#print axioms forest
end PCG_ErrorLaws
