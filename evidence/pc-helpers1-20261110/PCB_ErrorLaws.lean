import PCB_ErrorRef.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCB_ErrorLaws
open PCB_ErrorRef.pool_v1

theorem receipt (e : verifier_dispatch.PoolV1VerifierDispatchFormatError) :
    authorization_receipt.PCB_159.reference e =
      ok (.Dispatch e) := by rfl

theorem account (e : authorization_receipt.PoolV1AuthorizationReceiptError) :
    authorization_receipt_account.PCB_160.reference e =
      ok (.Receipt e) := by rfl

theorem forest (e : incremental_merkle.PoolV1TreeError) :
    pair_forest_accounts.PCB_189.reference e =
      ok (.Tree e) := by rfl

#print axioms receipt
#print axioms account
#print axioms forest
end PCB_ErrorLaws
