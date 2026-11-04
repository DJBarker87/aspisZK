import NFQ_ScanReference.Funs
import AdapterRwModel
set_option autoImplicit false
namespace NFQ_Readonly
open Aeneas Aeneas.Std Result
open AdapterRw
/-- Exact full Result: scalar predicate is only the safe reference carrier. -/
theorem reference (signer writable executable : Bool) :
    (do let admitted ← NFQ_ScanReference.readonly_buffer_ref signer writable executable
        ok (if admitted then core.result.Result.Ok () else
          .Err solana_program_error.ProgramError.InvalidAccountData)) =
    r1_pool_adapter.readonly_buffer_meta_ok signer writable executable := by
  cases signer <;> cases writable <;> cases executable <;> rfl
#print axioms reference
end NFQ_Readonly
