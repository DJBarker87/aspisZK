import NGK_NFR_CHelper
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NHC_ErrorConversion
/-- Exact emitted conversion on every valid Pool error constructor. -/
theorem result (e : NGK_NFR_CHelper.aspis_pool.error.PoolV1ProgramError) :
    NGK_NFR_CHelper.convertPoolError e =
    ok (AdapterRw.solana_program_error.ProgramError.Custom (read_discriminant e)) := by
  cases e <;> rfl
#print axioms result
end NHC_ErrorConversion
