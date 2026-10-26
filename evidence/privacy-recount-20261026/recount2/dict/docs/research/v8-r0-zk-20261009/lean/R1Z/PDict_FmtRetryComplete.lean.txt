import R1Z.PDict_FmtMaskedBody
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.retry_attempt`. -/
theorem erase_425 (ops other : ExternalFuns) :
    @prover.retry_attempt _ (replace ops other) = @prover.retry_attempt _ ops := by
  funext T callback public1 compiled variant hash
  delta prover.retry_attempt
  apply fixed_equal
  funext recur nonce_store next_attempt k
  try simp only [erase_424 ops other]
  all_goals rfl
#print axioms erase_425
end R1Z.PDict_FmtErase
