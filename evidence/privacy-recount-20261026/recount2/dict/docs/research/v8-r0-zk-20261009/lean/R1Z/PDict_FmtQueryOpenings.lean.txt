import R1Z.PDict_FmtOpeningValues
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.append_query_openings_loop`. -/
theorem erase_418 (ops other : ExternalFuns) :
    @prover.append_query_openings_loop _ (replace ops other) = @prover.append_query_openings_loop _ ops := by
  delta prover.append_query_openings_loop
  try simp only [erase_417 ops other]
  all_goals rfl
#print axioms erase_418

/-- Full symbolic source-function equality for `prover.append_query_openings`. -/
theorem erase_419 (ops other : ExternalFuns) :
    @prover.append_query_openings _ (replace ops other) = @prover.append_query_openings _ ops := by
  delta prover.append_query_openings
  try simp only [erase_418 ops other]
  all_goals rfl
#print axioms erase_419

end R1Z.PDict_FmtErase
