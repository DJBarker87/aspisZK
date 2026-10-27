import R1Z.PDict_ReachErase25
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.append_opening_values`. -/
theorem erase_416 (ops other : ExternalFuns) :
    @prover.append_opening_values _ (replace ops other) = @prover.append_opening_values _ ops := by
  delta prover.append_opening_values
  try simp only [erase_412 ops other, erase_415 ops other]
  all_goals rfl
#print axioms erase_416

/-- Full symbolic source-function equality for `prover.append_query_openings_loop.body`. -/
theorem erase_417 (ops other : ExternalFuns) :
    @prover.append_query_openings_loop.body _ (replace ops other) = @prover.append_query_openings_loop.body _ ops := by
  delta prover.append_query_openings_loop.body
  try simp only [erase_408 ops other, erase_409 ops other, erase_416 ops other, erase_351 ops other]
  all_goals rfl
#print axioms erase_417

end R1Z.PDict_ReachErase
