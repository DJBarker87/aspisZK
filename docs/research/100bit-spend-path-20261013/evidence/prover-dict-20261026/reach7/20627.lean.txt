import R1Z.PDict_ReachErase21
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.fold_cell`. -/
theorem erase_352 (ops other : ExternalFuns) :
    @prover.fold_cell _ (replace ops other) = @prover.fold_cell _ ops := by
  delta prover.fold_cell
  all_goals rfl
#print axioms erase_352

/-- Full symbolic source-function equality for `prover.fold_loop.body`. -/
theorem erase_353 (ops other : ExternalFuns) :
    @prover.fold_loop.body _ (replace ops other) = @prover.fold_loop.body _ ops := by
  delta prover.fold_loop.body
  try simp only [erase_352 ops other]
  all_goals rfl
#print axioms erase_353

/-- Full symbolic source-function equality for `prover.fold_loop`. -/
theorem erase_354 (ops other : ExternalFuns) :
    @prover.fold_loop _ (replace ops other) = @prover.fold_loop _ ops := by
  delta prover.fold_loop
  try simp only [erase_353 ops other]
  all_goals rfl
#print axioms erase_354

/-- Full symbolic source-function equality for `prover.fold`. -/
theorem erase_355 (ops other : ExternalFuns) :
    @prover.fold _ (replace ops other) = @prover.fold _ ops := by
  delta prover.fold
  try simp only [erase_354 ops other]
  all_goals rfl
#print axioms erase_355

/-- Full symbolic source-function equality for `prover.folded_leaves_loop0_loop0.body`. -/
theorem erase_356 (ops other : ExternalFuns) :
    @prover.folded_leaves_loop0_loop0.body _ (replace ops other) = @prover.folded_leaves_loop0_loop0.body _ ops := by
  delta prover.folded_leaves_loop0_loop0.body
  all_goals rfl
#print axioms erase_356

/-- Full symbolic source-function equality for `prover.folded_leaves_loop0_loop0`. -/
theorem erase_357 (ops other : ExternalFuns) :
    @prover.folded_leaves_loop0_loop0 _ (replace ops other) = @prover.folded_leaves_loop0_loop0 _ ops := by
  delta prover.folded_leaves_loop0_loop0
  try simp only [erase_356 ops other]
  all_goals rfl
#print axioms erase_357

end R1Z.PDict_ReachErase
