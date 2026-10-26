import R1Z.PDict_FmtErase21
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
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

/-- Full symbolic source-function equality for `prover.folded_leaves_loop0.body`. -/
theorem erase_358 (ops other : ExternalFuns) :
    @prover.folded_leaves_loop0.body _ (replace ops other) = @prover.folded_leaves_loop0.body _ ops := by
  delta prover.folded_leaves_loop0.body
  try simp only [erase_357 ops other]
  all_goals rfl
#print axioms erase_358

/-- Full symbolic source-function equality for `prover.folded_leaves_loop0`. -/
theorem erase_359 (ops other : ExternalFuns) :
    @prover.folded_leaves_loop0 _ (replace ops other) = @prover.folded_leaves_loop0 _ ops := by
  delta prover.folded_leaves_loop0
  try simp only [erase_358 ops other]
  all_goals rfl
#print axioms erase_359

/-- Full symbolic source-function equality for `prover.folded_leaves`. -/
theorem erase_360 (ops other : ExternalFuns) :
    @prover.folded_leaves _ (replace ops other) = @prover.folded_leaves _ ops := by
  delta prover.folded_leaves
  try simp only [erase_359 ops other]
  all_goals rfl
#print axioms erase_360

/-- Full symbolic source-function equality for `transport.Variant.Insts.CoreCmpPartialEqVariant`. -/
theorem erase_361 (ops other : ExternalFuns) :
    @transport.Variant.Insts.CoreCmpPartialEqVariant _ (replace ops other) = @transport.Variant.Insts.CoreCmpPartialEqVariant _ ops := by
  delta transport.Variant.Insts.CoreCmpPartialEqVariant
  all_goals rfl
#print axioms erase_361

/-- Full symbolic source-function equality for `prover.public_check`. -/
theorem erase_362 (ops other : ExternalFuns) :
    @prover.public_check _ (replace ops other) = @prover.public_check _ ops := by
  delta prover.public_check
  try simp only [erase_361 ops other]
  all_goals rfl
#print axioms erase_362

/-- Full symbolic source-function equality for `prover.round_loop0_loop0_loop0.body`. -/
theorem erase_363 (ops other : ExternalFuns) :
    @prover.round_loop0_loop0_loop0.body _ (replace ops other) = @prover.round_loop0_loop0_loop0.body _ ops := by
  delta prover.round_loop0_loop0_loop0.body
  all_goals rfl
#print axioms erase_363

/-- Full symbolic source-function equality for `prover.round_loop0_loop0_loop0`. -/
theorem erase_364 (ops other : ExternalFuns) :
    @prover.round_loop0_loop0_loop0 _ (replace ops other) = @prover.round_loop0_loop0_loop0 _ ops := by
  delta prover.round_loop0_loop0_loop0
  try simp only [erase_363 ops other]
  all_goals rfl
#print axioms erase_364

/-- Full symbolic source-function equality for `prover.round_loop0_loop0.body`. -/
theorem erase_365 (ops other : ExternalFuns) :
    @prover.round_loop0_loop0.body _ (replace ops other) = @prover.round_loop0_loop0.body _ ops := by
  delta prover.round_loop0_loop0.body
  try simp only [erase_364 ops other]
  all_goals rfl
#print axioms erase_365

/-- Full symbolic source-function equality for `prover.round_loop0_loop0`. -/
theorem erase_366 (ops other : ExternalFuns) :
    @prover.round_loop0_loop0 _ (replace ops other) = @prover.round_loop0_loop0 _ ops := by
  delta prover.round_loop0_loop0
  try simp only [erase_365 ops other]
  all_goals rfl
#print axioms erase_366

/-- Full symbolic source-function equality for `prover.round_loop0.body`. -/
theorem erase_367 (ops other : ExternalFuns) :
    @prover.round_loop0.body _ (replace ops other) = @prover.round_loop0.body _ ops := by
  delta prover.round_loop0.body
  try simp only [erase_366 ops other]
  all_goals rfl
#print axioms erase_367
end R1Z.PDict_FmtErase
