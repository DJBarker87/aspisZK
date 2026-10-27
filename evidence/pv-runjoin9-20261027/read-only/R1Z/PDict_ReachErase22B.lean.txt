import R1Z.PDict_ReachErase22A
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_ReachErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

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
end R1Z.PDict_ReachErase
