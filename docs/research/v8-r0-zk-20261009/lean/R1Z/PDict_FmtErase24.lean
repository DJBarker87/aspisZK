import R1Z.PDict_FmtErase23
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

/-- Full symbolic source-function equality for `prover.opening_claim_bytes_loop`. -/
theorem erase_384 (ops other : ExternalFuns) :
    @prover.opening_claim_bytes_loop _ (replace ops other) = @prover.opening_claim_bytes_loop _ ops := by
  delta prover.opening_claim_bytes_loop
  try simp only [erase_383 ops other]
  all_goals rfl
#print axioms erase_384

/-- Full symbolic source-function equality for `prover.opening_claim_bytes`. -/
theorem erase_385 (ops other : ExternalFuns) :
    @prover.opening_claim_bytes _ (replace ops other) = @prover.opening_claim_bytes _ ops := by
  delta prover.opening_claim_bytes
  try simp only [erase_384 ops other]
  all_goals rfl
#print axioms erase_385

/-- Full symbolic source-function equality for `prover.opening_coefficients_loop.body`. -/
theorem erase_386 (ops other : ExternalFuns) :
    @prover.opening_coefficients_loop.body _ (replace ops other) = @prover.opening_coefficients_loop.body _ ops := by
  delta prover.opening_coefficients_loop.body
  try simp only [erase_273 ops other]
  all_goals rfl
#print axioms erase_386

/-- Full symbolic source-function equality for `prover.opening_coefficients_loop`. -/
theorem erase_387 (ops other : ExternalFuns) :
    @prover.opening_coefficients_loop _ (replace ops other) = @prover.opening_coefficients_loop _ ops := by
  delta prover.opening_coefficients_loop
  try simp only [erase_386 ops other]
  all_goals rfl
#print axioms erase_387

/-- Full symbolic source-function equality for `prover.opening_coefficients`. -/
theorem erase_388 (ops other : ExternalFuns) :
    @prover.opening_coefficients _ (replace ops other) = @prover.opening_coefficients _ ops := by
  delta prover.opening_coefficients
  try simp only [erase_387 ops other]
  all_goals rfl
#print axioms erase_388

/-- Full symbolic source-function equality for `prover.opening_inactive_loop.body`. -/
theorem erase_389 (ops other : ExternalFuns) :
    @prover.opening_inactive_loop.body _ (replace ops other) = @prover.opening_inactive_loop.body _ ops := by
  delta prover.opening_inactive_loop.body
  all_goals rfl
#print axioms erase_389

/-- Full symbolic source-function equality for `prover.opening_inactive_loop`. -/
theorem erase_390 (ops other : ExternalFuns) :
    @prover.opening_inactive_loop _ (replace ops other) = @prover.opening_inactive_loop _ ops := by
  delta prover.opening_inactive_loop
  try simp only [erase_389 ops other]
  all_goals rfl
#print axioms erase_390

/-- Full symbolic source-function equality for `prover.opening_inactive`. -/
theorem erase_391 (ops other : ExternalFuns) :
    @prover.opening_inactive _ (replace ops other) = @prover.opening_inactive _ ops := by
  delta prover.opening_inactive
  try simp only [erase_390 ops other]
  all_goals rfl
#print axioms erase_391

/-- Full symbolic source-function equality for `prover.prepare_opening`. -/
theorem erase_392 (ops other : ExternalFuns) :
    @prover.prepare_opening _ (replace ops other) = @prover.prepare_opening _ ops := by
  delta prover.prepare_opening
  try simp only [erase_59 ops other, erase_375 ops other, erase_276 ops other, erase_376 ops other, erase_347 ops other, erase_351 ops other, erase_355 ops other, erase_382 ops other, erase_385 ops other, erase_388 ops other, erase_391 ops other, erase_371 ops other, erase_361 ops other]
  all_goals rfl
#print axioms erase_392

/-- Full symbolic source-function equality for `host_compact.compact_semantic_row`. -/
theorem erase_393 (ops other : ExternalFuns) :
    @host_compact.compact_semantic_row _ (replace ops other) = @host_compact.compact_semantic_row _ ops := by
  delta host_compact.compact_semantic_row
  try simp only [erase_199 ops other]
  all_goals rfl
#print axioms erase_393

/-- Full symbolic source-function equality for `host_compact.compact_semantic_loop.body`. -/
theorem erase_394 (ops other : ExternalFuns) :
    @host_compact.compact_semantic_loop.body _ (replace ops other) = @host_compact.compact_semantic_loop.body _ ops := by
  delta host_compact.compact_semantic_loop.body
  try simp only [erase_393 ops other]
  all_goals rfl
#print axioms erase_394

/-- Full symbolic source-function equality for `host_compact.compact_semantic_loop`. -/
theorem erase_395 (ops other : ExternalFuns) :
    @host_compact.compact_semantic_loop _ (replace ops other) = @host_compact.compact_semantic_loop _ ops := by
  delta host_compact.compact_semantic_loop
  try simp only [erase_394 ops other]
  all_goals rfl
#print axioms erase_395

/-- Full symbolic source-function equality for `host_compact.compact_semantic`. -/
theorem erase_396 (ops other : ExternalFuns) :
    @host_compact.compact_semantic _ (replace ops other) = @host_compact.compact_semantic _ ops := by
  delta host_compact.compact_semantic
  try simp only [erase_395 ops other]
  all_goals rfl
#print axioms erase_396

/-- Full symbolic source-function equality for `host_tree.multiproof_levels`. -/
theorem erase_397 (ops other : ExternalFuns) :
    @host_tree.multiproof_levels _ (replace ops other) = @host_tree.multiproof_levels _ ops := by
  delta host_tree.multiproof_levels
  delta host_tree.multiproof_levels.mutual
  all_goals rfl
#print axioms erase_397

/-- Full symbolic source-function equality for `host_tree.check_indices_loop.body`. -/
theorem erase_398 (ops other : ExternalFuns) :
    @host_tree.check_indices_loop.body _ (replace ops other) = @host_tree.check_indices_loop.body _ ops := by
  delta host_tree.check_indices_loop.body
  all_goals rfl
#print axioms erase_398

/-- Full symbolic source-function equality for `host_tree.check_indices_loop`. -/
theorem erase_399 (ops other : ExternalFuns) :
    @host_tree.check_indices_loop _ (replace ops other) = @host_tree.check_indices_loop _ ops := by
  delta host_tree.check_indices_loop
  try simp only [erase_398 ops other]
  all_goals rfl
#print axioms erase_399
end R1Z.PDict_FmtErase
