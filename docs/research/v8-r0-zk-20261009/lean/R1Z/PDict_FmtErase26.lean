import R1Z.PDict_FmtErase25
import R1Z.PDict_VolatileCell
import R1Z.PrivacyR1HeadlineDeployedReal
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
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

/-- Full symbolic source-function equality for `prover.publish_compact`. -/
theorem erase_420 (ops other : ExternalFuns) :
    @prover.publish_compact _ (replace ops other) = @prover.publish_compact _ ops := by
  delta prover.publish_compact
  try simp only [erase_396 ops other, erase_405 ops other, erase_419 ops other]
  all_goals rfl
#print axioms erase_420

/-- Full symbolic source-function equality for `prover.prove_from_semantics`. -/
theorem erase_421 (ops other : ExternalFuns) :
    @prover.prove_from_semantics _ (replace ops other) = @prover.prove_from_semantics _ ops := by
  delta prover.prove_from_semantics
  try simp only [erase_341 ops other, erase_372 ops other, erase_392 ops other, erase_420 ops other]
  all_goals rfl
#print axioms erase_421

/-- Full symbolic source-function equality for `prover.semantic_error`. -/
theorem erase_422 (ops other : ExternalFuns) :
    @prover.semantic_error _ (replace ops other) = @prover.semantic_error _ ops := by
  delta prover.semantic_error
  all_goals rfl
#print axioms erase_422

/-- Full symbolic source-function equality for `prover.prove_masked_with_attempt`. -/
theorem erase_423 (ops other : ExternalFuns) :
    @prover.prove_masked_with_attempt _ (replace ops other) = @prover.prove_masked_with_attempt _ ops := by
  delta prover.prove_masked_with_attempt
  try simp only [erase_59 ops other, erase_60 ops other, erase_61 ops other, erase_83 ops other, erase_108 ops other, erase_116 ops other, erase_134 ops other, erase_257 ops other, erase_325 ops other, erase_336 ops other, erase_341 ops other, erase_342 ops other, erase_421 ops other, erase_422 ops other]
  all_goals rfl
#print axioms erase_423

/-- Full symbolic source-function equality for `prover.prove_masked_attempt`. -/
theorem erase_424 (ops other : ExternalFuns) :
    @prover.prove_masked_attempt _ (replace ops other) = @prover.prove_masked_attempt _ ops := by
  delta prover.prove_masked_attempt
  try simp only [erase_56 ops other, erase_423 ops other]
  all_goals rfl
#print axioms erase_424

/-- Full symbolic source-function equality for `prover.retry_attempt`. -/
theorem erase_425 (ops other : ExternalFuns) :
    @prover.retry_attempt _ (replace ops other) = @prover.retry_attempt _ ops := by
  funext T callback public compiled variant hash
  delta prover.retry_attempt
  apply fixed_equal
  funext recur nonce_store next_attempt k
  try simp only [erase_424 ops other]
  all_goals rfl
#print axioms erase_425
/-- Every return, failure and divergence of the full recursive retry execution
is unchanged when only the Formatter operation is replaced. -/
theorem retry_without_formatter (ops other : ExternalFuns) :
    @prover.retry_attempt _ (replace ops other) = @prover.retry_attempt _ ops :=
  erase_425 ops other
#print axioms retry_without_formatter
#print axioms R1Z.PDict_VolatileCell.op124_installed
#print R1Z.ProverCommitDeployedFuel22.RustProverRefinement
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
end R1Z.PDict_FmtErase
