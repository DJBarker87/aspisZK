import R1Z.PDict_FmtSemantics
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]

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

end R1Z.PDict_FmtErase
