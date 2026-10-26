import R1Z.PDict_Static222_21
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
/-- Carrier transport candidate for `prover.fold_cell`. -/
theorem erase_352 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.fold_cell (types base F) (selected base F ops) = @prover.fold_cell base ops := by
  delta prover.fold_cell
  all_goals rfl
#print axioms erase_352

/-- Carrier transport candidate for `prover.fold_loop.body`. -/
theorem erase_353 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.fold_loop.body (types base F) (selected base F ops) = @prover.fold_loop.body base ops := by
  delta prover.fold_loop.body
  try simp only [erase_352 base F ops]
  all_goals rfl
#print axioms erase_353

/-- Carrier transport candidate for `prover.fold_loop`. -/
theorem erase_354 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.fold_loop (types base F) (selected base F ops) = @prover.fold_loop base ops := by
  delta prover.fold_loop
  try simp only [erase_353 base F ops]
  all_goals rfl
#print axioms erase_354

/-- Carrier transport candidate for `prover.fold`. -/
theorem erase_355 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.fold (types base F) (selected base F ops) = @prover.fold base ops := by
  delta prover.fold
  try simp only [erase_354 base F ops]
  all_goals rfl
#print axioms erase_355

/-- Carrier transport candidate for `prover.folded_leaves_loop0_loop0.body`. -/
theorem erase_356 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.folded_leaves_loop0_loop0.body (types base F) (selected base F ops) = @prover.folded_leaves_loop0_loop0.body base ops := by
  delta prover.folded_leaves_loop0_loop0.body
  all_goals rfl
#print axioms erase_356

/-- Carrier transport candidate for `prover.folded_leaves_loop0_loop0`. -/
theorem erase_357 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.folded_leaves_loop0_loop0 (types base F) (selected base F ops) = @prover.folded_leaves_loop0_loop0 base ops := by
  delta prover.folded_leaves_loop0_loop0
  try simp only [erase_356 base F ops]
  all_goals rfl
#print axioms erase_357

end R1Z.PDict_Static222
