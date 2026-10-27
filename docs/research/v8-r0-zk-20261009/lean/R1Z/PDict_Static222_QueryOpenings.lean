import R1Z.PDict_Static222_OpeningValues
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap


/-- Full symbolic source-function equality for `prover.append_query_openings_loop`. -/
theorem erase_418 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_query_openings_loop (types base F) (selected base F ops) = @prover.append_query_openings_loop base ops := by
  delta prover.append_query_openings_loop
  try simp only [erase_417 base F ops]
  all_goals rfl
#print axioms erase_418

/-- Full symbolic source-function equality for `prover.append_query_openings`. -/
theorem erase_419 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_query_openings (types base F) (selected base F ops) = @prover.append_query_openings base ops := by
  delta prover.append_query_openings
  try simp only [erase_418 base F ops]
  all_goals rfl
#print axioms erase_419

end R1Z.PDict_Static222
