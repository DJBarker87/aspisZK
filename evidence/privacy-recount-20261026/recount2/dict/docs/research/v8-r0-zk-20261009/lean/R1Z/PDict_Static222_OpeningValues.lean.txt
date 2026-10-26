import R1Z.PDict_Static222_25
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Static222
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap


/-- Full symbolic source-function equality for `prover.append_opening_values`. -/
theorem erase_416 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_opening_values (types base F) (selected base F ops) = @prover.append_opening_values base ops := by
  delta prover.append_opening_values
  try simp only [erase_412 base F ops, erase_415 base F ops]
  all_goals rfl
#print axioms erase_416

/-- Full symbolic source-function equality for `prover.append_query_openings_loop.body`. -/
theorem erase_417 (base : ExternalTypes) (F : Type) (ops : @ExternalFuns base) :
    @prover.append_query_openings_loop.body (types base F) (selected base F ops) = @prover.append_query_openings_loop.body base ops := by
  delta prover.append_query_openings_loop.body
  try simp only [erase_408 base F ops, erase_409 base F ops, erase_416 base F ops, erase_351 base F ops]
  all_goals rfl
#print axioms erase_417

end R1Z.PDict_Static222
