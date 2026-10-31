import Aeneas
set_option autoImplicit false
namespace NEC_HeaderMonad
open Aeneas Result

theorem ok_if {α : Type} (condition : Prop) [Decidable condition] (left right : α) :
 Result.ok (if condition then left else right) =
 (if condition then Result.ok left else Result.ok right) := by
 by_cases h : condition <;> simp [h]

#print axioms ok_if
end NEC_HeaderMonad
