import R1Z.ProverCommitSemanticTransport26
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultTransport
open Aeneas Aeneas.Std Result ProverCommitSemanticTransport26

theorem map_comp {A B C : Type} (first : A → B) (second : B → C) (m : Result A) :
    mapR second (mapR first m) = mapR (second ∘ first) m := by
  cases m <;> rfl

/-- Change only a returned state carrier; failures and divergence are retained.
This is the naturality step needed at the actual reservation callback. -/
theorem bind_map {A B C D : Type} (input : A → B) (output : C → D)
    (m : Result A) (left : A → Result C) (right : B → Result D)
    (continuation : ∀ a, mapR output (left a) = right (input a)) :
    mapR output (m >>= left) = mapR input m >>= right := by
  cases m with
  | fail e => rfl
  | div => rfl
  | ok a => exact continuation a

#print axioms map_comp
#print axioms bind_map
end R1Z.PV_RunJoin_ResultTransport
