import AspisV8R13.AdaptiveHistory

/-!
In the source-shaped diagnostic the changed private keys have lengths 79
(main expansion) and 220 (C2 leaves). Public suffix calls have lengths
33,52,467; earlier entry framing is separately checked in the executable KAT.
This arithmetic NEVER classifies arbitrary adversarial calls as public-safe.
DRAFT: not compiled.
-/
set_option autoImplicit false
namespace AspisV8R14

theorem first_three_public_frames_not_c2 (n : Nat)
    (shape : n = 33 ∨ n = 52 ∨ n = 467) : n ≠ 220 := by
  rcases shape with h | h | h <;> subst n <;> decide

theorem first_three_public_frames_not_expansion (n : Nat)
    (shape : n = 33 ∨ n = 52 ∨ n = 467) : n ≠ 79 := by
  rcases shape with h | h | h <;> subst n <;> decide

/-- Byte equality forces length equality; use this only after proving the
literal framing and all modified families for the chosen source profile. -/
theorem lists_disjoint_of_length {A : Type*} (x y : List A)
    (lengths : x.length ≠ y.length) : x ≠ y := by
  intro h; exact lengths (congrArg List.length h)

#print axioms first_three_public_frames_not_c2
#print axioms first_three_public_frames_not_expansion
#print axioms lists_disjoint_of_length
end AspisV8R14
