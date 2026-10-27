import R0Z.PoseidonInternal

/-! Poseidon table facts, first one (DESIGN-BUILDER-MODEL §11.4 c): the copy's
INTERNAL_SHIFTS row satisfies the named facts `ShiftsBound` and `ShiftsOk`
used by `internal_round_lift`.  Fifteen lanes of small numerals (at most
16), each checked by `rfl`/`decide` after unfolding the one table; no
field element is involved. -/
set_option autoImplicit false

namespace R0Z.PoseidonRefine
open Aeneas Aeneas.Std Result R0PoseidonCopy

theorem internal_shifts_ok : ShiftsOk INTERNAL_SHIFTS := by
  intro ⟨j, hj⟩
  rw [INTERNAL_SHIFTS]
  interval_cases j <;> rfl

theorem internal_shifts_bound : ShiftsBound INTERNAL_SHIFTS := by
  intro j hj
  rw [INTERNAL_SHIFTS]
  interval_cases j <;> decide

end R0Z.PoseidonRefine

#print axioms R0Z.PoseidonRefine.internal_shifts_ok
#print axioms R0Z.PoseidonRefine.internal_shifts_bound
