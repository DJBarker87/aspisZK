import Aeneas

/-! Candidate value representation for the exact retained Charon TPattern.
This does not install a Rust type or assert native/extractor correspondence. -/
set_option autoImplicit false
namespace R1Z.ProverRwRngTransportValidity
open Aeneas.Std

/-- Inclusive endpoints from rng-caller-aeneas-003's retained TPattern. -/
def Pattern (x : I32) : Prop :=
  (-2147483648 ≤ x.val ∧ x.val ≤ -1) ∨ (1 ≤ x.val ∧ x.val ≤ 2147483647)

abbrev PatternValue := { x : I32 // Pattern x }
abbrev ValidI32 := { x : I32 // x.val ≠ 0 }

/-- I32's own bounds supply the endpoints; only zero is excluded. -/
theorem pattern_iff_nonzero (x : I32) : Pattern x ↔ x.val ≠ 0 := by
  have bounds := x.hBounds
  change (-2147483648 ≤ x.val ∧ x.val < 2147483648) at bounds
  unfold Pattern
  omega

def toValid (x : PatternValue) : ValidI32 :=
  ⟨x.val, (pattern_iff_nonzero x.val).mp x.property⟩

def toPattern (x : ValidI32) : PatternValue :=
  ⟨x.val, (pattern_iff_nonzero x.val).mpr x.property⟩

theorem toValid_preserves_value (x : PatternValue) : (toValid x).val = x.val := rfl

theorem pattern_roundtrip (x : PatternValue) : toPattern (toValid x) = x := by
  apply Subtype.ext
  rfl

theorem valid_roundtrip (x : ValidI32) : toValid (toPattern x) = x := by
  apply Subtype.ext
  rfl

#print axioms pattern_iff_nonzero
#print axioms toValid_preserves_value
#print axioms pattern_roundtrip
#print axioms valid_roundtrip
end R1Z.ProverRwRngTransportValidity
