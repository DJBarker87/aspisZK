import SelectedSelectorToSemanticWeight
import PositivePackBinding

/-! The exact boundary between Rust `semantic_packed` and the opt-in positive
transfer lane.

`semantic_packed` has 94 source positions, 0 through 93.  The selected
positive model has a 95th position at index 94, inserted by the research
`payment_terminal` wrapper as `terminal_delta`.  Thus a direct identity
between `semantic_packed` and the 95-position `packedRows` object is false.
This leaf proves the minimal mismatch and the exact additive correction in
the final four-slot pack.  It neither assumes terminal acceptance nor drops
the positive constraint. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedSemanticPackedBoundary
open AspisV5ComponentCQM31TowerExact
open AspisPool.V7PairForestCuArithmeticEquivalences
open AspisV8.PositiveTerminalInsertion
open AspisV8.PositivePackBinding

/-- Last source pack emitted by the 94-position `semantic_packed`: positions
92 and 93 are the two asset residuals; positions 94 and 95 are zero. -/
def base94LastPack (row : Nat) (asset publicAsset : QM31Exact) : QM31Exact :=
  literalPack ![
    rowSelector 44 row * (asset - publicAsset),
    (rowSelector 508 row + rowSelector 460 row) * (asset - publicAsset),
    0, 0]

/-- The separately inserted positive lane is exactly the missing slot 2. -/
theorem selected95LastPack_eq_base94_add_positive
    (row : Nat) (asset publicAsset r c inv : QM31Exact) :
    sourceLastPack row asset publicAsset r c inv =
      base94LastPack row asset publicAsset +
        literalPack ![0, 0, rowSelector 1014 row * (r * c * inv - 1), 0] := by
  simpa [sourceLastPack, base94LastPack, addSlot2, literalPack_eq_tower_map] using
    (pack_slot2_add towerI towerU
      ![rowSelector 44 row * (asset - publicAsset),
        (rowSelector 508 row + rowSelector 460 row) * (asset - publicAsset), 0, 0]
      (rowSelector 1014 row * (r * c * inv - 1)))

/-- At the reserved positive row, the actual 94-position source pack is zero
for equal asset claims, independent of the product-inverse witness. -/
theorem base94LastPack_row1014 (asset : QM31Exact) :
    base94LastPack 1014 asset asset = 0 := by
  rcases row1014_selector_separation with ⟨h44, h508, h460, _⟩
  simp only [base94LastPack, h44, h508, h460, zero_mul, zero_add, sub_self]
  ext <;> simp [literalPack]

/-- Minimal counterexample to identifying the 94-position source output with
the selected 95-position model before applying `terminal_delta`. -/
theorem direct_semanticPacked_to_selected95_false :
    sourceLastPack 1014 0 0 0 0 0 ≠ base94LastPack 1014 0 0 := by
  rw [row1014_last_pack, base94LastPack_row1014]
  simp only [zero_mul, zero_sub, mul_neg, mul_one]
  exact neg_ne_zero.mpr towerU_ne_zero

#print axioms selected95LastPack_eq_base94_add_positive
#print axioms base94LastPack_row1014
#print axioms direct_semanticPacked_to_selected95_false
end AspisV8Completion.SelectedSemanticPackedBoundary
