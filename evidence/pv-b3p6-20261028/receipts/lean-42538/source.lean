import Aeneas.Std
namespace PV_B3P_ByteBounds226
open Aeneas Aeneas.Std
set_option autoImplicit false

-- Arithmetic facts for every dynamic indexing region of byte_at. These are
-- natural-number obligations; linkage to wrapping scalar operations is separate.
theorem digest_index (i start : Nat) (lo : start ≤ i) (hi : i < start + 32) :
    (i - start) / 4 < 8 ∧ (i - start) % 4 < 4 := by omega

theorem frontier_index (i start : Nat) (lo : start ≤ i) (hi : i < start + 640) :
    (i - start) / 32 < 20 ∧ ((i - start) % 32) / 4 < 8 ∧
      (i - start) % 4 < 4 := by omega

theorem index_shift (i start : Nat) (lo : start ≤ i) (hi : i < start + 8) :
    8 * (i - start) < 64 := by omega

theorem chunks_cover (i : Nat) (hi : i < 1472) :
    i / 64 < 23 ∧ i % 64 < 64 ∧ 64 * (i / 64) + i % 64 = i := by omega

theorem full_byte_domain (i : Nat) (variant : Bool)
    (hi : i < if variant then 1427 else 1455) : i < 1472 := by
  cases variant <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> omega

theorem padded_suffix (n i : Nat) (hn : n = 1427 ∨ n = 1455)
    (hi : n ≤ i) (limit : i < 1472) :
    i - n < 45 := by rcases hn with rfl | rfl <;> omega

#print axioms digest_index
#print axioms frontier_index
#print axioms index_shift
#print axioms chunks_cover
#print axioms full_byte_domain
#print axioms padded_suffix
end PV_B3P_ByteBounds226
