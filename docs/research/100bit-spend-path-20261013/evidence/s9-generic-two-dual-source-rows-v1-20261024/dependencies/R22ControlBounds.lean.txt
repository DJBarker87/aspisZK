import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! Small symbolic index/range obligations for the arithmetic inventory.
These do not assert a source/extraction correspondence for unextracted cones. -/
set_option autoImplicit false
namespace AspisR1.R22ControlBounds

/-- Rows used by ten rounds and prepare fit the stored U8 transcript tags. -/
theorem round_rows (round : Nat) (h : round < 10) :
    15 + round < 256 ∧ 160 + (15 + round) < 256 ∧
    (15 + round) + 1 < 256 ∧ round < 10 := by omega

theorem prepare_rows (row : Nat) (h : row ≤ 32) :
    160 + row < 256 ∧ (row < 32 → row + 1 ≤ 32) := by omega

/-- No dependency on a concrete array enumeration. -/
theorem horner_indices (index round : Nat) (hi : 0 < index ∧ index ≤ 28)
    (hr : round < 10) : index - 1 < 28 ∧ round < 10 := by omega

theorem boundary_successor (index : Nat) (hi : index < 28) :
    index < 28 ∧ index + 1 ≤ 28 := by omega

/-- Includes byte offsets for all four base-dot slots and their tails. -/
theorem fast_dot_offsets (slot term byte : Nat)
    (hs : slot < 4) (ht : term < 26) (hb : byte < 4) :
    120*slot + 4*term + byte < 480 ∧ term < 29 := by omega

theorem fast_dot_tails (slot term byte : Nat)
    (hs : slot < 4) (ht : term < 2) (hb : byte < 16) :
    480 + slot*32 + term*16 + byte < 608 ∧ term + 26 < 29 := by omega

theorem weights_digits (j s : Nat) (hj : j < 64) (hs : s < 16) :
    16*j+s < 1024 := by omega

theorem libra_indices (index : Nat) (h : index < 56) :
    index/28 < 2 ∧ index%28 < 28 := by omega

theorem point_indices (tau : Nat) (h : tau < 5) :
    2*tau ≤ 8 ∧ 9-2*tau < 10 ∧ 8-2*tau < 10 ∧
    2*tau ≤ 9 := by omega

/-- Each multiplication/addition in a sampler byte-word index is bounded. -/
theorem sampler_word_indices (i byte : Nat) (hi : i < 8) (hb : byte < 4) :
    4*i < 32 ∧ 4*i+byte < 32 ∧ i+1 ≤ 8 := by omega

/-- Widened long-division dividend after remainder reduction fits U64. -/
theorem sampler_dividend (remainder word : Nat)
    (hr : remainder < 2147483647) (hw : word < 4294967296) :
    remainder*4294967296 < 9223372036854775808 ∧
    remainder*4294967296+word < 9223372036854775808 := by omega

#print axioms round_rows
#print axioms prepare_rows
#print axioms horner_indices
#print axioms boundary_successor
#print axioms fast_dot_offsets
#print axioms fast_dot_tails
#print axioms weights_digits
#print axioms libra_indices
#print axioms point_indices
#print axioms sampler_word_indices
#print axioms sampler_dividend
end AspisR1.R22ControlBounds
