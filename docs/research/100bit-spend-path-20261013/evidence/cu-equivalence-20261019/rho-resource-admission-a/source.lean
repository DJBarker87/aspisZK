import CuSavingsRhoAllocationSuccess
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoResourceAdmission
open Aeneas Aeneas.Std

/-- Pinned std Layout::repeat_packed checks size*count and then
from_size_alignment checks size <= isize::MAX+1-align. For the actual
32-byte/8-aligned raw residue rows, every guard is discharged symbolically.
RawVec starts at cap=len=0, so checked_add yields count and selects allocate,
not grow/copy. The zero-count path performs no allocation. -/
theorem layout_admitted (count : Nat) (hn : count ≤ 256) :
    32*count ≤ 8192 ∧ 32*count ≤ 9223372036854775800 ∧
    32*count < 18446744073709551616 ∧ (32*count)%8=0 := by
  refine ⟨by omega,by omega,by omega,?_⟩
  simp only [Nat.mul_mod,show 32%8=0 by decide,Nat.zero_mul,Nat.zero_mod]

/-- The alignment-aware size guard used by the pinned 64-bit std constructor. -/
theorem std_guard_constant : (2^63 : Nat)-8=9223372036854775800 := by decide

/-- Combined extra reservation (not a claim that all 256 KiB are free).
Supply a remaining common allocation budget at the actual stage boundary. -/
theorem sufficient_raw_budget (count remaining future : Nat) (hn : count ≤ 256)
    (hf : 8199+future ≤ remaining) : 32*count+7+future ≤ remaining := by omega

theorem sufficient_s2_budget (remaining future : Nat)
    (hf : 2055+future ≤ remaining) : 32*64+7+future ≤ remaining := by omega

#print axioms layout_admitted
#print axioms std_guard_constant
#print axioms sufficient_raw_budget
#print axioms sufficient_s2_budget
end AspisR1.CuSavingsRhoResourceAdmission
