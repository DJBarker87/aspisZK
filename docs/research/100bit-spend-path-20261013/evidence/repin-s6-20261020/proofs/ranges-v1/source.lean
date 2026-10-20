import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

/-! Local integer and indexing obligations of the frozen adapter stage1.
These facts do not assert totality of SDK, decoder, validator or tx1 children. -/
set_option autoImplicit false
namespace AspisR1.RepinS6Ranges

/-- The admitted stage1 instruction is exactly two bytes and k is 10 or 11. -/
theorem instruction_indices (length k : Nat)
    (h : length = 2 ∧ (k = 10 ∨ k = 11)) :
    1 < length ∧ k ≤ 11 ∧ k < 4294967296 := by omega

/-- All three account indexes are guarded before the first account read. -/
theorem account_indices (length : Nat) (h : length = 3) :
    0 < length ∧ 1 < length ∧ 2 < length := by omega

/-- Both additions are constants, independent of malformed input bytes.
The proof prefix is 688 bytes and the frozen compact proof is 57607 bytes. -/
theorem local_additions (machineMax : Nat) (h : 4294967295 ≤ machineMax) :
    688 + 57607 ≤ machineMax ∧ 688 + 8 ≤ machineMax ∧
    688 + 57607 = 58295 ∧ 688 + 8 = 696 := by omega

/-- The length guard protects the candidate comparison, tag read and proof
subslice. The later OR conditions need not be assumed true. -/
theorem proof_indices (length : Nat) (h : length = 688 + 57607) :
    688 ≤ length ∧ 688 + 8 < length ∧
    688 ≤ 688 + 57607 ∧ 688 + 57607 ≤ length ∧
    (688 + 57607) - 688 = 57607 := by omega

/-- Equal lengths are the copy_from_slice precondition after tx1 succeeds. -/
theorem checkpoint_copy (outputLength checkpointLength : Nat)
    (h : outputLength = checkpointLength) : outputLength ≤ checkpointLength := by omega

#print axioms instruction_indices
#print axioms account_indices
#print axioms local_additions
#print axioms proof_indices
#print axioms checkpoint_copy
end AspisR1.RepinS6Ranges
