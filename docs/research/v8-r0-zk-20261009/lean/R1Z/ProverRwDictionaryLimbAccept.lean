import R1Z.ProverRwDictionaryLimbs
set_option autoImplicit false
namespace R1Z.ProverRwDictionaryLimbAccept
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryLimbs

/-- A retained eight-limb invariant suffices to derive success, rather than
supplying the parser result as a hypothesis. -/
theorem accepted (w : Nat → U32) (valid : ∀ i, i < 8 → w i < P) :
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs
      (ProverCommitArray49.array 8#usize w) = .ok (some (packed w)) := by
  rw [total]
  have h : ∀ i, i < 8 → ¬ w i >= P := fun i hi => not_le.mpr (valid i hi)
  simp only [decode,h 0 (by omega),h 1 (by omega),h 2 (by omega),h 3 (by omega),
    h 4 (by omega),h 5 (by omega),h 6 (by omega),h 7 (by omega),if_false]

#print axioms accepted
end R1Z.ProverRwDictionaryLimbAccept
