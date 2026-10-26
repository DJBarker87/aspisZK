import R1Z.ProverRwDictionaryLimbs
set_option autoImplicit false
namespace R1Z.ProverRwDictionaryLimbReject
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryLimbs

def valid (w : Nat → U32) : Prop :=
  ¬ w 0 >= P ∧ ¬ w 1 >= P ∧ ¬ w 2 >= P ∧ ¬ w 3 >= P ∧
  ¬ w 4 >= P ∧ ¬ w 5 >= P ∧ ¬ w 6 >= P ∧ ¬ w 7 >= P

/-- Exact rejection test. This is the real parser's eight finite guards,
not kernel normalization of a field recurrence. -/
theorem decode_none (w : Nat → U32) : decode w = none ↔ ¬ valid w := by
  unfold decode valid
  split_ifs <;> simp_all

/-- Exact success test removes both success and output-equality premises
when the canonical limb invariant is known. -/
theorem decode_some (w : Nat → U32) : decode w = some (packed w) ↔ valid w := by
  unfold decode valid
  split_ifs <;> simp_all

theorem rejected (w : Nat → U32) (invalid : ¬ valid w) :
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_limbs
      (ProverCommitArray49.array 8#usize w) = .ok none := by
  rw [total,(decode_none w).mpr invalid]

#print axioms decode_none
#print axioms decode_some
#print axioms rejected
end R1Z.ProverRwDictionaryLimbReject
