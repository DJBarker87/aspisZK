import PV_B3P_NextFormatting569227
namespace PV_B3P_PreconditionFormatting569227
open Aeneas Aeneas.Std
set_option autoImplicit false
/-- An arbitrary failing-check continuation, with no formatter interpretation. -/
def check (panic : Result Unit) (condition : Prop) [Decidable condition] : Result Unit :=
  if condition then .ok () else panic

theorem check_safe (panic : Result Unit) (condition : Prop) [Decidable condition]
    (safe : condition) : check panic condition = .ok () := by
  simp only [check,safe,if_true]

/-- IndexRange's constructor invariant and nonempty loop test imply both the
assert_unchecked operand and the unchecked successor precondition. -/
theorem index_range_conditions (start finish : Usize)
    (ordered : start.val ≤ finish.val) (active : start ≠ finish) :
    start.val < finish.val ∧ start.val+1 ≤ UScalar.max .Usize ∧
      (Usize.wrapping_add start 1#usize).val ≤ finish.val := by
  have different : start.val ≠ finish.val := by
    intro equal
    exact active (UScalar.eq_of_val_eq equal)
  have inside : start.val < finish.val := by omega
  have increment := PV_B3P_NthSourceFinal559227.increment_wrap start finish inside
  have nowrap : (Usize.wrapping_add start 1#usize).val = start.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    exact Nat.mod_eq_of_lt (PV_B3Q_RangeActual.increment_safe ⟨start,finish⟩ inside)
  constructor
  · exact inside
  constructor
  · scalar_tac
  · omega

theorem index_range_checks (assert_panic add_panic : Result Unit)
    (start finish : Usize) (ordered : start.val ≤ finish.val) (active : start ≠ finish) :
    check assert_panic (start.val < finish.val) = .ok () ∧
    check add_panic (start.val+1 ≤ UScalar.max .Usize) = .ok () := by
  have facts := index_range_conditions start finish ordered active
  exact ⟨check_safe _ _ facts.1,check_safe _ _ facts.2.1⟩

/-- Exactly the initializer's while guard supplies the mutable unchecked-index
and unchecked-add conditions; it also preserves the initialized-prefix bound. -/
theorem initializer_conditions (initialized length : Usize)
    (active : initialized.val < length.val) :
    initialized.val < length.val ∧ initialized.val+1 ≤ UScalar.max .Usize ∧
      (Usize.wrapping_add initialized 1#usize).val ≤ length.val :=
  index_range_conditions initialized length (by omega) (by
    intro same
    subst initialized
    omega)

theorem initializer_checks (index_panic add_panic : Result Unit)
    (initialized length : Usize) (active : initialized.val < length.val) :
    check index_panic (initialized.val < length.val) = .ok () ∧
    check add_panic (initialized.val+1 ≤ UScalar.max .Usize) = .ok () := by
  have facts := initializer_conditions initialized length active
  exact ⟨check_safe _ _ facts.1,check_safe _ _ facts.2.1⟩

/-- The source ZST slice-next subtraction is dominated by len != 0. No pointer
or non-ZST region semantics is inferred from this arithmetic fact. -/
theorem slice_subtraction_check (panic : Result Unit) (length : Usize)
    (nonempty : length ≠ 0#usize) :
    check panic (1 ≤ length.val) = .ok () := by
  apply check_safe
  have nonzero : length.val ≠ 0 := by
    intro equal
    exact nonempty (UScalar.eq_of_val_eq equal)
  omega

/-- Shared and mutable unchecked-index checks use the same exact strict bound. -/
theorem unchecked_index_check (panic : Result Unit) (index length : Usize)
    (inside : index.val < length.val) :
    check panic (index.val < length.val) = .ok () := check_safe _ _ inside
#print axioms check_safe
#print axioms index_range_conditions
#print axioms index_range_checks
#print axioms initializer_conditions
#print axioms initializer_checks
#print axioms slice_subtraction_check
#print axioms unchecked_index_check
end PV_B3P_PreconditionFormatting569227
