import R1Z.PV_RDB2_SumNative
set_option autoImplicit false
noncomputable section
namespace PV_B1_SumOriginal
open Aeneas Aeneas.Std Result PV_B1_230 PV_B1_SumControl

-- crates/aspis-statement/src/state_only_semantic.rs:583–585 at c57a344726:
-- (h1.len() == TRACE_ROWS).then(|| h1.iter().copied().fold(QM31::ZERO, QM31::add))
-- The iterator visits the slice in order; add is the native CT limb operation,
-- whose complete extracted Result is proved in PV_B1_SumNative.add_source.
def original_row (h1 : Slice Q) : Option Q :=
  if Slice.len h1 = 1024#usize then
    some (h1.val.foldl PV_B1_SumNative.add aspis_core.field.QM31.ZERO)
  else none

theorem op230_source (h1 : Slice Q) :
    state_only_copy_helper_sum h1 = ok (original_row h1) := by
  rw [PV_B1_SumNative.op230_source]
  unfold original_row TRACE_ROWS
  rfl

theorem wrong_length (h1 : Slice Q) (h : Slice.len h1 ≠ 1024#usize) :
    state_only_copy_helper_sum h1 = ok none := by
  rw [op230_source]
  simp only [original_row,h,if_false]

theorem exact_length (h1 : Slice Q) (h : Slice.len h1 = 1024#usize) :
    state_only_copy_helper_sum h1 =
      ok (some (h1.val.foldl PV_B1_SumNative.add aspis_core.field.QM31.ZERO)) := by
  rw [op230_source]
  simp only [original_row,h,if_true]

#print axioms op230_source
#print axioms wrong_length
#print axioms exact_length
end PV_B1_SumOriginal
