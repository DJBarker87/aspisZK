import FJc_FiniteSums
import FJc_GroupNat
import FJc_MaskTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_ExpandedInactive
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)
open scoped BigOperators

theorem coefficient_group (j : Nat) :
    FJc_InactiveCoefficientsModel.group j=FJc_GroupTable.group j := rfl

/-- Exact redistribution of source-grouped values into original coefficient/
low-coordinate pairs. Group membership bounds are derived from source data. -/
theorem selected (f : Slice U8) (low : Array NE 16#usize) :
    FJc_InactiveValue.sumPrefix f low 12=
      ∑ j : Fin 64,∑ s : Fin 16,
        if FJc_S2Rows.selected j.val s.val then
          FJc_InactiveCoefficientsModel.field f j.val*FIp_ArrayValue.value low s.val else 0 := by
  rw [FJc_FiniteSums.groups,←Fin.sum_univ_eq_sum_range]
  simp_rw [FJc_FiniteSums.coefficients,FJc_FiniteSums.subset,←Fin.sum_univ_eq_sum_range]
  simp_rw [coefficient_group]
  have h := FJc_GroupNat.distribute (n:=64) (g:=12) (s:=16)
    (fun j=>FJc_GroupTable.group j.val) (fun j=>FJc_GroupTable.bound j.val j.isLt)
    (fun j=>FJc_InactiveCoefficientsModel.field f j.val)
    (fun g s=>decide ((FJc_SubsetModel.mask g &&& 2^s.val)≠0))
    (fun s=>FIp_ArrayValue.value low s.val)
  simpa only [decide_eq_true_eq,FJc_S2Rows.selected] using h

theorem arithmetic_row (f : Slice U8) (low : Array NE 16#usize) :
    FJc_InactiveValue.sumPrefix f low 12=
      ∑ j : Fin 64,∑ s : Fin 16,
        if FJc_S2Rows.inactive j.val s.val then
          FJc_InactiveCoefficientsModel.field f j.val*FIp_ArrayValue.value low s.val else 0 := by
  rw [selected]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  simp only [FJc_MaskTable.value j.val s.val j.isLt s.isLt]
#print axioms coefficient_group
#print axioms selected
#print axioms arithmetic_row
end AspisR1.FJc_ExpandedInactive
end
