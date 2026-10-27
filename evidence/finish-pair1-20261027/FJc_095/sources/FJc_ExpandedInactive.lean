import FJc_FiniteSums
import FJc_GroupAlgebra
import FJc_MaskTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_ExpandedInactive
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)
open scoped BigOperators

def group (j : Fin 64) : Fin 12 :=
  ⟨FJc_InactiveCoefficientsModel.group j.val,by
    change FJc_GroupTable.group j.val<12
    exact FJc_GroupTable.bound j.val j.isLt⟩

theorem group_eq (j : Fin 64) (g : Fin 12) :
    group j=g ↔ FJc_InactiveCoefficientsModel.group j.val=g.val := Fin.ext_iff

/-- Exact redistribution of source-grouped values into original coefficient/
low-coordinate pairs. Group membership bounds are derived from source data. -/
theorem selected (f : Slice U8) (low : Array NE 16#usize) :
    FJc_InactiveValue.sumPrefix f low 12=
      ∑ j : Fin 64,∑ s : Fin 16,
        if FJc_S2Rows.selected j.val s.val then
          FJc_InactiveCoefficientsModel.field f j.val*FIp_ArrayValue.value low s.val else 0 := by
  rw [FJc_FiniteSums.groups,←Fin.sum_univ_eq_sum_range]
  simp_rw [FJc_FiniteSums.coefficients,FJc_FiniteSums.subset,←Fin.sum_univ_eq_sum_range]
  have h := FJc_GroupAlgebra.distribute (s:=16) group
    (fun j=>FJc_InactiveCoefficientsModel.field f j.val)
    (fun g s=>decide ((FJc_SubsetModel.mask g.val &&& 2^s.val)≠0))
    (fun s=>FIp_ArrayValue.value low s.val)
  simp only [group_eq,decide_eq_true_eq] at h
  exact h

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
#print axioms group_eq
#print axioms selected
#print axioms arithmetic_row
end AspisR1.FJc_ExpandedInactive
end
