import FJc_InactiveValue
import FJc_GroupAlgebra
import FJc_GroupTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_InactiveRegroup
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)
open scoped BigOperators

theorem coefficients (f : Slice U8) (g n : Nat) :
    FJc_InactiveCoefficientsModel.sumPrefix f g n=
      ∑ j∈Finset.range n,if FJc_InactiveCoefficientsModel.group j=g then FJc_InactiveCoefficientsModel.field f j else 0 := by
  induction n with
  | zero=>simp only [FJc_InactiveCoefficientsModel.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih=>rw [FJc_InactiveCoefficientsModel.sumPrefix,Finset.sum_range_succ,ih]

theorem subset (low : Array NE 16#usize) (g n : Nat) :
    FJc_SubsetModel.sumPrefix low g n=
      ∑ s∈Finset.range n,if (FJc_SubsetModel.mask g &&& 2^s)≠0 then FIp_ArrayValue.value low s else 0 := by
  induction n with
  | zero=>simp only [FJc_SubsetModel.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih=>rw [FJc_SubsetModel.sumPrefix,Finset.sum_range_succ,ih]

theorem groups (f : Slice U8) (low : Array NE 16#usize) (n : Nat) :
    FJc_InactiveValue.sumPrefix f low n=
      ∑ g∈Finset.range n,FJc_InactiveCoefficientsModel.sumPrefix f g 64*FJc_SubsetModel.sumPrefix low g 16 := by
  induction n with
  | zero=>simp only [FJc_InactiveValue.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih=>rw [FJc_InactiveValue.sumPrefix,Finset.sum_range_succ,ih]

theorem value (f : Slice U8) (low : Array NE 16#usize) :
    FJc_InactiveValue.sumPrefix f low 12=
      ∑ j : Fin 64,∑ s : Fin 16,
        if (FJc_SubsetModel.mask (FJc_InactiveCoefficientsModel.group j.val) &&& 2^s.val)≠0 then
          FJc_InactiveCoefficientsModel.field f j.val*FIp_ArrayValue.value low s.val else 0 := by
  rw [groups,←Fin.sum_univ_eq_sum_range]
  simp_rw [coefficients,←Fin.sum_univ_eq_sum_range]
  let group : Fin 64 → Fin 12 := fun j=>⟨FJc_InactiveCoefficientsModel.group j.val,
    FJc_GroupTable.bound j.val j.isLt⟩
  have reg := FJc_GroupAlgebra.regroup group
    (fun j : Fin 64=>FJc_InactiveCoefficientsModel.field f j.val)
    (fun g : Fin 12=>FJc_SubsetModel.sumPrefix low g.val 16)
  simp only [Fin.ext_iff,group] at reg
  rw [reg]
  apply Finset.sum_congr rfl
  intro j _
  rw [subset,←Fin.sum_univ_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  split <;> simp only [mul_zero]

#print axioms coefficients
#print axioms subset
#print axioms groups
#print axioms value
end AspisR1.FJr_InactiveRegroup
end
