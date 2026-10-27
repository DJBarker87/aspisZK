import FJc_InactiveValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_FiniteSums
open Aeneas Aeneas.Std
open FIo_FieldBridge (NE)
open scoped BigOperators

theorem subset (low : Array NE 16#usize) (g n : Nat) :
    FJc_SubsetModel.sumPrefix low g n=
      ∑ s∈Finset.range n, if (FJc_SubsetModel.mask g &&& 2^s)≠0 then FIp_ArrayValue.value low s else 0 := by
  induction n with
  | zero => simp only [FJc_SubsetModel.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJc_SubsetModel.sumPrefix,Finset.sum_range_succ,ih]

theorem coefficients (f : Slice U8) (g n : Nat) :
    FJc_InactiveCoefficientsModel.sumPrefix f g n=
      ∑ j∈Finset.range n, if FJc_InactiveCoefficientsModel.group j=g then FJc_InactiveCoefficientsModel.field f j else 0 := by
  induction n with
  | zero => simp only [FJc_InactiveCoefficientsModel.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJc_InactiveCoefficientsModel.sumPrefix,Finset.sum_range_succ,ih]

theorem groups (f : Slice U8) (low : Array NE 16#usize) (n : Nat) :
    FJc_InactiveValue.sumPrefix f low n=
      ∑ g∈Finset.range n,FJc_InactiveCoefficientsModel.sumPrefix f g 64*
        FJc_SubsetModel.sumPrefix low g 16 := by
  induction n with
  | zero => simp only [FJc_InactiveValue.sumPrefix,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [FJc_InactiveValue.sumPrefix,Finset.sum_range_succ,ih]
#print axioms subset
#print axioms coefficients
#print axioms groups
end AspisR1.FJc_FiniteSums
end
