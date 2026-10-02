import AspisV8R19.R370KernelEvaluation
import AspisV8R19.SourceCircleBoundary

/-! The existing source-shaped quotient columns automatically satisfy the
cross-polynomial evaluation constraint. No Rust execution or complete legal
mask coverage is asserted. -/
set_option autoImplicit false
namespace AspisR19.R372SourceColumnCompatibility
open R370KernelEvaluation SourceCircleBoundary
open scoped BigOperators
variable {F : Type*} [Field F] [NeZero (2 : F)]

theorem column_first_fold (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha : F) (j : Fin 13) (d : Fin 256) :
    firstFold 256 alpha (column t alpha j) d=0 := by
  simpa only [firstFold,mul_comm] using coefficient_fold_zero t ht alpha j d

theorem column_cross_compatibility (t : Fin 22 → F) (ht : Function.Injective t)
    (alpha quarter : F) (j : Fin 13) (w : Fin 256 × Fin 4 → F) :
    kernelEval 256 quarter alpha (column t alpha j) w=0 := by
  exact kernel_eval_zero_of_first_fold 256 quarter alpha _ w
    (column_first_fold t ht alpha j)

theorem linear_combination_cross_compatibility (t : Fin 22 → F)
    (ht : Function.Injective t) (alpha quarter : F) (c : Fin 13 → F)
    (w : Fin 256 × Fin 4 → F) :
    kernelEval 256 quarter alpha (fun i => ∑ j : Fin 13, c j*column t alpha j i) w=0 := by
  apply kernel_eval_zero_of_first_fold
  intro d
  simp only [firstFold,Finset.sum_mul]
  rw [Finset.sum_comm]
  have hz : ∀ j : Fin 13, (∑ s : Fin 4, c j*column t alpha j (d,s)*alpha^s.val)=0 := by
    intro j
    calc
      _ = c j * firstFold 256 alpha (column t alpha j) d := by
        simp only [firstFold,Finset.mul_sum,mul_assoc]
      _ = 0 := by rw [column_first_fold t ht alpha j d,mul_zero]
  simp only [hz,Finset.sum_const_zero]

#print axioms column_first_fold
#print axioms column_cross_compatibility
#print axioms linear_combination_cross_compatibility
end AspisR19.R372SourceColumnCompatibility
