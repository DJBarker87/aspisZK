import R0.RoundCore
import AspisV8R19.R370KernelEvaluation

/-! Exact correspondence to the original natural-basis kernel. The shared
RoundCore constants also occur in the Wide-side F5 theorem. -/
set_option autoImplicit false
namespace AspisR0.KernelCorrespondence
open AspisR0.RoundCore AspisR19.R370KernelEvaluation
open AspisR19.BetaUniformCorrection AspisR19.FullCoefficientBoundary
open Polynomial
open scoped BigOperators
noncomputable section
variable {K : Type*} [Field K]

theorem firstFold_eq (alpha : K) (q : Fin 1024 → K) :
    firstFold 256 alpha (unflatten q) = RoundCore.fold alpha q := rfl

theorem dualFold_eq (alpha : K) (w : Fin 1024 → K) :
    AspisR19.R370KernelEvaluation.dualFold 256 alpha (unflatten w) =
      RoundCore.dualFold alpha w := rfl

theorem coefficient_eq (q w : Fin 1024 → K) (k : Nat) :
    (RoundCore.polynomial q w).coeff k =
      coefficient (sourceKernel 256 k RoundCore.quarter) (unflatten q) (unflatten w) := by
  simp only [RoundCore.polynomial, Polynomial.finsetSum_coeff, coefficient_blocks,
    coeff_monomial, unflatten, ite_mul, zero_mul]

theorem kernelEval_eq (alpha : K) (q w : Fin 1024 → K) :
    kernelEval 256 RoundCore.quarter alpha (unflatten q) (unflatten w) =
      (RoundCore.polynomial q w).eval alpha := by
  rw [kernel_eval_pairing, firstFold_eq, dualFold_eq, RoundCore.eval_polynomial]

theorem correspondence (alpha : K) (q w : Fin 1024 → K) :
    firstFold 256 alpha (unflatten q) = RoundCore.fold alpha q ∧
    AspisR19.R370KernelEvaluation.dualFold 256 alpha (unflatten w) =
      RoundCore.dualFold alpha w ∧
    kernelEval 256 RoundCore.quarter alpha (unflatten q) (unflatten w) =
      (RoundCore.polynomial q w).eval alpha ∧
    ∀ k, (RoundCore.polynomial q w).coeff k =
      coefficient (sourceKernel 256 k RoundCore.quarter) (unflatten q) (unflatten w) :=
  ⟨firstFold_eq alpha q, dualFold_eq alpha w, kernelEval_eq alpha q w, coefficient_eq q w⟩

#print axioms correspondence
end
end AspisR0.KernelCorrespondence
