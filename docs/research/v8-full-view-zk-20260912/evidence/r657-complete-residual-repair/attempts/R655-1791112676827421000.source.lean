import AspisV8R19.R652ResidualCoefficientCompletion
import AspisV8R19.R653SourceCoefficientBoundary
import AspisV8R19.R654ResidualAlphaNonzero
set_option autoImplicit false
namespace AspisV8R19.R655SourceResidualCompletion
open AspisR19 AspisV8R17 HighRepairInvariant BetaUniformCorrection
open R652ResidualCoefficientCompletion R653SourceCoefficientBoundary
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

/-- A first-fold-zero source quotient has zero evaluation of either complete
seven-coefficient relation. This retains the exact source weight restriction. -/
theorem source_relation_eval_zero (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (structured : Bool)
    (q : Index 32 → F)
    (hf : ∀ d, R370KernelEvaluation.firstFold 32 alpha q d = 0) :
    evalSeven (fun k : Fin 7 => TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous structured q k.val) alpha = 0 := by
  unfold evalSeven
  simp only [TwoSwapResidualSource.relation_eq]
  exact R370KernelEvaluation.kernel_eval_zero_of_first_fold 32 quarter alpha q
    (TwoSwapResidualModel.weight half a b c kappa z structured) hf

/-- The first six ordinary source coefficients determine the omitted seventh
when the first fold vanishes and alpha is nonzero. -/
theorem ordinary_source_completion (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (q : Index 32 → F)
    (ha : alpha ≠ 0) (hf : ∀ d, R370KernelEvaluation.firstFold 32 alpha q d = 0)
    (hs : ∀ k : Fin 7, k ≠ 6 → TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous false q k.val = 0) :
    ∀ k : Fin 7, TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous false q k.val = 0 := by
  exact ordinary_completion _ alpha ha
    (source_relation_eval_zero half quarter a b c kappa tau alpha z previous false q hf) hs

/-- The five selected structured coefficients and the retained low-block
moment determine both omitted coefficients. The moment is explicit here;
this theorem does not assert it for every legal witness difference. -/
theorem structured_source_completion (half quarter a b c kappa tau alpha : F)
    (z : Fin 10 → F) (previous : Fin 271 → F) (q : Index 32 → F)
    (ha : alpha ≠ 0) (hf : ∀ d, R370KernelEvaluation.firstFold 32 alpha q d = 0)
    (hm : (∑ d : Fin 32, ∑ s : Fin 4,
      q (d,s) * TwoSwapResidualModel.weight half a b c kappa z true (d,s)) = 0)
    (hs : ∀ k : Fin 7, k ≠ 4 → k ≠ 6 → TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous true q k.val = 0) :
    ∀ k : Fin 7, TwoSwapResidualSource.relation
      half quarter a b c kappa tau z previous true q k.val = 0 := by
  apply structured_completion _ alpha ha
    (source_relation_eval_zero half quarter a b c kappa tau alpha z previous true q hf) ?_ hs
  simp only [TwoSwapResidualSource.relation_eq]
  rw [coefficient_boundary, hm, mul_zero]

#print axioms source_relation_eval_zero
#print axioms ordinary_source_completion
#print axioms structured_source_completion
end
end AspisV8R19.R655SourceResidualCompletion
