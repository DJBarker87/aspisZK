import AspisR1.CopyEvaluateRowExact

/-! Symbolic retained evaluator identity; the full link registry stays opaque. -/
set_option autoImplicit false
namespace AspisR1.CopyEvaluatorModel
noncomputable section
open AspisR1.CopyEvaluateRowExact (ExactQM retainedRow)
attribute [local irreducible] R0P.copyLinks

theorem retained_evaluator_eq (openings : Fin 16 → ExactQM) (helper : ExactQM)
    (selectors : R0P.CopySelectors ExactQM) (lambda chi : ExactQM)
    (index : Nat) (variant : R0P.Variant) :
    R0P.copyEvaluateWithSelectors openings helper selectors lambda chi index variant =
      (R0P.copyActiveLiteral selectors *
        R0P.copyResidual (retainedRow openings selectors lambda index variant) helper chi,
       R0P.copyActiveLiteral selectors) := by
  simp only [R0P.copyEvaluateWithSelectors,retainedRow,AspisR1.CopyLinkStepExact.modelStep]

#print axioms retained_evaluator_eq
end
end AspisR1.CopyEvaluatorModel
