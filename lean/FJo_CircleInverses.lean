import FJo_CircleModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_CircleInverses
open AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
/-- Exact inverse-coordinate form consumed by the native circle port. -/
theorem value (alpha : E) (f : AspisPool.AlgorithmicCircleDecoderV7.InitialWord E) (i : Fin 262144) :
    FoldRuntimeAlgebra.circleWithInverses alpha (exactCircleX i)⁻¹ (exactCircleY i)⁻¹
      (FirstFold.fibre f i)=FirstFold.foldWord alpha f i := by
  rw [FoldRuntimeAlgebra.circle_with_inverses_eq,FJo_CircleModel.value]
#print axioms value
end AspisR1.FJo_CircleInverses
end
