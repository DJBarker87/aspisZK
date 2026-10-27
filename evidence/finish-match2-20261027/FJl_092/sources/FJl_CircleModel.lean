import FJl_SlotLiteral
import FoldRuntimeAlgebra
import R1FirstFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_CircleModel
open AspisWide.InitialEncoder AspisWide.FinalEncoder
abbrev E := AspisWideTower.WideExact
/-- The symbolic native circle expression is the original model first fold
on precisely the SAME four fibre coordinates. -/
theorem value (alpha : E) (f : AspisPool.AlgorithmicCircleDecoderV7.InitialWord E)
    (i : Fin 262144) :
    FoldRuntimeAlgebra.circle alpha (exactCircleX i) (exactCircleY i) (FirstFold.fibre f i)=
      FirstFold.foldWord alpha f i := by
  have nz := FirstFold.fibre_coordinates_nonzero (K := E) i
  rw [FoldRuntimeAlgebra.circle_eq_model alpha _ _ _ two_ne_zero nz.1 nz.2]
  rfl
#print axioms value
end AspisR1.FJl_CircleModel
end
