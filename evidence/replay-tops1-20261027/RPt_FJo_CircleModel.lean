import RPt_FJo_CircleGeneric
import RPt_FJl_SlotLiteral
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_CircleModel
open AspisWide.InitialEncoder AspisWide.FinalEncoder
open AspisV5ComponentCConcreteFoldLinearity AspisV5FriConcreteEncoderCommutation
attribute [local irreducible] exactCircleX exactCircleY
abbrev E := AspisWideTower.WideExact
/-- Stored geometry instantiation of the generic field identity. -/
theorem value (alpha : E) (f : AspisPool.AlgorithmicCircleDecoderV7.InitialWord E)
    (i : Fin 262144) :
    FoldRuntimeAlgebra.circle alpha (exactCircleX i) (exactCircleY i) (FirstFold.fibre f i)=
      FirstFold.foldWord alpha f i := by
  exact FJo_CircleGeneric.value alpha f i
#print axioms value
end AspisR1.FJo_CircleModel
end
