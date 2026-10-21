import S4LiteralCallbackValueRootV1
import AspisFormal.V6Width29CorrelatedAgreement
open AspisR1FastDotsTailFieldProductRootV1

#synth Field TowerWide
#synth Fintype (Fin 29)
example (word : Fin 29 → TowerWide) (gamma : TowerWide) :
    AspisV6Width29CorrelatedAgreement.width29Batch word gamma =
      ∑ lane : Fin 29, word lane * gamma ^ lane.val := by
  unfold AspisV6Width29CorrelatedAgreement.width29Batch
  rfl
