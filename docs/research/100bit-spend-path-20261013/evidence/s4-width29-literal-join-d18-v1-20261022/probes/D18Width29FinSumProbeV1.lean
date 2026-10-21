import S4LiteralCallbackValueRootV1
import AspisFormal.V6Width29CorrelatedAgreement
open AspisR1FastDotsTailFieldProductRootV1

example (f : Fin 29 → TowerWide) :
    (∑ i : Fin 29, f i) =
      (∑ i : Fin 26, f (Fin.castAdd 3 i)) +
        ∑ i : Fin 3, f (Fin.natAdd 26 i) := by
  simpa using (Fin.sum_univ_add (a := 26) (b := 3) f)
