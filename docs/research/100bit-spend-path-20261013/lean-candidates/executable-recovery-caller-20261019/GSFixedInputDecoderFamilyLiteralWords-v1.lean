import GSFixedInputDecoderFamily
import GSFixedInputDecoderBankLiteralWords

set_option autoImplicit false

namespace AspisWide.GSFixedInputDecoderFamilyLiteralWords

open AspisWide.GSWideExactAgreementInputs
open AspisWide.GSFixedInputDecoderBankLiteralWords
open AspisR1.GSFixedInputDecoderFamily
open AspisR1.ConcreteProjection

abbrev WideExact := AspisWideTower.WideExact

variable [Field WideExact] [Fintype WideExact]
  [Algebra (ZMod AspisCircleGroupOrder.P) WideExact]

/-- V occupies final-bank lane 0; the four distinct second-fold channel words
occupy lanes 1 through 4 after the deployed fourfold repetition. -/
def fiveFinalWords (V : FinalWord WideExact)
    (g : Fin 4 → SmallWord WideExact) : Fin 5 → FinalWord WideExact :=
  Fin.cases V (fun s => repeatSmallWord (g s))

def fromReceivedWords (W : Fin 29 → InitialWord WideExact)
    (V : FinalWord WideExact) (g : Fin 4 → SmallWord WideExact) :
    Inputs WideExact 5 where
  initialPoints := fun i => initialLiteralPoints (W i)
  initialSize := fun i => initialLiteralPoints_size (W i)
  finalPoints := fun i => finalLiteralPoints (fiveFinalWords V g i)
  finalSize := fun i => finalLiteralPoints_size (fiveFinalWords V g i)

theorem initialPoints_eq (W : Fin 29 → InitialWord WideExact)
    (V : FinalWord WideExact) (g : Fin 4 → SmallWord WideExact) (i : Fin 29) :
    (fromReceivedWords W V g).initialPoints i = initialLiteralPoints (W i) := rfl

theorem finalPoints_eq (W : Fin 29 → InitialWord WideExact)
    (V : FinalWord WideExact) (g : Fin 4 → SmallWord WideExact) (i : Fin 5) :
    (fromReceivedWords W V g).finalPoints i =
      finalLiteralPoints (fiveFinalWords V g i) := rfl

theorem finalSize_eq (W : Fin 29 → InitialWord WideExact)
    (V : FinalWord WideExact) (g : Fin 4 → SmallWord WideExact) (i : Fin 5) :
    (fromReceivedWords W V g).finalSize i = 262144 :=
  finalLiteralPoints_size (fiveFinalWords V g i)

#print axioms fiveFinalWords
#print axioms fromReceivedWords
#print axioms finalPoints_eq

end AspisWide.GSFixedInputDecoderFamilyLiteralWords
