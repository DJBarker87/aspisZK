import GSFixedInputDecoderBank
import WideExactGRSInstantiationV5
import SecondFoldMatched
import AspisFormal.V7ExactOneFoldDomains

set_option autoImplicit false

namespace AspisWide.GSFixedInputDecoderBankLiteralWords

open AspisCircleGroupOrder
open AspisV7ExactOneFoldDomains
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.GSWideExactAgreementInputs
open AspisWide.WideExactGRSInstantiation
open AspisR1.SecondFoldMatched
open AspisR1.ConcreteProjection

abbrev K := AspisWideTower.WideExact

variable [Field K] [Fintype K] [Algebra (ZMod P) K]

/-- Literal deployed log-20 point and normalization. This runtime definition
uses the stored circle domain and field operations directly; it does not
evaluate the polynomial-bearing GRS conversion record. -/
def initialLiteralPair (received : InitialWord K) (i : Fin 1048576) : K × K :=
  let point := storedInitialCirclePoint20 i
  let parameter := algebraMap (ZMod P) K (point.1.2 / (1 + X point))
  (parameter, (1 + parameter ^ 2) ^ 512 * received i)

/-- Array form of the literal log-20 point sequence. -/
def initialLiteralPoints (received : InitialWord K) : Array (K × K) :=
  Array.ofFn (initialLiteralPair received)

/-- Literal deployed log-18 points have multiplier one. -/
def finalLiteralPair (received : FinalWord K) (i : Fin 262144) : K × K :=
  (algebraMap (ZMod P) K (storedFirstLineX18 i), received i)

def finalLiteralPoints (received : FinalWord K) : Array (K × K) :=
  Array.ofFn (finalLiteralPair received)

def repeatSmallWord (received : SmallWord K) : FinalWord K :=
  fun i => received (AspisR1.parentIndex i)

theorem initialLiteralPoints_size (received : InitialWord K) :
    (initialLiteralPoints received).size = 1048576 := by
  simp [initialLiteralPoints]

theorem finalLiteralPoints_size (received : FinalWord K) :
    (finalLiteralPoints received).size = 262144 := by
  simp [finalLiteralPoints]

/-- The literal log-20 point is the already-established conversion point. -/
theorem initialLiteralPoint_eq_conversion (received : InitialWord K)
    (i : Fin 1048576) :
    (initialLiteralPair received i).1 = initialConversion.points i := by
  change algebraMap (ZMod P) K
      ((storedInitialCirclePoint20 i).1.2 /
        (1 + X (storedInitialCirclePoint20 i))) = initialConversion.points i
  rw [initialConversion, AspisWide.GRSConversion.exactInitialGRSConversion,
    AspisWide.GRSConversion.exactCircleGRSPoint_eq_stored]

/-- The literal log-20 normalized value is the conversion's multiplier inverse
times the received symbol. -/
theorem initialLiteralValue_eq_conversion (received : InitialWord K)
    (i : Fin 1048576) :
    (initialLiteralPair received i).2 =
      (initialConversion.multipliers i)⁻¹ * received i := by
  change (1 + (algebraMap (ZMod P) K
      ((storedInitialCirclePoint20 i).1.2 /
        (1 + X (storedInitialCirclePoint20 i)))) ^ 2) ^ 512 * received i = _
  rw [initialConversion, AspisWide.GRSConversion.exactInitialGRSConversion,
    AspisWide.GRSConversion.exactCircleGRSPoint_eq_stored,
    AspisWide.GRSConversion.exactCircleGRSMultiplier]
  simp only [inv_inv]

theorem initialLiteralPoints_eq_normalized (received : InitialWord K) :
    initialLiteralPoints received = initialNormalizedPoints received := by
  apply Array.ext
  · simp [initialLiteralPoints, initialNormalizedPoints]
  · intro i hi₁ hi₂
    apply Prod.ext
    · exact initialLiteralPoint_eq_conversion received i
    · exact initialLiteralValue_eq_conversion received i

theorem finalLiteralPoint_eq_conversion (received : FinalWord K)
    (i : Fin 262144) :
    (finalLiteralPair received i).1 = finalConversion.points i := by
  rfl

theorem finalLiteralValue_eq_conversion (received : FinalWord K)
    (i : Fin 262144) :
    (finalLiteralPair received i).2 =
      (finalConversion.multipliers i)⁻¹ * received i := by
  simp [finalConversion, AspisWide.GRSConversion.exactFinalGRSConversion]

theorem finalLiteralPoints_eq_normalized (received : FinalWord K) :
    finalLiteralPoints received = finalNormalizedPoints received := by
  apply Array.ext
  · simp [finalLiteralPoints, finalNormalizedPoints]
  · intro i hi₁ hi₂
    apply Prod.ext
    · exact finalLiteralPoint_eq_conversion received i
    · exact finalLiteralValue_eq_conversion received i

/-- Fixed-input bank values are now assembled from direct runtime functions.
The conversion-record equalities are proof bridges above only. -/
def fromReceivedWords
    (W : Fin 29 → InitialWord K)
    (V : FinalWord K)
    (U : SmallWord K) : AspisR1.GSFixedInputDecoderBank.Inputs K where
  initialPoints := fun i => initialLiteralPoints (W i)
  initialSize := fun i => initialLiteralPoints_size (W i)
  finalPoints := fun i =>
    Fin.cases (finalLiteralPoints V)
      (fun _ => finalLiteralPoints (repeatSmallWord U)) i
  finalSize := by
    intro i
    fin_cases i <;> simp [finalLiteralPoints_size]

theorem initialPoints_eq (W : Fin 29 → InitialWord K)
    (V : FinalWord K) (U : SmallWord K) (i : Fin 29) :
    (fromReceivedWords W V U).initialPoints i = initialLiteralPoints (W i) := rfl

theorem finalPoints_zero_eq (W : Fin 29 → InitialWord K)
    (V : FinalWord K) (U : SmallWord K) :
    (fromReceivedWords W V U).finalPoints 0 = finalLiteralPoints V := rfl

theorem finalPoints_one_eq (W : Fin 29 → InitialWord K)
    (V : FinalWord K) (U : SmallWord K) :
    (fromReceivedWords W V U).finalPoints 1 = finalLiteralPoints (repeatSmallWord U) := rfl

#print axioms initialLiteralPair
#print axioms finalLiteralPair
#print axioms initialLiteralPoints_eq_normalized
#print axioms finalLiteralPoints_eq_normalized
#print axioms fromReceivedWords

end AspisWide.GSFixedInputDecoderBankLiteralWords
