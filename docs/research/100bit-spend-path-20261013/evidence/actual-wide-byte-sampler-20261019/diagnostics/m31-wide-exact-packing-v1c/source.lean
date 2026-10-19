import M31EightLimbOutputLaw
import R1WideExactLimbCodec
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Rat.Cast.Defs

set_option autoImplicit false
namespace M31RetryOutputFiber

open AspisR1.WideExactLimbCodec

/-- Pair the first and second four M31 outputs in the exact retained layout. -/
def outputWideLimbs (ys : EightValues) : WideLimbs :=
  (fun i => ys (Fin.castAdd 4 i), fun i => ys (Fin.natAdd 4 i))

def outputWideExact (ys : EightValues) : AspisWideTower.WideExact :=
  pairToExact (outputWideLimbs ys)

theorem append_outputWideLimbs (ys : EightValues) :
    Fin.append (outputWideLimbs ys).1 (outputWideLimbs ys).2 = ys := by
  funext i
  fin_cases i <;> rfl

theorem outputWideExact_eq_digitsField (ys : EightValues) :
    outputWideExact ys = R0C.ModuloField.digitsField ys := by
  rw [outputWideExact, pairToExact_eq_digitsField]
  exact congrArg R0C.ModuloField.digitsField (append_outputWideLimbs ys)

/-- Exact successful word-block preimages of an actual WideExact output. -/
def wideExactOutputFiber (w : AspisWideTower.WideExact) : Prop :=
  {xs : EightRetryInputs // ∀ i : Fin 8,
    output decode31 (xs i) = some ((R0C.ModuloField.digitsField.symm w) i)}

theorem wideExactOutputFiber_card (w : AspisWideTower.WideExact) :
    Nat.card (wideExactOutputFiber w) = limbBaseCount ^ 8 := by
  exact eightOutputFiber_card_limbBase (R0C.ModuloField.digitsField.symm w)

def wideExactConditionalMass (w : AspisWideTower.WideExact) : ℚ :=
  eightConditionalMass (R0C.ModuloField.digitsField.symm w)

theorem wideExactConditionalMass_uniform (w : AspisWideTower.WideExact) :
    wideExactConditionalMass w = 1 / (P31 : ℚ) ^ 8 := by
  exact eightConditionalMass_uniform _

#print axioms outputWideExact_eq_digitsField
#print axioms wideExactOutputFiber_card
#print axioms wideExactConditionalMass_uniform

end M31RetryOutputFiber
