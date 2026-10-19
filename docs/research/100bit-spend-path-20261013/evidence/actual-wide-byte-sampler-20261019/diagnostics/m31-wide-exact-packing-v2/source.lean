import M31EightLimbOutputLaw
import R1RetainedExactLimbCodec
import Mathlib.Data.Rat.Cast.Defs

set_option autoImplicit false
namespace M31RetryOutputFiber

open AspisV8R15.ExactTowerBase

abbrev WideExactOutput := AspisWideTower.WideExact
abbrev OutputQM31Limbs := AspisR1.RetainedExactLimbCodec.QM31Limbs

/-- Split the actual eight accepted M31 outputs into the two retained
four-residue QM31 coordinates. -/
def outputLimbsEquiv : EightValues ≃ OutputQM31Limbs × OutputQM31Limbs where
  toFun ys := (fun i => ys (Fin.castAdd 4 i), fun i => ys (Fin.natAdd 4 i))
  invFun limbs := Fin.append limbs.1 limbs.2
  left_inv ys := by
    funext i
    fin_cases i <;> rfl
  right_inv limbs := by
    apply Prod.ext <;> funext i <;> rfl

/-- Pack the retained pair through the already-proved M31-to-exact-QM31 maps
and the existing exact quadratic-product equivalence. -/
def pairRetainedToWideExact : OutputQM31Limbs × OutputQM31Limbs ≃ WideExactOutput :=
  (Equiv.prodCongr
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv).trans
      (QuadraticAlgebra.equivProd wideU 0).symm

def outputToWideExact : EightValues ≃ WideExactOutput :=
  outputLimbsEquiv.trans pairRetainedToWideExact

noncomputable def wideExactConditionalMass (w : WideExactOutput) : ℚ :=
  eightConditionalMass (outputToWideExact.symm w)

theorem wideExactOutputFiber_card (w : WideExactOutput) :
    Nat.card (eightOutputFiber (outputToWideExact.symm w)) = limbBaseCount ^ 8 :=
  eightOutputFiber_card_limbBase _

theorem wideExactConditionalMass_uniform (w : WideExactOutput) :
    wideExactConditionalMass w = 1 / (P31 : ℚ) ^ 8 :=
  eightConditionalMass_uniform _

theorem outputToWideExact_apply (ys : EightValues) :
    outputToWideExact ys =
      (QuadraticAlgebra.equivProd wideU 0).symm
        (AspisR1.RetainedExactLimbCodec.limbsToQM31Exact (outputLimbsEquiv ys).1,
         AspisR1.RetainedExactLimbCodec.limbsToQM31Exact (outputLimbsEquiv ys).2) := rfl

#print axioms outputLimbsEquiv
#print axioms wideExactOutputFiber_card
#print axioms wideExactConditionalMass_uniform
#print axioms outputToWideExact_apply

end M31RetryOutputFiber
