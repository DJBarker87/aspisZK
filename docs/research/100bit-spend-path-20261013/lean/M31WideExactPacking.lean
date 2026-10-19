import M31EightLimbOutputLaw
import R1RetainedExactLimbCodec
import R1RetainedFieldByteCodec
import WideTower
import M31EquivUniformTransport

set_option autoImplicit false
namespace M31RetryOutputFiber

open AspisV8R15.ExactTowerBase
open AspisWideTower
open AspisR1.RetainedFieldByteCodec
open M31AcceptFiber

abbrev WideExactOutput := WideExact
abbrev OutputQM31Limbs := QM31Limbs

/-- Split the actual eight accepted M31 outputs into the two retained
four-residue QM31 coordinates. -/
def outputLimbsEquiv : EightValues ≃ OutputQM31Limbs × OutputQM31Limbs where
  toFun ys := (fun i => ys (Fin.castAdd 4 i), fun i => ys (Fin.natAdd 4 i))
  invFun limbs := Fin.append limbs.1 limbs.2
  left_inv ys := by
    funext i
    fin_cases i <;> rfl
  right_inv limbs := by
    apply Prod.ext
    · funext i
      change (Fin.append limbs.1 limbs.2) (Fin.castAdd 4 i) = limbs.1 i
      rw [Fin.append_left]
    · funext i
      change (Fin.append limbs.1 limbs.2) (Fin.natAdd 4 i) = limbs.2 i
      rw [Fin.append_right]

/-- Pack the retained pair through the existing M31-to-exact-QM31 maps
and exact quadratic-product equivalence. -/
def pairRetainedToWideExact : OutputQM31Limbs × OutputQM31Limbs ≃ WideExactOutput :=
  (Equiv.prodCongr
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv
    AspisR1.RetainedExactLimbCodec.qm31ExactLimbEquiv).trans
      (QuadraticAlgebra.equivProd wideU 0).symm

def outputToWideExact : EightValues ≃ WideExactOutput :=
  outputLimbsEquiv.trans pairRetainedToWideExact

def wideExactOutputFiber (w : WideExactOutput) :=
  eightOutputFiber (outputToWideExact.symm w)

noncomputable def wideExactConditionalMass (w : WideExactOutput) : ℚ :=
  eightConditionalMass (outputToWideExact.symm w)

theorem output_limbs_inverse (ys : EightValues) :
    outputLimbsEquiv.symm (outputLimbsEquiv ys) = ys := outputLimbsEquiv.left_inv ys

theorem outputToWideExact_apply (ys : EightValues) :
    outputToWideExact ys =
      (QuadraticAlgebra.equivProd wideU 0).symm
        (AspisR1.RetainedExactLimbCodec.limbsToQM31Exact (outputLimbsEquiv ys).1,
         AspisR1.RetainedExactLimbCodec.limbsToQM31Exact (outputLimbsEquiv ys).2) := rfl

theorem wideExactOutputFiber_card (w : WideExactOutput) :
    Nat.card (wideExactOutputFiber w) = limbBaseCount ^ 8 :=
  eightOutputFiber_card_limbBase _

theorem wideExactConditionalMass_uniform (w : WideExactOutput) :
    wideExactConditionalMass w = 1 / (P31 : ℚ) ^ 8 := by
  apply M31EquivUniformTransport.uniform_mass_equiv_symm
      outputToWideExact eightConditionalMass (1 / (P31 : ℚ) ^ 8)
  intro ys
  exact eightConditionalMass_uniform ys

#print axioms outputToWideExact
#print axioms outputToWideExact_apply
#print axioms wideExactOutputFiber_card
#print axioms wideExactConditionalMass_uniform

end M31RetryOutputFiber
