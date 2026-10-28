import NDO_JGd_Coefficients
import NDO_JGd_Power1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_HornerData
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std
def coeff := ExtractedMaskHornerCaller.coefficientValue (ExtractedMaskCallerModel.populatedCoefficients (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly))
def r26 : W := ((1794094306,970136214),(692219080,662936248))
def run (n : Nat) (v : Q) : Q := ExtractedMaskHornerPolynomial.hornerLoopModel coeff (value JGd_Linear00.sum0) n v
theorem seed : coeff 26 = value r26 := JGd_Coefficients.value ⟨26,by omega⟩
#print axioms seed
end AspisR1.JGd_HornerData
end
