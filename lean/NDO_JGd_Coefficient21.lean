import NDO_JGd_Coefficient20
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient21
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q021) 1#usize = ok t21 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨5,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((2041608749,847828130),(1698118915,1691076741)) 1 = ((1299655517,2041608749),(456406906,1698118915))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a21 5#usize (by change 5<10;omega) = a22 := by
  have hexp : core.convert.num.FromUsizeU8.from 11#u8 = 11#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (5#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a21.set (core.convert.num.FromUsizeU8.from 11#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q021) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a22
  rw [hexp]
  change a21.set 11#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q021) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a22
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a21 ⟨5#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a22 ⟨6#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 5#usize 10#usize 6#usize n
    (by change 5<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 5<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient21
end
