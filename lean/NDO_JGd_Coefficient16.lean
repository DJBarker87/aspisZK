import NDO_JGd_Coefficient15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient16
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q016) 0#usize = ok t16 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨0,by omega⟩
  · change 0<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((479557376,317941656),(305958949,1440737655)) 0 = ((479557376,317941656),(305958949,1440737655))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a16 0#usize (by change 0<10;omega) = a17 := by
  have hexp : core.convert.num.FromUsizeU8.from 1#u8 = 1#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (0#usize &&& 3#usize) = 0#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a16.set (core.convert.num.FromUsizeU8.from 1#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q016) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a17
  rw [hexp]
  change a16.set 1#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q016) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a17
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a16 ⟨0#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a17 ⟨1#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 0#usize 10#usize 1#usize n
    (by change 0<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 0<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient16
end
