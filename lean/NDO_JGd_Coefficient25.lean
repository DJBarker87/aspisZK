import NDO_JGd_Coefficient24
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient25
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q025) 1#usize = ok t25 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨9,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((31707117,1141605523),(1555692882,675499391)) 1 = ((1005878124,31707117),(1471984256,1555692882))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a25 9#usize (by change 9<10;omega) = a26 := by
  have hexp : core.convert.num.FromUsizeU8.from 21#u8 = 21#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (9#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a25.set (core.convert.num.FromUsizeU8.from 21#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q025) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a26
  rw [hexp]
  change a25.set 21#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q025) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a26
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a25 ⟨9#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a26 ⟨10#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 9#usize 10#usize 10#usize n
    (by change 9<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 9<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient25
end
