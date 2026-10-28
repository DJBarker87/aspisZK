import NDO_JGd_Coefficient21
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient22
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q022) 2#usize = ok t22 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨6,by omega⟩
  · change 2<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1819985108,1775297862),(1866648082,1549667231)) 2 = ((36145286,671015250),(1819985108,1775297862))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a22 6#usize (by change 6<10;omega) = a23 := by
  have hexp : core.convert.num.FromUsizeU8.from 15#u8 = 15#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (6#usize &&& 3#usize) = 2#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a22.set (core.convert.num.FromUsizeU8.from 15#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q022) 2#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a23
  rw [hexp]
  change a22.set 15#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q022) 2#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a23
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a22 ⟨6#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a23 ⟨7#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 6#usize 10#usize 7#usize n
    (by change 6<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 6<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient22
end
