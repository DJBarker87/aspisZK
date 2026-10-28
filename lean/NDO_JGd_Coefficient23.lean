import NDO_JGd_Coefficient22
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient23
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q023) 3#usize = ok t23 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨7,by omega⟩
  · change 3<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((576030860,1960024758),(266706019,1357022704)) 3 = ((1314215867,1323872981),(187458889,576030860))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a23 7#usize (by change 7<10;omega) = a24 := by
  have hexp : core.convert.num.FromUsizeU8.from 17#u8 = 17#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (7#usize &&& 3#usize) = 3#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a23.set (core.convert.num.FromUsizeU8.from 17#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q023) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a24
  rw [hexp]
  change a23.set 17#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q023) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a24
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a23 ⟨7#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a24 ⟨8#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 7#usize 10#usize 8#usize n
    (by change 7<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 7<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient23
end
