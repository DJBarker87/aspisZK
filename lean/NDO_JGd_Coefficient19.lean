import NDO_JGd_Coefficient18
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient19
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q019) 3#usize = ok t19 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨3,by omega⟩
  · change 3<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((156420109,768169737),(457809055,2121990699)) 3 = ((1740660488,941111058),(1379313910,156420109))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a19 3#usize (by change 3<10;omega) = a20 := by
  have hexp : core.convert.num.FromUsizeU8.from 7#u8 = 7#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (3#usize &&& 3#usize) = 3#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a19.set (core.convert.num.FromUsizeU8.from 7#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q019) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a20
  rw [hexp]
  change a19.set 7#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q019) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a20
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a19 ⟨3#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a20 ⟨4#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 3#usize 10#usize 4#usize n
    (by change 3<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 3<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient19
end
