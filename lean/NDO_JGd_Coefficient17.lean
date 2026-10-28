import NDO_JGd_Coefficient16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient17
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q017) 1#usize = ok t17 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨1,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1156423977,1883598252),(1752370157,2077925937)) 1 = ((263885395,1156423977),(69557710,1752370157))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a17 1#usize (by change 1<10;omega) = a18 := by
  have hexp : core.convert.num.FromUsizeU8.from 3#u8 = 3#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (1#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a17.set (core.convert.num.FromUsizeU8.from 3#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q017) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a18
  rw [hexp]
  change a17.set 3#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q017) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a18
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a17 ⟨1#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a18 ⟨2#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 1#usize 10#usize 2#usize n
    (by change 1<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 1<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient17
end
