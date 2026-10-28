import NDO_JGd_Coefficient02
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient03
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q003) 3#usize = ok t03 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨3,by omega⟩
  · change 3<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1592384557,1945247415),(1778484467,540792410)) 3 = ((1434898007,868692877),(202236232,1592384557))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a03 3#usize (by change 3<16;omega) = a04 := by
  have hexp : core.convert.num.FromUsizeU8.from 6#u8 = 6#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (3#usize &&& 3#usize) = 3#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a03.set (core.convert.num.FromUsizeU8.from 6#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q003) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a04
  rw [hexp]
  change a03.set 6#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q003) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a04
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a03 ⟨3#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a04 ⟨4#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 3#usize 16#usize 4#usize n
    (by change 3<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 3<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient03
end
