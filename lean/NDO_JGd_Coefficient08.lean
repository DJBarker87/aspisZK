import NDO_JGd_Coefficient07
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient08
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q008) 0#usize = ok t08 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨8,by omega⟩
  · change 0<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1758460621,1711624258),(1933517417,1591239394)) 0 = ((1758460621,1711624258),(1933517417,1591239394))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a08 8#usize (by change 8<16;omega) = a09 := by
  have hexp : core.convert.num.FromUsizeU8.from 16#u8 = 16#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (8#usize &&& 3#usize) = 0#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a08.set (core.convert.num.FromUsizeU8.from 16#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q008) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a09
  rw [hexp]
  change a08.set 16#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q008) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a09
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a08 ⟨8#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a09 ⟨9#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 8#usize 16#usize 9#usize n
    (by change 8<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 8<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient08
end
