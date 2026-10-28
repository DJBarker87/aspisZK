import NDO_JGd_Coefficient06
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient07
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q007) 3#usize = ok t07 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨7,by omega⟩
  · change 3<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((844088711,1816701484),(1695483190,593217799)) 3 = ((1413048506,650264934),(330782163,844088711))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a07 7#usize (by change 7<16;omega) = a08 := by
  have hexp : core.convert.num.FromUsizeU8.from 14#u8 = 14#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (7#usize &&& 3#usize) = 3#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a07.set (core.convert.num.FromUsizeU8.from 14#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q007) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a08
  rw [hexp]
  change a07.set 14#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q007) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a08
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a07 ⟨7#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a08 ⟨8#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 7#usize 16#usize 8#usize n
    (by change 7<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 7<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient07
end
