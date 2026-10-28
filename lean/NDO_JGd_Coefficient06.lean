import NDO_JGd_Coefficient05
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient06
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q006) 2#usize = ok t06 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨6,by omega⟩
  · change 2<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1519785285,417843121),(1706245526,1595448726)) 2 = ((1817042326,602175684),(1519785285,417843121))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a06 6#usize (by change 6<16;omega) = a07 := by
  have hexp : core.convert.num.FromUsizeU8.from 12#u8 = 12#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (6#usize &&& 3#usize) = 2#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a06.set (core.convert.num.FromUsizeU8.from 12#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q006) 2#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a07
  rw [hexp]
  change a06.set 12#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q006) 2#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a07
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a06 ⟨6#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a07 ⟨7#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 6#usize 16#usize 7#usize n
    (by change 6<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 6<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient06
end
