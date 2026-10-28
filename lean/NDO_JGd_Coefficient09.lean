import NDO_JGd_Coefficient08
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient09
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q009) 1#usize = ok t09 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨9,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1783465304,2017546462),(1885178356,269065480)) 1 = ((129937185,1783465304),(1878418167,1885178356))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a09 9#usize (by change 9<16;omega) = a10 := by
  have hexp : core.convert.num.FromUsizeU8.from 18#u8 = 18#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (9#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a09.set (core.convert.num.FromUsizeU8.from 18#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q009) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a10
  rw [hexp]
  change a09.set 18#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q009) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a10
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a09 ⟨9#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a10 ⟨10#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 9#usize 16#usize 10#usize n
    (by change 9<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 9<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient09
end
