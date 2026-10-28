import NDO_JGd_Coefficient12
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient13
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q013) 1#usize = ok t13 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨13,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((970136214,353389341),(662936248,1455264567)) 1 = ((1794094306,970136214),(692219080,662936248))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a13 13#usize (by change 13<16;omega) = a14 := by
  have hexp : core.convert.num.FromUsizeU8.from 26#u8 = 26#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (13#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a13.set (core.convert.num.FromUsizeU8.from 26#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q013) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a14
  rw [hexp]
  change a13.set 26#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q013) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a14
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a13 ⟨13#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a14 ⟨14#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 13#usize 16#usize 14#usize n
    (by change 13<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 13<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient13
end
