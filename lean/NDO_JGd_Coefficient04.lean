import NDO_JGd_Coefficient03
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient04
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q004) 0#usize = ok t04 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨4,by omega⟩
  · change 0<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((652624296,575674261),(1739907054,2128745497)) 0 = ((652624296,575674261),(1739907054,2128745497))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a04 4#usize (by change 4<16;omega) = a05 := by
  have hexp : core.convert.num.FromUsizeU8.from 8#u8 = 8#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (4#usize &&& 3#usize) = 0#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a04.set (core.convert.num.FromUsizeU8.from 8#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q004) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a05
  rw [hexp]
  change a04.set 8#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q004) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a05
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a04 ⟨4#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a05 ⟨5#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 4#usize 16#usize 5#usize n
    (by change 4<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 4<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient04
end
