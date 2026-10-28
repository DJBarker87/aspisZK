import NDO_JGd_Coefficient04
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient05
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q005) 1#usize = ok t05 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨5,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((261001302,1433811342),(2093232551,1795606717)) 1 = ((713672305,261001302),(351876930,2093232551))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a05 5#usize (by change 5<16;omega) = a06 := by
  have hexp : core.convert.num.FromUsizeU8.from 10#u8 = 10#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (5#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a05.set (core.convert.num.FromUsizeU8.from 10#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q005) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a06
  rw [hexp]
  change a05.set 10#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q005) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a06
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a05 ⟨5#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a06 ⟨6#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 5#usize 16#usize 6#usize n
    (by change 5<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 5<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient05
end
