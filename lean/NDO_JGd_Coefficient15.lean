import NDO_JGd_Coefficient14
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient15
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q015) 3#usize = ok t15 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨15,by omega⟩
  · change 3<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((1928970014,1690570642),(320451959,1519481212)) 3 = ((935552911,1268906353),(456913005,1928970014))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a15 15#usize (by change 15<16;omega) = a16 := by
  have hexp : core.convert.num.FromUsizeU8.from 25#u8 = 25#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (15#usize &&& 3#usize) = 3#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a15.set (core.convert.num.FromUsizeU8.from 25#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q015) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a16
  rw [hexp]
  change a15.set 25#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q015) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a16
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a15 ⟨15#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a16 ⟨16#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 15#usize 16#usize 16#usize n
    (by change 15<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 15<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient15
end
