import NDO_JGd_Coefficient00
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient01
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q001) 1#usize = ok t01 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨1,by omega⟩
  · change 1<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((122159246,1529111516),(1799434707,1890743665)) 1 = ((618372131,122159246),(256739982,1799434707))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a01 1#usize (by change 1<16;omega) = a02 := by
  have hexp : core.convert.num.FromUsizeU8.from 2#u8 = 2#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (1#usize &&& 3#usize) = 1#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a01.set (core.convert.num.FromUsizeU8.from 2#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q001) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a02
  rw [hexp]
  change a01.set 2#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q001) 1#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a02
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a01 ⟨1#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a02 ⟨2#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 1#usize 16#usize 2#usize n
    (by change 1<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 1<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient01
end
