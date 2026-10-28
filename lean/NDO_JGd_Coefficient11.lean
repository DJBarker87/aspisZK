import NDO_JGd_Coefficient10
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient11
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q011) 3#usize = ok t11 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.c1_canonical ⟨11,by omega⟩
  · change 3<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((111471460,2019486034),(196044068,454889585)) 3 = ((1041660409,2084682198),(127997613,111471460))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop0.writeAt0
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1) a11 11#usize (by change 11<16;omega) = a12 := by
  have hexp : core.convert.num.FromUsizeU8.from 22#u8 = 22#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (11#usize &&& 3#usize) = 3#usize := by decide
  unfold ExtractedMaskCoefficientLoop0.writeAt0 state_only_hiding.FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a11.set (core.convert.num.FromUsizeU8.from 22#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q011) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a12
  rw [hexp]
  change a11.set 22#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q011) 3#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a12
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a11 ⟨11#usize,16#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop0.writeModel0 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.c1)
      a12 ⟨12#usize,16#usize⟩ n := by
  rw [JGd_CoefficientStep.step0 _ _ 11#usize 16#usize 12#usize n
    (by change 11<16;omega) (JGd_CoefficientStep.next _ _ _ (by change 11<16;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient11
end
