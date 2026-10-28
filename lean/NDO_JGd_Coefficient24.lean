import NDO_JGd_Coefficient23
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGd_Coefficient24
open JGd_ExactWords
attribute [local irreducible] HPow.hPow HMul.hMul HAdd.hAdd
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open JGd_CoefficientData
theorem basis : state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q024) 0#usize = ok t24 := by
  apply JGd_CoefficientStep.basis
  · exact JFu_MaskInputs.maskOnly_canonical ⟨8,by omega⟩
  · change 0<4;omega
  · change ExtractedMaskTowerBasis.basisWords ((40105540,1572894176),(1128859828,1452095554)) 0 = ((40105540,1572894176),(1128859828,1452095554))
    norm_num [ExtractedMaskTowerBasis.basisWords, ExtractedMaskTowerBasis.iWords, ExtractedMaskQM31Mul.rWords, ExtractedMaskTowerBasis.P, ExtractedMaskTowerAdd.P, ExtractedMaskQM31Mul.P]
#print axioms basis
theorem write : ExtractedMaskCoefficientLoop1.writeAt1
    (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly) a24 8#usize (by change 8<10;omega) = a25 := by
  have hexp : core.convert.num.FromUsizeU8.from 19#u8 = 19#usize := by
    apply UScalar.eq_of_val_eq
    rw [core.convert.num.FromUsizeU8.from_val_eq]
    rfl
  have hbit : (8#usize &&& 3#usize) = 0#usize := by decide
  unfold ExtractedMaskCoefficientLoop1.writeAt1 state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS
  dsimp only
  rw [hbit]
  change a24.set (core.convert.num.FromUsizeU8.from 19#u8) (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q024) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a25
  rw [hexp]
  change a24.set 19#usize (match state_only_hiding.mul_tower_basis (FIp_SemanticArithmetic.toProbe JFu_ClaimsData.q024) 0#usize with | .ok z => z | .fail _ => field.QM31.ZERO | .div => field.QM31.ZERO) = a25
  rw [basis]
  rfl
#print axioms write
theorem advance (n : Nat) :
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a24 ⟨8#usize,10#usize⟩ (n+1) =
    ExtractedMaskCoefficientLoop1.writeModel1 (FIp_SemanticArithmetic.mapArray JFu_MaskInputs.maskOnly)
      a25 ⟨9#usize,10#usize⟩ n := by
  rw [JGd_CoefficientStep.step1 _ _ 8#usize 10#usize 9#usize n
    (by change 8<10;omega) (JGd_CoefficientStep.next _ _ _ (by change 8<10;omega) (by rfl)),write]
#print axioms advance
end AspisR1.JGd_Coefficient24
end
