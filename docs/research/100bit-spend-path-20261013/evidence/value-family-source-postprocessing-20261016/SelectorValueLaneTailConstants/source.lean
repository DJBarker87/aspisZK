import Aeneas.Std
import ExtractedMaskScalarExact

/-! Exact values returned by the two checked U32 shifts in the candidate
reconstruction tail, and their embeddings into the retained exact field. -/
set_option autoImplicit false
namespace AspisR1.SelectorValueLaneTailConstants

open Aeneas Aeneas.Std WP

abbrev ExactQM := AspisR1.ExtractedMaskScalarExact.QM31Exact
abbrev M31 := AspisR1.ExtractedMaskScalarExact.M31

def scale10 : M31 := 1024#u32
def scale20 : M31 := 1048576#u32

theorem shift10_success : (1#u32 <<< 10#i32 : Result U32) = .ok scale10 := by
  have htoNat : (10#i32).toNat = 10 := by rfl
  have hspec := UScalar.ShiftLeft_IScalar_spec (1#u32) (10#i32)
    (UScalar.size UScalarTy.U32) (by scalar_tac) (by scalar_tac) rfl
  obtain ⟨out, hrun, hvalue⟩ := WP.spec_imp_exists hspec
  have hout : out.val = 1024 := by
    rw [hvalue.1]
    rw [htoNat]
    rw [Nat.shiftLeft_eq]
    norm_num [UScalar.val, IScalar.toNat, U32.size, U32.numBits,
      UScalarTy.U32_numBits_eq]
  have heq : out = scale10 := UScalar.eq_of_val_eq hout
  rw [hrun, heq]

theorem shift20_success : (1#u32 <<< 20#i32 : Result U32) = .ok scale20 := by
  have htoNat : (20#i32).toNat = 20 := by rfl
  have hspec := UScalar.ShiftLeft_IScalar_spec (1#u32) (20#i32)
    (UScalar.size UScalarTy.U32) (by scalar_tac) (by scalar_tac) rfl
  obtain ⟨out, hrun, hvalue⟩ := WP.spec_imp_exists hspec
  have hout : out.val = 1048576 := by
    rw [hvalue.1]
    rw [htoNat]
    rw [Nat.shiftLeft_eq]
    norm_num [UScalar.val, IScalar.toNat, U32.size, U32.numBits,
      UScalarTy.U32_numBits_eq]
  have heq : out = scale20 := UScalar.eq_of_val_eq hout
  rw [hrun, heq]

theorem source_shift_embeddings :
    AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale10 = (1024 : ExactQM) ∧
    AspisR1.ExtractedMaskScalarExact.scalarEmbedding scale20 = (1048576 : ExactQM) := by
  constructor
  · ext <;> norm_num [scale10, AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
      AspisV8R15.ExactTowerBase.QM31Exact,
      AspisV8R15.ExactTowerBase.CM31Exact,
      AspisV8R15.ExactTowerBase.M31Exact,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
  · ext <;> norm_num [scale20, AspisR1.ExtractedMaskScalarExact.scalarEmbedding,
      AspisV8R15.ExactTowerBase.QM31Exact,
      AspisV8R15.ExactTowerBase.CM31Exact,
      AspisV8R15.ExactTowerBase.M31Exact,
      QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

#print axioms shift10_success
#print axioms shift20_success
#print axioms source_shift_embeddings
end AspisR1.SelectorValueLaneTailConstants
