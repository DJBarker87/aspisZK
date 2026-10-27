import FJg_ReaderScalarCanon
import CheckpointBytes4SavedFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_SourceCanonical
open CheckpointBytes4ReaderFields
open AspisR1CurrentWide.Proof

theorem k (x : OraclePortCheckpointAbiC5.K) : FJg_ReaderScalarCanon.CanonK (sourceK x) := by
  let limbs := RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x
  change ((M31ParserRefinement.valueToU32 (limbs 0)).val<2147483647 ∧
    (M31ParserRefinement.valueToU32 (limbs 1)).val<2147483647) ∧
    (
    (M31ParserRefinement.valueToU32 (limbs 2)).val<2147483647 ∧
    (M31ParserRefinement.valueToU32 (limbs 3)).val<2147483647)
  simp only [M31ParserRefinement.valueToU32_val]
  exact ⟨⟨(limbs 0).isLt,(limbs 1).isLt⟩,⟨(limbs 2).isLt,(limbs 3).isLt⟩⟩

theorem e (x : OraclePortCheckpointAbiC5.E) : FJg_ReaderScalarCanon.CanonE (sourceE x) := by
  exact ⟨k x.re,k x.im⟩

#print axioms k
#print axioms e
end AspisR1.FJr_SourceCanonical
end
