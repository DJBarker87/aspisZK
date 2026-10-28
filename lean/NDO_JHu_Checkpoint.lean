import NDO_JHu_CheckpointAssembly
import JHu_FixtureSequences
import NDO_JHu_FixtureDigests
import JHu_ZeroFields
import NDO_NCV_FieldViews
import NCV_SequenceValidation
import NCV_Install
set_option autoImplicit false
namespace AspisR1.JHu_Checkpoint
open Aeneas Aeneas.Std Result
attribute [local irreducible] JHg_DataForest.bytes

theorem source : NCV_Reference.decode_checkpoint_ref JHg_DataForest.value=
    ok (.Ok (NCV_Carrier.fromCheckpoint JHg_AccountValues.checkpoint)) := by
  have len : JHg_DataForest.value.val.length=192 := JHg_DataForest.length
  apply JHu_CheckpointAssembly.source
  · scalar_tac
  · exact NCV_FieldViews.read_prefix _ 4#usize (by scalar_tac)
  · apply JHu_ZeroFields.equal
    · rw [JHg_FieldRead.length _ 0 4 (by omega)];omega
    · exact JHg_AuditForest.magic
  · exact NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditForest.version
  · exact NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditForest.lanes
  · exact NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditForest.encoding
  · have h:=MultiproofConeSlices.drop_total JHg_DataForest.value 176#usize (by scalar_tac)
    rw [NCV_FieldViews.suffix,len] at h
    exact h
  · exact JHu_ZeroFields.zero _ 16 JHg_AuditForest.reserved (by omega)
  · apply JHu_ReferenceBytes.bytes32 _ _ _ (by omega) (by scalar_tac)
    exact JHg_AuditForest.master
  · apply JHu_ReferenceBytes.bytes32 _ _ _ (by omega) (by scalar_tac)
    exact JHg_AuditForest.domain.trans JHg_AuditMaster.domain.symm
  · apply JHu_ZeroFields.nonzero
    · exact Nat.le_trans (by change 32 ≤ 768;omega) (Nat.le_refl 768)
    · change (34#u8 : U8) ≠ 0#u8
      scalar_tac
    · change 0<32
      omega
  · apply JHu_ZeroFields.nonzero
    · change 32 ≤ 768
      omega
    · change (5#u8 : U8) ≠ 0#u8
      scalar_tac
    · change 0<32
      omega
  · exact JHu_FixtureDigests.checkpoint
  · exact JHu_FixtureSequences.checkpoint
  · apply NCV_SequenceValidation.valid
    intro j hj
    change (NCV_ArrayFrame.coord (Array.repeat 8#usize 0#u64) j).val ≤ 1048576
    rw [NCV_ArrayRead.repeat_value _ _ j (by simpa using hj)]
    scalar_tac
  · exact NCV_FieldViews.byte _ _ _ (by scalar_tac) JHg_AuditForest.bump
  · apply JHu_ReferenceWords.word64 _ _ _ (by omega) (by scalar_tac)
    exact JHg_Scalar09.bytes
#print axioms source

theorem observation : NCV_Install.op49 JHg_DataForest.value=ok (.Ok JHg_AccountValues.checkpoint) := by
  simp only [NCV_Install.op49,source,bind_tc_ok,NCV_Install.mapReturn,NCV_Carrier.checkpoint_surjective]
#print axioms observation
end AspisR1.JHu_Checkpoint
