import NCV_SequenceRun
import NCV_ArrayRead
import JHg_AuditMaster
import JHg_AuditForest
set_option autoImplicit false
namespace NCV_FixtureSequences
open Aeneas Aeneas.Std Result AspisR1

theorem master : NCV_CastRef.sequences JHg_DataMaster.value 320#usize=
    ok (Array.repeat 8#usize 0#u64) := by
  have len : JHg_DataMaster.value.val.length=384 := JHg_DataMaster.length
  apply NCV_SequenceRun.value _ _ _ (fun _=>Array.repeat 8#usize 0#u8)
    (by omega) (by scalar_tac)
  · intro k hk
    change (JHg_DataMaster.bytes.drop (320+8*k)).take 8=List.replicate 8 0#u8
    interval_cases k
    · exact JHg_AuditMaster.last_sequence_0
    · exact JHg_AuditMaster.last_sequence_1
    · exact JHg_AuditMaster.last_sequence_2
    · exact JHg_AuditMaster.last_sequence_3
    · exact JHg_AuditMaster.last_sequence_4
    · exact JHg_AuditMaster.last_sequence_5
    · exact JHg_AuditMaster.last_sequence_6
    · exact JHg_AuditMaster.last_sequence_7
  · intro k hk
    rw [NCV_ArrayRead.repeat_value 8#usize 0#u64 k (by simpa using hk)]
    rfl

theorem checkpoint : NCV_CastRef.sequences JHg_DataForest.value 112#usize=
    ok (Array.repeat 8#usize 0#u64) := by
  have len : JHg_DataForest.value.val.length=192 := JHg_DataForest.length
  apply NCV_SequenceRun.value _ _ _ (fun _=>Array.repeat 8#usize 0#u8)
    (by omega) (by scalar_tac)
  · intro k hk
    change (JHg_DataForest.bytes.drop (112+8*k)).take 8=List.replicate 8 0#u8
    interval_cases k
    · exact JHg_AuditForest.lane_sequence_0
    · exact JHg_AuditForest.lane_sequence_1
    · exact JHg_AuditForest.lane_sequence_2
    · exact JHg_AuditForest.lane_sequence_3
    · exact JHg_AuditForest.lane_sequence_4
    · exact JHg_AuditForest.lane_sequence_5
    · exact JHg_AuditForest.lane_sequence_6
    · exact JHg_AuditForest.lane_sequence_7
  · intro k hk
    rw [NCV_ArrayRead.repeat_value 8#usize 0#u64 k (by simpa using hk)]
    rfl

#print axioms master
#print axioms checkpoint
end NCV_FixtureSequences
