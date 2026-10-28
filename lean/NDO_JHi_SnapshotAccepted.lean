import NDO_JHi_SnapshotDecoderAction
import NDO_JHi_RawValuesValidated
import JHi_RetypePairSuccess
import RPz7_S6NativeSnapshotEncodeSuccessV1
set_option autoImplicit false
namespace AspisR1.JHi_SnapshotAccepted
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct

theorem source (output : Slice U8) (size : output.length=800) : ∃ updated : Slice U8,
    aspis_statement.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
      JHg_RawCommon.common.lane_transition.live_snapshot output=ok (.Ok (),updated) ∧
    updated.length=800 := by
  obtain ⟨⟨status,updated⟩,run,success⟩:=WP.spec_imp_exists
    (AspisS6NativeSnapshotEncoderGraph.encode_success JFt_SnapshotValue.value output size JFt_SnapshotValue.validated)
  have len:=AspisS6NativeSnapshotEncodeTotal.encode_spec JFt_SnapshotValue.value output
  rw [run,WP.spec_ok] at len
  change status=core.result.Result.Ok () at success
  subst status
  have usize : Slice.len output=800#usize := by scalar_tac
  rw [JHi_SnapshotDecoderAction.source _ output usize JFt_SnapshotValue.validated] at run
  have raw:=JHi_SnapshotBody.source _ output usize JHi_RawValuesValidated.snapshot
  have same : JHi_SnapshotBody.decode JHg_RawCommon.common.lane_transition.live_snapshot=
      JFt_SnapshotValue.value := rfl
  rw [same] at raw
  exact ⟨updated,raw.trans (JHi_RetypePairSuccess.source _ _ run),len.trans size⟩
#print axioms source
end AspisR1.JHi_SnapshotAccepted
