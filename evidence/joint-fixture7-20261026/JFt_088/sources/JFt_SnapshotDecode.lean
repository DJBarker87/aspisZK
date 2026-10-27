import JFt_Snapshot00
import JFt_SnapshotBytes
import JFt_SnapshotConstants
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem factored : AspisS6NativeSnapshotDecoderFactored.decode JFu_PublicRange.snapshot=
    ok (.Ok JFt_SnapshotValue.value) := by
  have size : Slice.len JFu_PublicRange.snapshot=800#usize := by
    have h:=JFu_PublicRange.length 176 800 (by decide)
    change (JFu_PublicRange.segment 176 800 (by decide)).length=800 at h
    scalar_tac
  have tail:=JFt_Snapshot00.source
  unfold JFu_PublicRange.snapshot at tail
  unfold AspisS6NativeSnapshotDecoderFactored.decode
  simp only [size,POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,ne_self,Bool.false_eq_true,↓reduceIte]
  simp only [JFu_PublicRange.snapshot,
    JFt_LocalWindow.firstn 176 800 8#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,JFt_SnapshotHeader.magic_selected,
    JFt_SnapshotConstants.magic_array,bind_tc_ok,JFt_SnapshotConstants.magic_compare]
  simp only [←JFu_PublicRange.snapshot,JFt_SnapshotBytes.b8,JFt_SnapshotBytes.b9,
    JFt_SnapshotBytes.b10,JFt_SnapshotBytes.b11,JFt_SnapshotBytes.b12,JFt_SnapshotBytes.b13,
    JFt_SnapshotBytes.b14,JFt_SnapshotBytes.b15,bind_tc_ok,
    POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION,ne_self,Bool.false_eq_true,↓reduceIte]
  simp only [JFu_PublicRange.snapshot,
    JFt_Range.read 176 800 (by decide) 16#usize 48#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 128#usize 160#usize (by decide) (by decide),
    show (16#usize).val=16 from rfl,show (48#usize).val=48 from rfl,
    show (128#usize).val=128 from rfl,show (160#usize).val=160 from rfl,Nat.reduceAdd,Nat.reduceSub,
    JFt_SnapshotHeader.format_selected,JFt_SnapshotConstants.format_call,
    JFt_SnapshotConstants.format_array,JFt_SnapshotConstants.format_compare,
    JFt_Digest01.source,bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    Bool.false_eq_true,↓reduceIte,tail]

theorem source : decode_pool_v1_pair_live_snapshot_v1 JFu_PublicRange.snapshot=
    ok (.Ok JFt_SnapshotValue.value) :=
  (AspisS6NativeSnapshotDecoderFactored.decode_source _).symm.trans factored

#print axioms factored
#print axioms source
end AspisR1.JFt_SnapshotDecode
