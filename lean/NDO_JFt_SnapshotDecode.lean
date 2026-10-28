import NDO_JFt_Snapshot00
import NDO_JFt_SnapshotBytes
import NDO_JFt_SnapshotConstants
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotDecode
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem factored : AspisS6NativeSnapshotDecoderFactored.decode JFu_PublicRange.snapshot=
    ok (.Ok JFt_SnapshotValue.value) := by
  have size : Slice.len JFu_PublicRange.snapshot=800#usize := by
    have h : JFu_PublicRange.snapshot.length=800 := JFu_PublicRange.length 176 800 (by decide)
    scalar_tac
  have lengthCheck : (800#usize !=800#usize)=false := by decide
  have oneCheck : (1#u8 !=1#u8)=false := by decide
  have zeroCheck : (0#u8 !=0#u8)=false := by decide
  have b8:=JFt_SnapshotBytes.b8
  unfold JFu_PublicRange.snapshot at b8
  have b9:=JFt_SnapshotBytes.b9
  unfold JFu_PublicRange.snapshot at b9
  have b10:=JFt_SnapshotBytes.b10
  unfold JFu_PublicRange.snapshot at b10
  have b11:=JFt_SnapshotBytes.b11
  unfold JFu_PublicRange.snapshot at b11
  have b12:=JFt_SnapshotBytes.b12
  unfold JFu_PublicRange.snapshot at b12
  have b13:=JFt_SnapshotBytes.b13
  unfold JFu_PublicRange.snapshot at b13
  have b14:=JFt_SnapshotBytes.b14
  unfold JFu_PublicRange.snapshot at b14
  have b15:=JFt_SnapshotBytes.b15
  unfold JFu_PublicRange.snapshot at b15
  have tail:=JFt_Snapshot00.source
  unfold JFu_PublicRange.snapshot at tail
  unfold AspisS6NativeSnapshotDecoderFactored.decode
  simp only [size,POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,lengthCheck,oneCheck,zeroCheck,Bool.false_eq_true,↓reduceIte]
  simp only [JFu_PublicRange.snapshot,
    JFt_LocalWindow.firstn 176 800 8#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,JFt_SnapshotHeader.magic_selected,
    JFt_SnapshotConstants.magic_array,bind_tc_ok,JFt_SnapshotConstants.magic_compare]
  simp only [b8,b9,
    b10,b11,b12,b13,
    b14,b15,bind_tc_ok,
    POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION,lengthCheck,oneCheck,zeroCheck,Bool.false_eq_true,↓reduceIte]
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
