import NDO_JFt_SnapshotTail
set_option autoImplicit false
namespace AspisR1.JFt_Snapshot12
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_12 JFu_PublicRange.snapshot JFt_Digest01.value JFt_Digest02.value JFt_Digest03.value JFt_Digest04.value JFt_Digest05.value JFt_Digest06.value JFt_Digest07.value JFt_Digest08.value JFt_Digest09.value JFt_Digest10.value JFt_Digest11.value JFt_Digest12.value JFt_Digest13.value=ok (.Ok JFt_SnapshotValue.value) := by
  have tail:=JFt_SnapshotTail.source
  unfold JFu_PublicRange.snapshot at tail
  unfold part_12
  simp only [JFu_PublicRange.snapshot,
    show (544#usize).val=544 from rfl,
    show (576#usize).val=576 from rfl,
    show (608#usize).val=608 from rfl,
    show (640#usize).val=640 from rfl,
    show (672#usize).val=672 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    JFt_Range.read 176 800 (by decide) 544#usize 576#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 576#usize 608#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 608#usize 640#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 640#usize 672#usize (by decide) (by decide),
    JFt_Digest14.source,
    JFt_Digest15.source,
    JFt_Digest16.source,
    JFt_Digest17.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Snapshot12
