import NDO_JFt_Snapshot12
set_option autoImplicit false
namespace AspisR1.JFt_Snapshot08
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_8 JFu_PublicRange.snapshot JFt_Digest01.value JFt_Digest02.value JFt_Digest03.value JFt_Digest04.value JFt_Digest05.value JFt_Digest06.value JFt_Digest07.value JFt_Digest08.value JFt_Digest09.value=ok (.Ok JFt_SnapshotValue.value) := by
  have tail:=JFt_Snapshot12.source
  unfold JFu_PublicRange.snapshot at tail
  unfold part_8
  simp only [JFu_PublicRange.snapshot,
    show (416#usize).val=416 from rfl,
    show (448#usize).val=448 from rfl,
    show (480#usize).val=480 from rfl,
    show (512#usize).val=512 from rfl,
    show (544#usize).val=544 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    JFt_Range.read 176 800 (by decide) 416#usize 448#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 448#usize 480#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 480#usize 512#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 512#usize 544#usize (by decide) (by decide),
    JFt_Digest10.source,
    JFt_Digest11.source,
    JFt_Digest12.source,
    JFt_Digest13.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Snapshot08
