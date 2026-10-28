import NDO_JFt_Snapshot08
set_option autoImplicit false
namespace AspisR1.JFt_Snapshot04
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_4 JFu_PublicRange.snapshot JFt_Digest01.value JFt_Digest02.value JFt_Digest03.value JFt_Digest04.value JFt_Digest05.value=ok (.Ok JFt_SnapshotValue.value) := by
  have tail:=JFt_Snapshot08.source
  unfold JFu_PublicRange.snapshot at tail
  unfold part_4
  simp only [JFu_PublicRange.snapshot,
    show (288#usize).val=288 from rfl,
    show (320#usize).val=320 from rfl,
    show (352#usize).val=352 from rfl,
    show (384#usize).val=384 from rfl,
    show (416#usize).val=416 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    JFt_Range.read 176 800 (by decide) 288#usize 320#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 320#usize 352#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 352#usize 384#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 384#usize 416#usize (by decide) (by decide),
    JFt_Digest06.source,
    JFt_Digest07.source,
    JFt_Digest08.source,
    JFt_Digest09.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Snapshot04
