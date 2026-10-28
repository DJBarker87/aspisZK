import NDO_JFt_Snapshot04
set_option autoImplicit false
namespace AspisR1.JFt_Snapshot00
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_0 JFu_PublicRange.snapshot JFt_Digest01.value=ok (.Ok JFt_SnapshotValue.value) := by
  have tail:=JFt_Snapshot04.source
  unfold JFu_PublicRange.snapshot at tail
  unfold part_0
  simp only [JFu_PublicRange.snapshot,
    show (160#usize).val=160 from rfl,
    show (192#usize).val=192 from rfl,
    show (224#usize).val=224 from rfl,
    show (256#usize).val=256 from rfl,
    show (288#usize).val=288 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    JFt_Range.read 176 800 (by decide) 160#usize 192#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 192#usize 224#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 224#usize 256#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 256#usize 288#usize (by decide) (by decide),
    JFt_Digest02.source,
    JFt_Digest03.source,
    JFt_Digest04.source,
    JFt_Digest05.source,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Snapshot00
