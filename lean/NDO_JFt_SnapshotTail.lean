import NDO_JFt_SnapshotValue
import RPz7_S6NativeSnapshotDecoderFactoredV1
set_option autoImplicit false
namespace AspisR1.JFt_SnapshotTail
open Aeneas Aeneas.Std Result
open AspisS6NativeSnapshotDecoderFactored

theorem source : part_16 JFu_PublicRange.snapshot JFt_Digest01.value JFt_Digest02.value JFt_Digest03.value JFt_Digest04.value JFt_Digest05.value JFt_Digest06.value JFt_Digest07.value JFt_Digest08.value JFt_Digest09.value JFt_Digest10.value JFt_Digest11.value JFt_Digest12.value JFt_Digest13.value JFt_Digest14.value JFt_Digest15.value JFt_Digest16.value JFt_Digest17.value=ok (.Ok JFt_SnapshotValue.value) := by
  unfold part_16
  simp only [JFu_PublicRange.snapshot,
    show (48#usize).val=48 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (120#usize).val=120 from rfl,
    show (128#usize).val=128 from rfl,
    show (672#usize).val=672 from rfl,
    show (704#usize).val=704 from rfl,
    show (736#usize).val=736 from rfl,
    show (768#usize).val=768 from rfl,
    show (800#usize).val=800 from rfl,
    Nat.reduceAdd,Nat.reduceSub,

    JFt_Range.read 176 800 (by decide) 672#usize 704#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 704#usize 736#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 736#usize 768#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 768#usize 800#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 48#usize 80#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 80#usize 112#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 112#usize 120#usize (by decide) (by decide),
    JFt_Range.read 176 800 (by decide) 120#usize 128#usize (by decide) (by decide),
    JFt_Digest18.source,
    JFt_Digest19.source,
    JFt_Digest20.source,
    JFt_Digest21.source,
    JFt_Metadata.pool,
    JFt_Metadata.domain,
    JFt_Metadata.sequence,
    JFt_Metadata.index,
    lift,bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    JFu_PublicIndices.sequence]
  have validated:=JFt_SnapshotValue.validated
  unfold JFt_SnapshotValue.value at validated
  rw [validated]
  rfl

#print axioms source
end AspisR1.JFt_SnapshotTail
