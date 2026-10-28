import NDO_JFt_AfterstateDigest
import RPz7_S6NativeAfterstateDecoderFactoredV1
set_option autoImplicit false
namespace AspisR1.JFt_AfterstateTail
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_16 JFu_PublicRange.afterstate JFt_Digest22.value JFt_Digest23.value JFt_Digest24.value JFt_Digest25.value JFt_Digest26.value JFt_Digest27.value JFt_Digest28.value JFt_Digest29.value JFt_Digest30.value JFt_Digest31.value JFt_Digest32.value JFt_Digest33.value JFt_Digest34.value JFt_Digest35.value JFt_Digest36.value JFt_Digest37.value JFt_Digest38.value=ok (.Ok JFt_AfterstateValue.value) := by
  unfold part_16
  simp only [JFu_PublicRange.afterstate,
    JFt_Range.read 976 688 (by decide) 560#usize 592#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 592#usize 624#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 624#usize 656#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 656#usize 688#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 8#usize 16#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,
    show (16#usize).val=16 from rfl,
    show (560#usize).val=560 from rfl,
    show (592#usize).val=592 from rfl,
    show (624#usize).val=624 from rfl,
    show (656#usize).val=656 from rfl,
    show (688#usize).val=688 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFt_AfterstateDigest.exact39,
    JFt_AfterstateDigest.decode39,
    JFt_AfterstateDigest.exact40,
    JFt_AfterstateDigest.decode40,
    JFt_AfterstateDigest.exact41,
    JFt_AfterstateDigest.decode41,
    JFt_AfterstateDigest.exact42,
    JFt_AfterstateDigest.decode42,
    JFt_AfterstateDigest.next,
    JFu_PublicIndices.next,
    lift,bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch]
  have validated:=JFt_AfterstateValue.validated
  unfold JFt_AfterstateValue.value at validated
  rw [validated]
  rfl

#print axioms source
end AspisR1.JFt_AfterstateTail
