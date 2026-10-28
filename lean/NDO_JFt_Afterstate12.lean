import NDO_JFt_AfterstateTail
set_option autoImplicit false
namespace AspisR1.JFt_Afterstate12
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_12 JFu_PublicRange.afterstate JFt_Digest22.value JFt_Digest23.value JFt_Digest24.value JFt_Digest25.value JFt_Digest26.value JFt_Digest27.value JFt_Digest28.value JFt_Digest29.value JFt_Digest30.value JFt_Digest31.value JFt_Digest32.value JFt_Digest33.value JFt_Digest34.value=ok (.Ok JFt_AfterstateValue.value) := by
  have tail:=JFt_AfterstateTail.source
  unfold JFu_PublicRange.afterstate at tail
  unfold part_12
  simp only [JFu_PublicRange.afterstate,
    JFt_Range.read 976 688 (by decide) 432#usize 464#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 464#usize 496#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 496#usize 528#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 528#usize 560#usize (by decide) (by decide),
    show (432#usize).val=432 from rfl,
    show (464#usize).val=464 from rfl,
    show (496#usize).val=496 from rfl,
    show (528#usize).val=528 from rfl,
    show (560#usize).val=560 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFt_AfterstateDigest.exact35,
    JFt_AfterstateDigest.decode35,
    JFt_AfterstateDigest.exact36,
    JFt_AfterstateDigest.decode36,
    JFt_AfterstateDigest.exact37,
    JFt_AfterstateDigest.decode37,
    JFt_AfterstateDigest.exact38,
    JFt_AfterstateDigest.decode38,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Afterstate12
