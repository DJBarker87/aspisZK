import NDO_JFt_Afterstate08
set_option autoImplicit false
namespace AspisR1.JFt_Afterstate04
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_4 JFu_PublicRange.afterstate JFt_Digest22.value JFt_Digest23.value JFt_Digest24.value JFt_Digest25.value JFt_Digest26.value=ok (.Ok JFt_AfterstateValue.value) := by
  have tail:=JFt_Afterstate08.source
  unfold JFu_PublicRange.afterstate at tail
  unfold part_4
  simp only [JFu_PublicRange.afterstate,
    JFt_Range.read 976 688 (by decide) 176#usize 208#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 208#usize 240#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 240#usize 272#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 272#usize 304#usize (by decide) (by decide),
    show (176#usize).val=176 from rfl,
    show (208#usize).val=208 from rfl,
    show (240#usize).val=240 from rfl,
    show (272#usize).val=272 from rfl,
    show (304#usize).val=304 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFt_AfterstateDigest.exact27,
    JFt_AfterstateDigest.decode27,
    JFt_AfterstateDigest.exact28,
    JFt_AfterstateDigest.decode28,
    JFt_AfterstateDigest.exact29,
    JFt_AfterstateDigest.decode29,
    JFt_AfterstateDigest.exact30,
    JFt_AfterstateDigest.decode30,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Afterstate04
