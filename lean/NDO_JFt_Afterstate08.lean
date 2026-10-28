import NDO_JFt_Afterstate12
set_option autoImplicit false
namespace AspisR1.JFt_Afterstate08
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_8 JFu_PublicRange.afterstate JFt_Digest22.value JFt_Digest23.value JFt_Digest24.value JFt_Digest25.value JFt_Digest26.value JFt_Digest27.value JFt_Digest28.value JFt_Digest29.value JFt_Digest30.value=ok (.Ok JFt_AfterstateValue.value) := by
  have tail:=JFt_Afterstate12.source
  unfold JFu_PublicRange.afterstate at tail
  unfold part_8
  simp only [JFu_PublicRange.afterstate,
    JFt_Range.read 976 688 (by decide) 304#usize 336#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 336#usize 368#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 368#usize 400#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 400#usize 432#usize (by decide) (by decide),
    show (304#usize).val=304 from rfl,
    show (336#usize).val=336 from rfl,
    show (368#usize).val=368 from rfl,
    show (400#usize).val=400 from rfl,
    show (432#usize).val=432 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFt_AfterstateDigest.exact31,
    JFt_AfterstateDigest.decode31,
    JFt_AfterstateDigest.exact32,
    JFt_AfterstateDigest.decode32,
    JFt_AfterstateDigest.exact33,
    JFt_AfterstateDigest.decode33,
    JFt_AfterstateDigest.exact34,
    JFt_AfterstateDigest.decode34,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Afterstate08
