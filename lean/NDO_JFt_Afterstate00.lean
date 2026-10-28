import NDO_JFt_Afterstate04
set_option autoImplicit false
namespace AspisR1.JFt_Afterstate00
open Aeneas Aeneas.Std Result
open AspisS6NativeAfterstateDecoderFactored

theorem source : part_0 JFu_PublicRange.afterstate JFt_Digest22.value=ok (.Ok JFt_AfterstateValue.value) := by
  have tail:=JFt_Afterstate04.source
  unfold JFu_PublicRange.afterstate at tail
  unfold part_0
  simp only [JFu_PublicRange.afterstate,
    JFt_Range.read 976 688 (by decide) 48#usize 80#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 80#usize 112#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 112#usize 144#usize (by decide) (by decide),
    JFt_Range.read 976 688 (by decide) 144#usize 176#usize (by decide) (by decide),
    show (48#usize).val=48 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (144#usize).val=144 from rfl,
    show (176#usize).val=176 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFt_AfterstateDigest.exact23,
    JFt_AfterstateDigest.decode23,
    JFt_AfterstateDigest.exact24,
    JFt_AfterstateDigest.decode24,
    JFt_AfterstateDigest.exact25,
    JFt_AfterstateDigest.decode25,
    JFt_AfterstateDigest.exact26,
    JFt_AfterstateDigest.decode26,
    bind_tc_ok,
    AspisR1TerminalDecoder.core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    tail]

#print axioms source
end AspisR1.JFt_Afterstate00
