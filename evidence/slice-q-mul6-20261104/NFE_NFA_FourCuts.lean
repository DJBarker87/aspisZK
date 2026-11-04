import NFE_NFA_DotCuts
import NEV_FourResult
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFA_FourCuts
open Aeneas Aeneas.Std Result
/-- The SAME original slice prefix, actual conversion, all four fixed calls
and ordered results follow from one accepted actual wrapper execution. -/
theorem actual (q : Slice U8) (g : NEV_DotInputs.Coefficients)
    (out : Array NEV_DotCarrier.NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots q g=ok out) :
    ∃ window converted fixed a b c d,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        q {«end»:=608#usize}=ok window ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize window=ok converted ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok fixed ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 0#usize=ok a ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 1#usize=ok b ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 2#usize=ok c ∧
      FIp_NativeDots.fast_dots.four_dots_one fixed g 3#usize=ok d ∧
      out=Array.make 4#usize [a,b,c,d] := by
  unfold FIp_NativeDots.fast_dots.four_dots at run
  obtain ⟨window,select,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨converted,convert,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨fixed,unwrap,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨a,callA,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨b,callB,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨c,callC,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨d,callD,run⟩:=Port3_PushFrame.bind_success _ _ _ run
  exact ⟨window,converted,fixed,a,b,c,d,select,convert,unwrap,callA,callB,callC,callD,
    (Result.ok.inj run).symm⟩
#print axioms actual
end AspisR1.NFE_NFA_FourCuts
end
