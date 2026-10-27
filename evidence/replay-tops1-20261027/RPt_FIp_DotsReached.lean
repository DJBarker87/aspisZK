import RPz7_FIp_NativeDots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_DotsReached
open Aeneas Aeneas.Std Result
abbrev NE := FIo_Install.NE

theorem four (q : Slice U8) (g : Array NE 29#usize) (out : Array NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots q g=ok out) :
    ∃ (selected : Slice U8) (prefix608 : Array U8 608#usize) (v0 v1 v2 v3 : NE),
      ∃ converted,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        q {«end»:=608#usize}=ok selected ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize selected=ok converted ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok prefix608 ∧
      FIp_NativeDots.fast_dots.four_dots_one prefix608 g 0#usize=ok v0 ∧
      FIp_NativeDots.fast_dots.four_dots_one prefix608 g 1#usize=ok v1 ∧
      FIp_NativeDots.fast_dots.four_dots_one prefix608 g 2#usize=ok v2 ∧
      FIp_NativeDots.fast_dots.four_dots_one prefix608 g 3#usize=ok v3 ∧
      out=Array.make 4#usize [v0,v1,v2,v3] := by
  unfold FIp_NativeDots.fast_dots.four_dots at run
  obtain ⟨selected,hs,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨converted,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨prefix608,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨v0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨v1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨v2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨v3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨selected,prefix608,v0,v1,v2,v3,converted,hs,hc,hp,h0,h1,h2,h3,(Result.ok.inj run).symm⟩

#print axioms four
end AspisR1.FIp_DotsReached
end
