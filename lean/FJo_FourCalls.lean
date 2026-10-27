import FIp_DotsReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_FourCalls
open Aeneas Aeneas.Std Result
abbrev NE := FIo_Install.NE
/-- A source return at every slot; no interpretation is expanded here. -/
theorem reached (opening : Slice U8) (g : Array NE 29#usize) (out : Array NE 4#usize)
    (run : FIp_NativeDots.fast_dots.four_dots opening g=ok out) :
    ∃ (selected : Slice U8) (q : Array U8 608#usize), ∃ converted,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        opening {«end»:=608#usize}=ok selected ∧
      core.array.TryFromSharedArraySlice.try_from 608#usize selected=ok converted ∧
      core.result.Result.unwrap core.fmt.DebugTryFromSliceError converted=ok q ∧
      ∀ s : Fin 4, ∃ v,
        FIp_NativeDots.fast_dots.four_dots_one q g (Usize.ofNat s.val (by have:=s.isLt;scalar_tac))=ok v ∧
        out.val[s.val]?=some v := by
  obtain ⟨selected,q,v0,v1,v2,v3,converted,hs,hc,hp,h0,h1,h2,h3,ho⟩ := FIp_DotsReached.four opening g out run
  refine ⟨selected,q,converted,hs,hc,hp,?_⟩
  subst out
  intro s
  fin_cases s
  · exact ⟨v0,h0,rfl⟩
  · exact ⟨v1,h1,rfl⟩
  · exact ⟨v2,h2,rfl⟩
  · exact ⟨v3,h3,rfl⟩
#print axioms reached
end AspisR1.FJo_FourCalls
end
