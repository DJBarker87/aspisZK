import NDO_JFw_TX2_PushStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_FoldPush
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev loopCall := FIo_Native.fast_pairing.canonical.Dot.push_loop
abbrev plus (a b : U64) := U64.wrapping_add a (FIo_ReduceBounds.fold b)

theorem source (a b c d r0 r1 r2 r3 : U64) :
    loopCall {start:=0#usize,«end»:=4#usize} ⟨pack a b c d⟩ (pack r0 r1 r2 r3)=
      ok (⟨pack (plus a r0) (plus b r1) (plus c r2) (plus d r3)⟩ : Dot) := by
  dsimp only [loopCall]
  erw [FIo_Native.fast_pairing.canonical.Dot.push_loop.eq_def,Aeneas.Std.loop.eq_def]
  simp only [JFw_TX2_PushStep.source0]
  change loopCall {start:=1#usize,«end»:=4#usize}
    ⟨pack (plus a r0) b c d⟩ (pack r0 r1 r2 r3)=_
  dsimp only [loopCall]
  erw [FIo_Native.fast_pairing.canonical.Dot.push_loop.eq_def,Aeneas.Std.loop.eq_def]
  simp only [JFw_TX2_PushStep.source1]
  change loopCall {start:=2#usize,«end»:=4#usize}
    ⟨pack (plus a r0) (plus b r1) c d⟩ (pack r0 r1 r2 r3)=_
  dsimp only [loopCall]
  erw [FIo_Native.fast_pairing.canonical.Dot.push_loop.eq_def,Aeneas.Std.loop.eq_def]
  simp only [JFw_TX2_PushStep.source2]
  change loopCall {start:=3#usize,«end»:=4#usize}
    ⟨pack (plus a r0) (plus b r1) (plus c r2) d⟩ (pack r0 r1 r2 r3)=_
  dsimp only [loopCall]
  erw [FIo_Native.fast_pairing.canonical.Dot.push_loop.eq_def,Aeneas.Std.loop.eq_def]
  simp only [JFw_TX2_PushStep.source3]
  change loopCall {start:=4#usize,«end»:=4#usize}
    ⟨pack (plus a r0) (plus b r1) (plus c r2) (plus d r3)⟩ (pack r0 r1 r2 r3)=_
  dsimp only [loopCall]
  erw [FIo_Native.fast_pairing.canonical.Dot.push_loop.eq_def,Aeneas.Std.loop.eq_def]
  simp only [JFw_TX2_PushStep.source4]
#print axioms source
end AspisR1.JFw_TX2_FoldPush
end
