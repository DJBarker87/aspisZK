import JFw_TX2_DotsExplicit
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_PushStep
open Aeneas Aeneas.Std Result ControlFlow
open JFs_TX2_RawMap
abbrev plus (a b : U64) := U64.wrapping_add a (FIo_ReduceBounds.fold b)
theorem next0 : core.iter.range.IteratorRange.next core.iter.range.StepUsize
    {start:=0#usize,«end»:=4#usize}=ok (some 0#usize,{start:=1#usize,«end»:=4#usize}) := by rfl

theorem source0 (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body (pack r0 r1 r2 r3)
      {start:=0#usize,«end»:=4#usize} ⟨pack a b c d⟩=
      ok (cont ({start:=1#usize,«end»:=4#usize},⟨pack (plus a r0) b c d⟩)) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [next0]
  rfl
#print axioms next0
#print axioms source0
end AspisR1.JFw_TX2_PushStep
end
