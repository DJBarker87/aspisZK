import LPf_DotWordStep
import JGo_TX2_Range
set_option autoImplicit false
namespace AspisR1.LPf_DotPushStep
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize

theorem source (self : Dot) (raw : Raw) (i next : Usize) (before term : U64)
    (hi : i.val < 4)
    (advance : core.iter.range.IteratorRange.next core.iter.range.StepUsize
      {start:=i,«end»:=4#usize} = ok (some i,{start:=next,«end»:=4#usize}))
    (oldRead : Array.index_usize self.sums i = ok before)
    (rawRead : Array.index_usize raw i = ok term) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=i,«end»:=4#usize} self =
      ok (.cont ({start:=next,«end»:=4#usize},
        ⟨self.sums.set i (U64.wrapping_add before (FIo_ReduceBounds.fold term))⟩)) := by
  obtain ⟨updated,write,same⟩ := WP.spec_imp_exists
    (Array.update_spec self.sums i
      (U64.wrapping_add before (FIo_ReduceBounds.fold term)) (by simpa using hi))
  subst updated
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [advance,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,oldRead,rawRead,bind_tc_ok,
    FIo_Native.fast_pairing.canonical.P,lift]
  change (do
    let a ← Array.update self.sums i (U64.wrapping_add before (FIo_ReduceBounds.fold term))
    ok (.cont ({start:=next,«end»:=4#usize},⟨a⟩))) = _
  rw [write,bind_tc_ok]

#print axioms source
end AspisR1.LPf_DotPushStep
