import JGo_TX2_LoopChain
import JGo_TX2_Range
import FIo_Install
import JFs_TX2_RawMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_DotLoop
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Range := core.ops.range.Range Usize

def lane (old raw : U64) : U64 :=
  U64.wrapping_add old (U64.wrapping_add (raw &&& 2147483647#u64) (U64.wrapping_shr raw 31#u32))

def a (self : Dot) (raw : Array U64 4#usize) (i : Nat) : Dot :=
  ⟨Array.make 4#usize [if 0 < i then lane self.sums.val[0] raw.val[0] else self.sums.val[0],
    if 1 < i then lane self.sums.val[1] raw.val[1] else self.sums.val[1],
    if 2 < i then lane self.sums.val[2] raw.val[2] else self.sums.val[2],
    if 3 < i then lane self.sums.val[3] raw.val[3] else self.sums.val[3]]⟩

theorem step0 (self : Dot) (raw : Array U64 4#usize) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw {start:=0#usize,«end»:=4#usize}
      self=ok (.cont ({start:=1#usize,«end»:=4#usize},a self raw 1)) := by
  rcases self with ⟨sums⟩
  obtain ⟨x0,x1,x2,x3,rfl⟩ := JFs_TX2_RawMap.shape sums
  obtain ⟨r0,r1,r2,r3,rfl⟩ := JFs_TX2_RawMap.shape raw
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  with_unfolding_all rfl

#print axioms step0
end AspisR1.JGq_DotLoop
end
