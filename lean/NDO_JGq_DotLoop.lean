import JGo_TX2_LoopChain
import JGo_TX2_Range
import RPz7_FIo_Install
import RPu_JFs_TX2_RawMap
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
theorem step1 (self : Dot) (raw : Array U64 4#usize) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw {start:=1#usize,«end»:=4#usize}
      (a self raw 1)=ok (.cont ({start:=2#usize,«end»:=4#usize},a self raw 2)) := by
  rcases self with ⟨sums⟩
  obtain ⟨x0,x1,x2,x3,rfl⟩ := JFs_TX2_RawMap.shape sums
  obtain ⟨r0,r1,r2,r3,rfl⟩ := JFs_TX2_RawMap.shape raw
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  with_unfolding_all rfl
#print axioms step1
theorem step2 (self : Dot) (raw : Array U64 4#usize) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw {start:=2#usize,«end»:=4#usize}
      (a self raw 2)=ok (.cont ({start:=3#usize,«end»:=4#usize},a self raw 3)) := by
  rcases self with ⟨sums⟩
  obtain ⟨x0,x1,x2,x3,rfl⟩ := JFs_TX2_RawMap.shape sums
  obtain ⟨r0,r1,r2,r3,rfl⟩ := JFs_TX2_RawMap.shape raw
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  with_unfolding_all rfl
#print axioms step2
theorem step3 (self : Dot) (raw : Array U64 4#usize) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw {start:=3#usize,«end»:=4#usize}
      (a self raw 3)=ok (.cont ({start:=4#usize,«end»:=4#usize},a self raw 4)) := by
  rcases self with ⟨sums⟩
  obtain ⟨x0,x1,x2,x3,rfl⟩ := JFs_TX2_RawMap.shape sums
  obtain ⟨r0,r1,r2,r3,rfl⟩ := JFs_TX2_RawMap.shape raw
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  with_unfolding_all rfl
#print axioms step3
theorem eta (self : Dot) (raw : Array U64 4#usize) : a self raw 0=self := by
  rcases self with ⟨sums⟩
  obtain ⟨x0,x1,x2,x3,rfl⟩ := JFs_TX2_RawMap.shape sums
  rfl
#print axioms eta
abbrev S := Range × Dot
def states (self : Dot) (raw : Array U64 4#usize) : Nat → S
  | 0 => ({start:=0#usize,«end»:=4#usize},self)
  | 1 => ({start:=1#usize,«end»:=4#usize},a self raw 1)
  | 2 => ({start:=2#usize,«end»:=4#usize},a self raw 2)
  | 3 => ({start:=3#usize,«end»:=4#usize},a self raw 3)
  | _ => ({start:=4#usize,«end»:=4#usize},a self raw 4)
theorem source (self : Dot) (raw : Array U64 4#usize) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize} self raw=ok (a self raw 4) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw s.1 s.2)
    (states self raw) 4 (a self raw 4)
  · intro i hi
    interval_cases i
    · exact step0 self raw
    · exact step1 self raw
    · exact step2 self raw
    · exact step3 self raw
  · unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_DotLoop
end
