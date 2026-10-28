-- Inherited body, import-only deployed-cohort retarget.
import NCD_B_LPf_DotPushStep
import JGo_TX2_LoopChain
set_option autoImplicit false
namespace AspisR1.LPf_DotPushFour
open Aeneas Aeneas.Std Result ControlFlow
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Raw := Array U64 4#usize
def update (a r : U64) : U64 := U64.wrapping_add a (FIo_ReduceBounds.fold r)

theorem source (a b c d r0 r1 r2 r3 : U64) :
    FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize}
      ⟨Array.make 4#usize [a,b,c,d]⟩ (Array.make 4#usize [r0,r1,r2,r3]) =
      ok ⟨Array.make 4#usize [update a r0,update b r1,update c r2,update d r3]⟩ := by
  let raw : Raw := Array.make 4#usize [r0,r1,r2,r3]
  let s0 : Dot := ⟨Array.make 4#usize [a,b,c,d]⟩
  let s1 : Dot := ⟨Array.make 4#usize [update a r0,b,c,d]⟩
  let s2 : Dot := ⟨Array.make 4#usize [update a r0,update b r1,c,d]⟩
  let s3 : Dot := ⟨Array.make 4#usize [update a r0,update b r1,update c r2,d]⟩
  let s4 : Dot := ⟨Array.make 4#usize [update a r0,update b r1,update c r2,update d r3]⟩
  have t0 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=0#usize,«end»:=4#usize} s0 = ok (.cont ({start:=1#usize,«end»:=4#usize},s1)) := by
    exact LPf_DotPushStep.source s0 raw 0#usize 1#usize a r0 (by decide)
      (JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide)) rfl rfl
  have t1 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=1#usize,«end»:=4#usize} s1 = ok (.cont ({start:=2#usize,«end»:=4#usize},s2)) := by
    exact LPf_DotPushStep.source s1 raw 1#usize 2#usize b r1 (by decide)
      (JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide)) rfl rfl
  have t2 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=2#usize,«end»:=4#usize} s2 = ok (.cont ({start:=3#usize,«end»:=4#usize},s3)) := by
    exact LPf_DotPushStep.source s2 raw 2#usize 3#usize c r2 (by decide)
      (JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide)) rfl rfl
  have t3 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=3#usize,«end»:=4#usize} s3 = ok (.cont ({start:=4#usize,«end»:=4#usize},s4)) := by
    exact LPf_DotPushStep.source s3 raw 3#usize 4#usize d r3 (by decide)
      (JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide)) rfl rfl
  have t4 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
      {start:=4#usize,«end»:=4#usize} s4 = ok (.done s4) := by
    unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
    rw [OccupancyRangeTraversal.next_done _ (by decide),bind_tc_ok]
    rfl
  change loop (fun state : core.ops.range.Range Usize × Dot =>
    FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw state.1 state.2)
    ({start:=0#usize,«end»:=4#usize},s0) = ok s4
  let states : Nat → core.ops.range.Range Usize × Dot
    | 0 => ({start:=0#usize,«end»:=4#usize},s0)
    | 1 => ({start:=1#usize,«end»:=4#usize},s1)
    | 2 => ({start:=2#usize,«end»:=4#usize},s2)
    | 3 => ({start:=3#usize,«end»:=4#usize},s3)
    | _ => ({start:=4#usize,«end»:=4#usize},s4)
  apply JGo_TX2_LoopChain.source _ states 4 s4
  · intro i hi
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
    rcases cases with h | h | h | h
    · subst i; exact t0
    · subst i; exact t1
    · subst i; exact t2
    · subst i; exact t3
  · exact t4

#print axioms source
end AspisR1.LPf_DotPushFour
