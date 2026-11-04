import NFG_PrivateWindow
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_PrivateTrace
open Aeneas Aeneas.Std Result ControlFlow NFG_PrivateWindow
/-- Four windows are states of one receiver, with one unchanged raw result.
The conclusion never selects a reply from a model output. -/
theorem four (raw : Raw) (s0 s1 s2 s3 s4 : Dot)
 (w0 : Window s0 s1 raw ⟨0,by decide⟩)
 (w1 : Window s1 s2 raw ⟨1,by decide⟩)
 (w2 : Window s2 s3 raw ⟨2,by decide⟩)
 (w3 : Window s3 s4 raw ⟨3,by decide⟩) :
 FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize} s0 raw=ok s4 := by
 have t0:=step s0 s1 raw ⟨0,by decide⟩ w0
 have t1:=step s1 s2 raw ⟨1,by decide⟩ w1
 have t2:=step s2 s3 raw ⟨2,by decide⟩ w2
 have t3:=step s3 s4 raw ⟨3,by decide⟩ w3
 have t4 : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw
   {start:=4#usize,«end»:=4#usize} s4=ok (done s4) := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push_loop.body
  rw [OccupancyRangeTraversal.next_done _ (by decide),bind_tc_ok]
  rfl
 change loop (fun state : core.ops.range.Range Usize × Dot =>
   FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw state.1 state.2)
  ({start:=0#usize,«end»:=4#usize},s0)=ok s4
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
   · subst i;exact t0
   · subst i;exact t1
   · subst i;exact t2
   · subst i;exact t3
 · exact t4
#print axioms four
end AspisR1.NFG_PrivateTrace
end
