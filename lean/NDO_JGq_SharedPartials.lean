import NDO_JGq_Partial0
import NDO_JGq_Partial1
import NDO_JGq_Partial2
import NDO_JGq_Partial3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_SharedPartials
open Aeneas Aeneas.Std Result ControlFlow
open JGq_Partial
abbrev E := FIo_Install.NE
def a0 : Array E 4#usize := Array.repeat 4#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
def a1 : Array E 4#usize := Array.make 4#usize [value0,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a2 : Array E 4#usize := Array.make 4#usize [value0,value1,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def a3 : Array E 4#usize := Array.make 4#usize [value0,value1,value2,FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO]
def value : Array E 4#usize := Array.make 4#usize [value0,value1,value2,value3]
theorem step0 : FIo_Native.weights.shared_partials_loop.body f JGq_Common.a16
    {start:=0#usize,«end»:=4#usize} a0=
    ok (.cont ({start:=1#usize,«end»:=4#usize},a1)) := by
  unfold FIo_Native.weights.shared_partials_loop.body
  rw [JGo_TX2_Range.next 0#usize 4#usize 1#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [source0,bind_tc_ok]
  rfl
#print axioms step0
theorem step1 : FIo_Native.weights.shared_partials_loop.body f JGq_Common.a16
    {start:=1#usize,«end»:=4#usize} a1=
    ok (.cont ({start:=2#usize,«end»:=4#usize},a2)) := by
  unfold FIo_Native.weights.shared_partials_loop.body
  rw [JGo_TX2_Range.next 1#usize 4#usize 2#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [source1,bind_tc_ok]
  rfl
#print axioms step1
theorem step2 : FIo_Native.weights.shared_partials_loop.body f JGq_Common.a16
    {start:=2#usize,«end»:=4#usize} a2=
    ok (.cont ({start:=3#usize,«end»:=4#usize},a3)) := by
  unfold FIo_Native.weights.shared_partials_loop.body
  rw [JGo_TX2_Range.next 2#usize 4#usize 3#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [source2,bind_tc_ok]
  rfl
#print axioms step2
theorem step3 : FIo_Native.weights.shared_partials_loop.body f JGq_Common.a16
    {start:=3#usize,«end»:=4#usize} a3=
    ok (.cont ({start:=4#usize,«end»:=4#usize},value)) := by
  unfold FIo_Native.weights.shared_partials_loop.body
  rw [JGo_TX2_Range.next 3#usize 4#usize 4#usize (by decide) (by decide),bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [source3,bind_tc_ok]
  rfl
#print axioms step3
abbrev S := core.ops.range.Range Usize × Array E 4#usize
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=4#usize},a0)
  | 1 => ({start:=1#usize,«end»:=4#usize},a1)
  | 2 => ({start:=2#usize,«end»:=4#usize},a2)
  | 3 => ({start:=3#usize,«end»:=4#usize},a3)
  | _ => ({start:=4#usize,«end»:=4#usize},value)
theorem source : FIo_Native.weights.shared_partials f JGq_Common.a16=ok (.Ok value) := by
  unfold FIo_Native.weights.shared_partials FIo_Native.weights.shared_partials_loop
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.weights.shared_partials_loop.body f JGq_Common.a16 s.1 s.2)
    states 4 (.Ok value)
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
  · unfold FIo_Native.weights.shared_partials_loop.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_SharedPartials
end
