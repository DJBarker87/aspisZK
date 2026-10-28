import NDO_JGq_LowGroup0
import NDO_JGq_LowGroup1
import NDO_JGq_LowGroup2
import NDO_JGq_LowGroup3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Low
open Aeneas Aeneas.Std Result ControlFlow
abbrev S := core.ops.range.Range Usize × Array E 16#usize
def states : Nat → S
  | 0 => ({start:=0#usize,«end»:=16#usize},a0)
  | 1 => ({start:=1#usize,«end»:=16#usize},a1)
  | 2 => ({start:=2#usize,«end»:=16#usize},a2)
  | 3 => ({start:=3#usize,«end»:=16#usize},a3)
  | 4 => ({start:=4#usize,«end»:=16#usize},a4)
  | 5 => ({start:=5#usize,«end»:=16#usize},a5)
  | 6 => ({start:=6#usize,«end»:=16#usize},a6)
  | 7 => ({start:=7#usize,«end»:=16#usize},a7)
  | 8 => ({start:=8#usize,«end»:=16#usize},a8)
  | 9 => ({start:=9#usize,«end»:=16#usize},a9)
  | 10 => ({start:=10#usize,«end»:=16#usize},a10)
  | 11 => ({start:=11#usize,«end»:=16#usize},a11)
  | 12 => ({start:=12#usize,«end»:=16#usize},a12)
  | 13 => ({start:=13#usize,«end»:=16#usize},a13)
  | 14 => ({start:=14#usize,«end»:=16#usize},a14)
  | 15 => ({start:=15#usize,«end»:=16#usize},a15)
  | _ => ({start:=16#usize,«end»:=16#usize},a16)
theorem source : FIo_Native.weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize}
    JGq_Powers0.a4 JGq_Powers1.a4 (Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok a16 := by
  unfold FIo_Native.weights.Weights.pair_loop7
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.weights.Weights.pair_loop7.body JGq_Powers0.a4 JGq_Powers1.a4 s.1 s.2)
    states 16 a16
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
    · exact step4
    · exact step5
    · exact step6
    · exact step7
    · exact step8
    · exact step9
    · exact step10
    · exact step11
    · exact step12
    · exact step13
    · exact step14
    · exact step15
  · unfold FIo_Native.weights.Weights.pair_loop7.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_Low
end
