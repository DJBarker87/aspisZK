import NDO_JGq_CommonStep00
import NDO_JGq_CommonStep01
import NDO_JGq_CommonStep02
import NDO_JGq_CommonStep03
import NDO_JGq_CommonStep04
import NDO_JGq_CommonStep05
import NDO_JGq_CommonStep06
import NDO_JGq_CommonStep07
import NDO_JGq_CommonStep08
import NDO_JGq_CommonStep09
import NDO_JGq_CommonStep10
import NDO_JGq_CommonStep11
import NDO_JGq_CommonStep12
import NDO_JGq_CommonStep13
import NDO_JGq_CommonStep14
import NDO_JGq_CommonStep15
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Common
open Aeneas Aeneas.Std Result ControlFlow
abbrev S := core.ops.range.Range Usize × Array Q 16#usize
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
theorem source : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
    w (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (w,a16) := by
  unfold FIo_Native.weights.Weights.pair_loop1
  apply JGo_TX2_LoopChain.source
    (fun s : S=>FIo_Native.weights.Weights.pair_loop1.body w s.1 s.2) states 16 (w,a16)
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
  · unfold FIo_Native.weights.Weights.pair_loop1.body
    with_unfolding_all rfl
#print axioms source
end AspisR1.JGq_Common
end
