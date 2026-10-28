import NDO_JGo_TX2_WeightRows
import NDO_JGo_TX2_WeightPoints
import JGo_TX2_Range
import NDO_JGo_TX2_ZOuterTools
import NDO_JGo_TX2_WeightZPins
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightConstruct
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
abbrev Range := core.ops.range.Range Usize
attribute [local irreducible] weights_new_loop1_loop0
theorem first0 : weights_new_loop0.body points {start:=0#usize,«end»:=3#usize} factors00=
    ok (ControlFlow.cont ({start:=1#usize,«end»:=3#usize},factors05)) := by
  unfold weights_new_loop0.body
  rw [JGo_TX2_Range.next 0#usize 3#usize 1#usize (by decide) (by decide)]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [JGo_TX2_WeightRows.inner0,bind_tc_ok]
#print axioms first0
theorem first1 : weights_new_loop0.body points {start:=1#usize,«end»:=3#usize} factors05=
    ok (ControlFlow.cont ({start:=2#usize,«end»:=3#usize},factors10)) := by
  unfold weights_new_loop0.body
  rw [JGo_TX2_Range.next 1#usize 3#usize 2#usize (by decide) (by decide)]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [JGo_TX2_WeightRows.inner1,bind_tc_ok]
#print axioms first1
theorem first2 : weights_new_loop0.body points {start:=2#usize,«end»:=3#usize} factors10=
    ok (ControlFlow.cont ({start:=3#usize,«end»:=3#usize},factors15)) := by
  unfold weights_new_loop0.body
  rw [JGo_TX2_Range.next 2#usize 3#usize 3#usize (by decide) (by decide)]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [JGo_TX2_WeightRows.inner2,bind_tc_ok]
#print axioms first2
def firstStates : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=3#usize},factors00)
  | 1 => ({start:=1#usize,«end»:=3#usize},factors05)
  | 2 => ({start:=2#usize,«end»:=3#usize},factors10)
  | _ => ({start:=3#usize,«end»:=3#usize},factors15)
theorem firstLoop : weights_new_loop0 {start:=0#usize,«end»:=3#usize} points factors00=ok factors15 := by
  unfold weights_new_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop0.body points iter factors)
    firstStates 3 factors15
  · intro i hi
    interval_cases i
    · exact first0
    · exact first1
    · exact first2
  · rfl
#print axioms firstLoop
theorem second0 : weights_new_loop1.body z {start:=0#usize,«end»:=2#usize} factors15=
    ok (.cont ({start:=1#usize,«end»:=2#usize},factors20)) := by
  have inner : weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize}
      (JGo_TX2_WeightZPins.back0 r3_1) 0#usize x0_1=ok factors20 := by
    rw [JGo_TX2_WeightZPins.back0_pin]
    exact JGo_TX2_WeightRows.inner3
  exact JGo_TX2_ZOuterTools.source z _ _ factors15 factors20 0#usize 3#usize
    (⟨z0x,z0y⟩ : circle.SecureCirclePoint) z0product x0_1 r3_0 r3_1 JGo_TX2_WeightZPins.back0
    (JGo_TX2_Range.next 0#usize 2#usize 1#usize (by decide) (by decide))
    (by rfl) JGo_TX2_WeightRow3.product
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide)))
    JGo_TX2_WeightZPins.read0 JGo_TX2_WeightZPins.write0 JGo_TX2_WeightRow3.double inner
#print axioms second0
theorem second1 : weights_new_loop1.body z {start:=1#usize,«end»:=2#usize} factors20=
    ok (.cont ({start:=2#usize,«end»:=2#usize},factors25)) := by
  have inner : weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize}
      (JGo_TX2_WeightZPins.back1 r4_1) 1#usize x1_1=ok factors25 := by
    rw [JGo_TX2_WeightZPins.back1_pin]
    exact JGo_TX2_WeightRows.inner4
  exact JGo_TX2_ZOuterTools.source z _ _ factors20 factors25 1#usize 4#usize
    (⟨z1x,z1y⟩ : circle.SecureCirclePoint) z1product x1_1 r4_0 r4_1 JGo_TX2_WeightZPins.back1
    (JGo_TX2_Range.next 1#usize 2#usize 2#usize (by decide) (by decide))
    (by rfl) JGo_TX2_WeightRow4.product
    (UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 1#usize (by decide)))
    JGo_TX2_WeightZPins.read1 JGo_TX2_WeightZPins.write1 JGo_TX2_WeightRow4.double inner
#print axioms second1
def secondStates : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=2#usize},factors15)
  | 1 => ({start:=1#usize,«end»:=2#usize},factors20)
  | _ => ({start:=2#usize,«end»:=2#usize},factors25)
theorem secondLoop : weights_new_loop1 {start:=0#usize,«end»:=2#usize} z factors15=ok factors25 := by
  unfold weights_new_loop1
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop1.body z iter factors)
    secondStates 2 factors25
  · intro i hi
    interval_cases i
    · exact second0
    · exact second1
  · rfl
#print axioms secondLoop
end AspisR1.JGo_TX2_WeightConstruct
end
