import JGo_TX2_WeightRows
import JGo_TX2_WeightPoints
import JGo_TX2_Range
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightConstruct
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
abbrev Range := core.ops.range.Range Usize
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
def seeded0 (q : Q) : Factors := Array.make 5#usize [r0_5,r1_5,r2_5,(Array.make 5#usize [Array.make 4#usize [field.QM31.ONE,z0y,z0x,q],Array.repeat 4#usize field.QM31.ZERO,Array.repeat 4#usize field.QM31.ZERO,Array.repeat 4#usize field.QM31.ZERO,Array.repeat 4#usize field.QM31.ZERO]),r4_0]
theorem second0 : weights_new_loop1.body z {start:=0#usize,«end»:=2#usize} factors15=
    ok (ControlFlow.cont ({start:=1#usize,«end»:=2#usize},factors20)) := by
  have index : Usize.wrapping_add 3#usize 0#usize=3#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 0#usize (by decide))
  unfold weights_new_loop1.body
  rw [JGo_TX2_Range.next 0#usize 2#usize 1#usize (by decide) (by decide)]
  simp only [lift,bind_tc_ok,index,Aeneas.Std.uncurry]
  change (do
    let q ← field.QM31.mul z0x z0y
    let x ← double z0x
    let out ← weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} (seeded0 q) 0#usize x
    ok (ControlFlow.cont ({start:=1#usize,«end»:=2#usize},out) : ControlFlow (Range × Factors) Factors))=_
  rw [JGo_TX2_WeightRow3.product,bind_tc_ok,JGo_TX2_WeightRow3.double,bind_tc_ok]
  change (do
    let out ← weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} factors16 0#usize x0_1
    ok (ControlFlow.cont ({start:=1#usize,«end»:=2#usize},out) : ControlFlow (Range × Factors) Factors))=_
  rw [JGo_TX2_WeightRows.inner3,bind_tc_ok]
#print axioms second0
def seeded1 (q : Q) : Factors := Array.make 5#usize [r0_5,r1_5,r2_5,r3_5,(Array.make 5#usize [Array.make 4#usize [field.QM31.ONE,z1y,z1x,q],Array.repeat 4#usize field.QM31.ZERO,Array.repeat 4#usize field.QM31.ZERO,Array.repeat 4#usize field.QM31.ZERO,Array.repeat 4#usize field.QM31.ZERO])]
theorem second1 : weights_new_loop1.body z {start:=1#usize,«end»:=2#usize} factors20=
    ok (ControlFlow.cont ({start:=2#usize,«end»:=2#usize},factors25)) := by
  have index : Usize.wrapping_add 3#usize 1#usize=4#usize :=
    UScalar.eq_of_val_eq (Port3_Wrapping.wrap_add_value 3#usize 1#usize (by decide))
  unfold weights_new_loop1.body
  rw [JGo_TX2_Range.next 1#usize 2#usize 2#usize (by decide) (by decide)]
  simp only [lift,bind_tc_ok,index,Aeneas.Std.uncurry]
  change (do
    let q ← field.QM31.mul z1x z1y
    let x ← double z1x
    let out ← weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} (seeded1 q) 1#usize x
    ok (ControlFlow.cont ({start:=2#usize,«end»:=2#usize},out) : ControlFlow (Range × Factors) Factors))=_
  rw [JGo_TX2_WeightRow4.product,bind_tc_ok,JGo_TX2_WeightRow4.double,bind_tc_ok]
  change (do
    let out ← weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} factors21 1#usize x1_1
    ok (ControlFlow.cont ({start:=2#usize,«end»:=2#usize},out) : ControlFlow (Range × Factors) Factors))=_
  rw [JGo_TX2_WeightRows.inner4,bind_tc_ok]
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
