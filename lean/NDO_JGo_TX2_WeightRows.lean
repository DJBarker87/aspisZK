import NDO_JGo_TX2_WeightRow0
import NDO_JGo_TX2_WeightRow1
import NDO_JGo_TX2_WeightRow2
import NDO_JGo_TX2_WeightRow3
import NDO_JGo_TX2_WeightRow4
import JGo_TX2_LoopChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightRows
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
abbrev Range := core.ops.range.Range Usize
def states0 : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=5#usize},factors00)
  | 1 => ({start:=1#usize,«end»:=5#usize},factors01)
  | 2 => ({start:=2#usize,«end»:=5#usize},factors02)
  | 3 => ({start:=3#usize,«end»:=5#usize},factors03)
  | 4 => ({start:=4#usize,«end»:=5#usize},factors04)
  | _ => ({start:=5#usize,«end»:=5#usize},factors05)
theorem inner0 : weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize} points factors00 0#usize=ok factors05 := by
  unfold weights_new_loop0_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop0_loop0.body points 0#usize iter factors) states0 5 factors05
  · intro i hi
    interval_cases i
    · exact JGo_TX2_WeightRow0.step0
    · exact JGo_TX2_WeightRow0.step1
    · exact JGo_TX2_WeightRow0.step2
    · exact JGo_TX2_WeightRow0.step3
    · exact JGo_TX2_WeightRow0.step4
  · rfl
#print axioms inner0
def states1 : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=5#usize},factors05)
  | 1 => ({start:=1#usize,«end»:=5#usize},factors06)
  | 2 => ({start:=2#usize,«end»:=5#usize},factors07)
  | 3 => ({start:=3#usize,«end»:=5#usize},factors08)
  | 4 => ({start:=4#usize,«end»:=5#usize},factors09)
  | _ => ({start:=5#usize,«end»:=5#usize},factors10)
theorem inner1 : weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize} points factors05 1#usize=ok factors10 := by
  unfold weights_new_loop0_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop0_loop0.body points 1#usize iter factors) states1 5 factors10
  · intro i hi
    interval_cases i
    · exact JGo_TX2_WeightRow1.step0
    · exact JGo_TX2_WeightRow1.step1
    · exact JGo_TX2_WeightRow1.step2
    · exact JGo_TX2_WeightRow1.step3
    · exact JGo_TX2_WeightRow1.step4
  · rfl
#print axioms inner1
def states2 : Nat → Range × Factors
  | 0 => ({start:=0#usize,«end»:=5#usize},factors10)
  | 1 => ({start:=1#usize,«end»:=5#usize},factors11)
  | 2 => ({start:=2#usize,«end»:=5#usize},factors12)
  | 3 => ({start:=3#usize,«end»:=5#usize},factors13)
  | 4 => ({start:=4#usize,«end»:=5#usize},factors14)
  | _ => ({start:=5#usize,«end»:=5#usize},factors15)
theorem inner2 : weights_new_loop0_loop0 {start:=0#usize,«end»:=5#usize} points factors10 2#usize=ok factors15 := by
  unfold weights_new_loop0_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors=>match s with | (iter,factors)=>weights_new_loop0_loop0.body points 2#usize iter factors) states2 5 factors15
  · intro i hi
    interval_cases i
    · exact JGo_TX2_WeightRow2.step0
    · exact JGo_TX2_WeightRow2.step1
    · exact JGo_TX2_WeightRow2.step2
    · exact JGo_TX2_WeightRow2.step3
    · exact JGo_TX2_WeightRow2.step4
  · rfl
#print axioms inner2
def states3 : Nat → Range × Factors × Q
  | 0 => ({start:=1#usize,«end»:=5#usize},factors16,x0_1)
  | 1 => ({start:=2#usize,«end»:=5#usize},factors17,x0_2)
  | 2 => ({start:=3#usize,«end»:=5#usize},factors18,x0_3)
  | 3 => ({start:=4#usize,«end»:=5#usize},factors19,x0_4)
  | _ => ({start:=5#usize,«end»:=5#usize},factors20,x0_5)
theorem inner3 : weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} factors16 0#usize x0_1=ok factors20 := by
  unfold weights_new_loop1_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors × Q=>match s with | (iter,factors,x)=>weights_new_loop1_loop0.body 0#usize iter factors x) states3 4 factors20
  · intro i hi
    interval_cases i
    · exact JGo_TX2_WeightRow3.step1
    · exact JGo_TX2_WeightRow3.step2
    · exact JGo_TX2_WeightRow3.step3
    · exact JGo_TX2_WeightRow3.step4
  · rfl
#print axioms inner3
def states4 : Nat → Range × Factors × Q
  | 0 => ({start:=1#usize,«end»:=5#usize},factors21,x1_1)
  | 1 => ({start:=2#usize,«end»:=5#usize},factors22,x1_2)
  | 2 => ({start:=3#usize,«end»:=5#usize},factors23,x1_3)
  | 3 => ({start:=4#usize,«end»:=5#usize},factors24,x1_4)
  | _ => ({start:=5#usize,«end»:=5#usize},factors25,x1_5)
theorem inner4 : weights_new_loop1_loop0 {start:=1#usize,«end»:=5#usize} factors21 1#usize x1_1=ok factors25 := by
  unfold weights_new_loop1_loop0
  apply JGo_TX2_LoopChain.source (fun s : Range × Factors × Q=>match s with | (iter,factors,x)=>weights_new_loop1_loop0.body 1#usize iter factors x) states4 4 factors25
  · intro i hi
    interval_cases i
    · exact JGo_TX2_WeightRow4.step1
    · exact JGo_TX2_WeightRow4.step2
    · exact JGo_TX2_WeightRow4.step3
    · exact JGo_TX2_WeightRow4.step4
  · rfl
#print axioms inner4
end AspisR1.JGo_TX2_WeightRows
end
