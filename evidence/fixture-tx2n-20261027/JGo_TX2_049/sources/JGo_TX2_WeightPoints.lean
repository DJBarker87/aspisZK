import JGo_TX2_WeightPoints0
import JGo_TX2_WeightPoints1
import JGo_TX2_WeightPoints2
import JGo_TX2_WeightPoints3
import JGo_TX2_WeightPoints4
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_WeightPoints
open Aeneas Aeneas.Std Result ControlFlow FIn_WeightsExtract JGo_TX2_WeightData
abbrev State := core.iter.adapters.rev.Rev (core.ops.range.Range Usize) × Array Q 10#usize × Q

def states : Nat → State
  | 0 => (⟨{start:=0#usize,«end»:=10#usize}⟩,successor00,carry00)
  | 1 => (⟨{start:=0#usize,«end»:=9#usize}⟩,successor01,carry01)
  | 2 => (⟨{start:=0#usize,«end»:=8#usize}⟩,successor02,carry02)
  | 3 => (⟨{start:=0#usize,«end»:=7#usize}⟩,successor03,carry03)
  | 4 => (⟨{start:=0#usize,«end»:=6#usize}⟩,successor04,carry04)
  | 5 => (⟨{start:=0#usize,«end»:=5#usize}⟩,successor05,carry05)
  | 6 => (⟨{start:=0#usize,«end»:=4#usize}⟩,successor06,carry06)
  | 7 => (⟨{start:=0#usize,«end»:=3#usize}⟩,successor07,carry07)
  | 8 => (⟨{start:=0#usize,«end»:=2#usize}⟩,successor08,carry08)
  | 9 => (⟨{start:=0#usize,«end»:=1#usize}⟩,successor09,carry09)
  | _ => (⟨{start:=0#usize,«end»:=0#usize}⟩,successor10,carry10)

theorem loop : state_only_prefix.state_only_statement_points_loop
    ⟨{start:=0#usize,«end»:=10#usize}⟩ alpha alpha field.QM31.ONE=ok successor10 := by
  unfold state_only_prefix.state_only_statement_points_loop
  apply JGo_TX2_LoopChain.source
    (fun s : State=>state_only_prefix.state_only_statement_points_loop.body alpha s.1 s.2.1 s.2.2)
    states 10 successor10
  · intro i hi
    interval_cases i
    · exact JGo_TX2_WeightPoints0.step00
    · exact JGo_TX2_WeightPoints0.step01
    · exact JGo_TX2_WeightPoints1.step02
    · exact JGo_TX2_WeightPoints1.step03
    · exact JGo_TX2_WeightPoints2.step04
    · exact JGo_TX2_WeightPoints2.step05
    · exact JGo_TX2_WeightPoints3.step06
    · exact JGo_TX2_WeightPoints3.step07
    · exact JGo_TX2_WeightPoints4.step08
    · exact JGo_TX2_WeightPoints4.step09
  · rfl
#print axioms loop

theorem source : state_only_prefix.r0.statement_points alpha=ok points := by
  unfold state_only_prefix.r0.statement_points state_only_prefix.state_only_statement_points
  change (do
    let successor ← state_only_prefix.state_only_statement_points_loop
      ⟨{start:=0#usize,«end»:=10#usize}⟩ alpha alpha field.QM31.ONE
    let a ← field.QM31.sub field.QM31.ONE (alpha.val[7])
    let absorption ← Array.update alpha 7#usize a
    let b ← Array.index_usize absorption 6#usize
    let c ← field.QM31.sub field.QM31.ONE b
    let absorption1 ← Array.update absorption 6#usize c
    ok (Array.make 3#usize [alpha,successor,absorption1]))=ok points
  rw [loop,bind_tc_ok]
  with_unfolding_all rfl
#print axioms source
end AspisR1.JGo_TX2_WeightPoints
end
