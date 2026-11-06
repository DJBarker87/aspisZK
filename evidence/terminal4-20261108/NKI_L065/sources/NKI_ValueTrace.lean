import NKI_ValueTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueTrace
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_ValuePrefix (Openings Selectors Tail)
structure Locals where
 value_selectors : Array NQ 3#usize
 q : NQ
 q1 : NQ
 q2 : NQ
 q3 : NQ
 q4 : NQ
 range_selector : NQ
 openings1 : Openings
 range1 : Array NQ 33#usize
 openings2 : Openings
 range2 : Array NQ 33#usize
 openings3 : Openings
 range3 : Array NQ 33#usize
 q5 : NQ
 q6 : NQ
 i : U32
 q7 : NQ
 q8 : NQ
 q9 : NQ
 i1 : U32
 q10 : NQ
 reconstructed : NQ
 q11 : NQ
 q12 : NQ
 range4 : Array NQ 33#usize
 q13 : NQ
 range5 : Array NQ 33#usize
 q14 : NQ
 range6 : Array NQ 33#usize
def run (openings : Openings) (selectors : Selectors) : Result Locals := do

  let value_selectors ←
    FIq_Native.core.array.Array.map
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      (Array.make 3#usize [ 0#usize, 2#usize, 4#usize ]) selectors
  let q ← Array.index_usize value_selectors 0#usize
  let q1 ← field.QM31.add field.QM31.ZERO q
  let q2 ← Array.index_usize value_selectors 1#usize
  let q3 ← field.QM31.add q1 q2
  let q4 ← Array.index_usize value_selectors 2#usize
  let range_selector ← field.QM31.add q3 q4
  let range := Array.repeat 33#usize field.QM31.ZERO
  let (openings1, range1) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range
      0#usize
  let (openings2, range2) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings1
      range1 0#usize
  let (openings3, range3) ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings2
      range2 0#usize
  let q5 ← pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.z
  let q6 ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.succ_z
  let i ← 1#u32 <<< 10#i32
  let q7 ← field.QM31.mul_m31 q6 i
  let q8 ← field.QM31.add q5 q7
  let q9 ←
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.xor12_z
  let i1 ← 1#u32 <<< 20#i32
  let q10 ← field.QM31.mul_m31 q9 i1
  let reconstructed ← field.QM31.add q8 q10
  let q11 ← Array.index_usize openings3.z 10#usize
  let q12 ← field.QM31.sub q11 reconstructed
  let range4 ← Array.update range3 30#usize q12
  let q13 ← Array.index_usize openings3.succ_z 10#usize
  let range5 ← Array.update range4 31#usize q13
  let q14 ← Array.index_usize openings3.xor12_z 10#usize
  let range6 ← Array.update range5 32#usize q14
  ok ⟨value_selectors,q,q1,q2,q3,q4,range_selector,openings1,range1,openings2,range2,openings3,range3,q5,q6,i,q7,q8,q9,i1,q10,reconstructed,q11,q12,range4,q13,range5,q14,range6⟩
def Canonical (o : Openings) (l : Locals) : Prop :=
 canonical l.value_selectors ∧
 Canon l.q ∧
 Canon l.q1 ∧
 Canon l.q2 ∧
 Canon l.q3 ∧
 Canon l.q4 ∧
 Canon l.range_selector ∧
 l.openings1=o ∧
 canonical l.range1 ∧
 l.openings2=o ∧
 canonical l.range2 ∧
 l.openings3=o ∧
 canonical l.range3 ∧
 Canon l.q5 ∧
 Canon l.q6 ∧
 Canon l.q7 ∧
 Canon l.q8 ∧
 Canon l.q9 ∧
 Canon l.q10 ∧
 Canon l.reconstructed ∧
 Canon l.q11 ∧
 Canon l.q12 ∧
 canonical l.range4 ∧
 Canon l.q13 ∧
 canonical l.range5 ∧
 Canon l.q14 ∧
 canonical l.range6
def output (l : Locals) : Tail := ⟨l.openings3,l.range_selector,l.range6⟩
def Clauses (openings : Openings) (selectors : Selectors) (l : Locals) : Prop :=
 let value_selectors:=l.value_selectors
 let q:=l.q
 let q1:=l.q1
 let q2:=l.q2
 let q3:=l.q3
 let q4:=l.q4
 let range_selector:=l.range_selector
 let openings1:=l.openings1
 let range1:=l.range1
 let openings2:=l.openings2
 let range2:=l.range2
 let openings3:=l.openings3
 let range3:=l.range3
 let q5:=l.q5
 let q6:=l.q6
 let i:=l.i
 let q7:=l.q7
 let q8:=l.q8
 let q9:=l.q9
 let i1:=l.i1
 let q10:=l.q10
 let reconstructed:=l.reconstructed
 let q11:=l.q11
 let q12:=l.q12
 let range4:=l.range4
 let q13:=l.q13
 let range5:=l.range5
 let q14:=l.q14
 let range6:=l.range6
 let range:=Array.repeat 33#usize field.QM31.ZERO
 (FIq_Native.core.array.Array.map
      pool_v1.pair_forest_semantic_terminal.add_value_lanes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
      (Array.make 3#usize [ 0#usize, 2#usize, 4#usize ]) selectors=ok value_selectors) ∧
 (Array.index_usize value_selectors 0#usize=ok q) ∧
 (field.QM31.add field.QM31.ZERO q=ok q1) ∧
 (Array.index_usize value_selectors 1#usize=ok q2) ∧
 (field.QM31.add q1 q2=ok q3) ∧
 (Array.index_usize value_selectors 2#usize=ok q4) ∧
 (field.QM31.add q3 q4=ok range_selector) ∧
 (pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0 openings range
      0#usize=ok (openings1, range1)) ∧
 (pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop1 openings1
      range1 0#usize=ok (openings2, range2)) ∧
 (pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop2 openings2
      range2 0#usize=ok (openings3, range3)) ∧
 (pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.z=ok q5) ∧
 (pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.succ_z=ok q6) ∧
 (1#u32 <<< 10#i32=ok i) ∧
 (field.QM31.mul_m31 q6 i=ok q7) ∧
 (field.QM31.add q5 q7=ok q8) ∧
 (pool_v1.pair_forest_semantic_terminal.reconstruct_10 openings3.xor12_z=ok q9) ∧
 (1#u32 <<< 20#i32=ok i1) ∧
 (field.QM31.mul_m31 q9 i1=ok q10) ∧
 (field.QM31.add q8 q10=ok reconstructed) ∧
 (Array.index_usize openings3.z 10#usize=ok q11) ∧
 (field.QM31.sub q11 reconstructed=ok q12) ∧
 (Array.update range3 30#usize q12=ok range4) ∧
 (Array.index_usize openings3.succ_z 10#usize=ok q13) ∧
 (Array.update range4 31#usize q13=ok range5) ∧
 (Array.index_usize openings3.xor12_z 10#usize=ok q14) ∧
 (Array.update range5 32#usize q14=ok range6)
theorem source (o : Openings) (s : Selectors)
 (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hh : canonical s.high) (hl : canonical s.low) : run o s ⦃ l=>Canonical o l ⦄ := by
 have zero:=FIv_NativeValue.zero.1
 have zeros:=JFy_ZeroArrays.source 33#usize
 unfold run
 step*
 all_goals first | assumption | scalar_tac | (subst_vars;unfold Canonical;exact ⟨by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl,by first|assumption|rfl⟩)
#print axioms source
end AspisR1.NKI_ValueTrace
end
