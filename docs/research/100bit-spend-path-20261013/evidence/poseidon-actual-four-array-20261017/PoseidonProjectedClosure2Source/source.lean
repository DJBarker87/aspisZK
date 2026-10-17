import AspisR1SelectedMaskProbe.Funs
import AspisR1SelectedMaskProbe.Types
import SelectorValueLaneLoops012Slice
import EqualityValueSlice
import ExtractedMaskQmPackBase4Whole
import ExtractedMaskPreparedState
import PoseidonPreparedSum3Source

/- Exact current candidate closure#2 call_mut body from Funs SHA 04fc...,
   with only its missing qmsum3 dependency explicitly mapped to its isolated
   exact source owner. The projected outer evaluator is a later target. -/
set_option autoImplicit false
namespace AspisR1PoseidonProjectedClosure2Source
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2 :=
  state_only_poseidon.StateOnlyPoseidonOpenings × Array field.QM31 16#usize ×
  field.PreparedQm31Multiplier × Array field.PreparedQm31Multiplier 3#usize ×
  Array field.QM31 4#usize × Array field.QM31 4#usize

def state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  (tupled_args : Std.Usize) :
  Result (field.QM31 × state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2)
  := do
  let (sopo, a, pqm, a1, a2, a3) := c
  let start ← 4#usize * tupled_args
  let i ← start + 4#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice field.QM31)) sopo.succ_z
      { start, «end» := i }
  let target ← field.qm31_pack_base4 s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice field.QM31)) a
      { start, «end» := i }
  let internal ← field.qm31_pack_base4 s1
  let q ← Array.index_usize a2 tupled_args
  let q1 ← field.QM31.sub target q
  let q2 ← Array.index_usize a3 tupled_args
  let q3 ← field.QM31.sub target q2
  let q4 ← field.QM31.sub target internal
  let q5 ←
    AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared a1 (Array.make 3#usize [ q1, q3, q4 ])
  let q6 ← field.PreparedQm31Multiplier.mul pqm q5
  ok (q6, c)

end AspisR1PoseidonProjectedClosure2Source
