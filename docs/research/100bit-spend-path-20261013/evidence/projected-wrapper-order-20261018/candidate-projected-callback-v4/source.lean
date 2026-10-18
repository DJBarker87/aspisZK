import PoseidonProjectedClosure2Source
import AspisR1.PoseidonClosure2ArrayExact
import PoseidonPreparedSum3Source

/- Candidate projected evaluator callback source cut.
   Candidate Rust SHA 82d54bbade8d81899c64ede23befce8b240b881d61b144e769c0d0e16ab5cff9;
   generated Funs SHA f1e258056294e84777f56f2a1ea3572329eca52b4bb553bfc6c58027bef1604c,
   callback body lines 1055-1085. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedCallbackSource
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1PoseidonProjectedClosure2Source

abbrev QM := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CandidateClosure :=
  state_only_poseidon.StateOnlyPoseidonOpenings × Array QM 16#usize ×
  Prepared × Array Prepared 3#usize × Array QM 4#usize × Array QM 4#usize

def candidate_call_mut (c : CandidateClosure) (tupled_args : Usize) :
    Result (QM × CandidateClosure) := do
  let (sopo, a, pqm, a1, a2, a3) := c
  let start ← 4#usize * tupled_args
  let i ← start + 4#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) sopo.succ_z
      { start, «end» := i }
  let target ← field.qm31_pack_base4 s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) a
      { start, «end» := i }
  let internal ← field.qm31_pack_base4 s1
  let q ← Array.index_usize a2 tupled_args
  let q1 ← field.QM31.sub target q
  let q2 ← Array.index_usize a3 tupled_args
  let q3 ← field.QM31.sub target q2
  let q4 ← field.QM31.sub target internal
  let q5 ← AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared a1
    (Array.make 3#usize [ q1, q3, q4 ])
  let q6 ← field.PreparedQm31Multiplier.mul pqm q5
  ok (q6, c)

abbrev CandidateCallback :=
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31

def candidate_callback : core.ops.function.FnMut CandidateClosure Usize QM := {
  FnOnceInst := state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnOnceTupleUsizeQM31
  call_mut := candidate_call_mut
}

def candidate_array (c : CandidateClosure) : Result (Array QM 4#usize) :=
  array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy candidate_callback
    field.QM31.ZERO c

theorem candidate_call_matches_closure2 (c : CandidateClosure) (i : Usize) :
    candidate_call_mut c i =
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut c i := by
  rfl

theorem candidate_callback_matches_closure2 :
    candidate_callback = AspisR1.PoseidonClosure2ArrayExact.Callback := by
  rfl

#print axioms candidate_call_matches_closure2
#print axioms candidate_callback_matches_closure2

end AspisR1.PoseidonCandidateProjectedCallbackSource
