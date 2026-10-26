import PreweightedClosureSlice
import Qm31PackBase4Slice
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace AspisR1PreweightedCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 113:4-123:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_preweighted_loop
  {N : Std.Usize} (iter : core.ops.range.RangeInclusive Std.Usize)
  (packed : Array field.QM31 24#usize) (start : Std.Usize)
  (values : Array field.QM31 N) :
  Result (Array field.QM31 24#usize)
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => ok packed
  | some group =>
    let lanes ←
      array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
        (pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        N) field.QM31.ZERO (group, start, values)
    let q ← Array.index_usize packed group
    let s ← lift (Array.to_slice lanes)
    let q1 ← field.qm31_pack_base4 s
    let q2 ← field.QM31.add q q1
    let a ← Array.update packed group q2
    pool_v1.pair_forest_semantic_terminal.add_preweighted_loop iter1 a start
      values
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_preweighted]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 106:0-124:1 -/
def pool_v1.pair_forest_semantic_terminal.add_preweighted
  {N : Std.Usize} (packed : Array field.QM31 24#usize) (start : Std.Usize)
  (values : Array field.QM31 N) :
  Result (Array field.QM31 24#usize)
  := do
  let first ← start / 4#usize
  let i ← start + N
  let i1 ← i - 1#usize
  let last ← i1 / 4#usize
  let iter ← core.ops.range.RangeInclusive.new first last
  pool_v1.pair_forest_semantic_terminal.add_preweighted_loop iter packed start
    values


end AspisR1PreweightedCandidate
