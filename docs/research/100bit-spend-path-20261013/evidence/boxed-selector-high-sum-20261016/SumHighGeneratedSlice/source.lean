import SumHighStdModels

/-! Exact shared source high-selector summation loops and wrapper, retained
byte-for-byte from the sealed generated candidate and isolated by namespace. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1SumHighCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 160:8-162:9 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0
  (iter : core.ops.range.Range Std.Usize)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (sum : field.QM31)
  :
  Result (pool_v1.pair_forest_copy_terminal.Selectors × field.QM31)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (selectors, sum)
  | some block =>
    let q ← Array.index_usize selectors.high block
    let sum1 ← field.QM31.add sum q
    pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0 iter1 selectors
      sum1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 159:4-163:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.sum_high_loop0
  (iter : core.slice.iter.Iter (core.ops.range.Range Std.Usize))
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (sum : field.QM31)
  :
  Result field.QM31
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok sum
  | some range =>
    let iter2 ←
      core.ops.range.Range.Insts.CoreCloneClone.clone core.clone.CloneUsize
        range
    let (selectors1, sum1) ←
      pool_v1.pair_forest_semantic_terminal.sum_high_loop0_loop0 iter2
        selectors sum
    pool_v1.pair_forest_semantic_terminal.sum_high_loop0 iter1 selectors1 sum1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 157:0-165:1 -/
def pool_v1.pair_forest_semantic_terminal.sum_high
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
  (ranges : Slice (core.ops.range.Range Std.Usize)) :
  Result field.QM31
  := do
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      ranges
  pool_v1.pair_forest_semantic_terminal.sum_high_loop0 iter selectors
    field.QM31.ZERO

end AspisR1SumHighCandidate
