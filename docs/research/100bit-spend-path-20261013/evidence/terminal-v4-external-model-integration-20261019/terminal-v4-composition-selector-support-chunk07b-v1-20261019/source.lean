import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionGatherClosuresChunk07aV2
import TerminalV4ValidateTransitionPredecessorV4
import TerminalV4EvalSelectorsChunk01
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::sum_high]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 174:8-176:9 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 173:4-177:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 171:0-179:1 -/
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
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::poseidon_selectors]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 225:0-230:1 -/
def pool_v1.pair_forest_semantic_terminal.poseidon_selectors
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result state_only_poseidon.StateOnlyPoseidonSelectors
  := do
  let s ←
    lift (Array.to_slice
      (Array.make 1#usize [
        ({ start := 0#usize, «end» := 57#usize } : core.ops.range.Range
        Std.Usize)
        ]))
  let q ← pool_v1.pair_forest_semantic_terminal.sum_high selectors s
  ok { block := q, «local» := selectors.low }
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::SELECTED_H1_COLUMN]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 56:0-57:88 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
  : Result Std.Usize :=
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
    + state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::SELECTED_G_COLUMN]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 58:0-58:56 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.SELECTED_G_COLUMN
  : Result Std.Usize := do
  let i ← pool_v1.pair_forest_semantic_terminal.SELECTED_H1_COLUMN
  i + 1#usize
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::expand]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 150:12-155:13 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0
  {N : Std.Usize}
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (weights : Array field.QM31 N) (prepared : field.PreparedQm31Multiplier) :
  Result (Array field.QM31 N)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok weights
  | some index =>
    let parent ← Array.index_usize weights index
    let right ← field.PreparedQm31Multiplier.mul prepared parent
    let q ← field.QM31.sub parent right
    let i ← 2#usize * index
    let weights1 ← Array.update weights i q
    let i1 ← i + 1#usize
    let a ← Array.update weights1 i1 right
    pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter1 a
      prepared
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::expand]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 148:8-157:9 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0
  {N : Std.Usize} (iter : core.slice.iter.Iter field.QM31)
  (weights : Array field.QM31 N) (len : Std.Usize) :
  Result (Array field.QM31 N)
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok weights
  | some coordinate =>
    let prepared ← field.PreparedQm31Multiplier.new coordinate
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
        (core.ops.range.Range.Insts.DoubleEndedIterator
        core.iter.range.StepUsize) { start := 0#usize, «end» := len }
    let weights1 ←
      pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0_loop0 iter2
        weights prepared
    let len1 ← len * 2#usize
    pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 iter1 weights1
      len1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::expand]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 144:4-159:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.expand
  (N : Std.Usize) (coordinates : Slice field.QM31) :
  Result (Array field.QM31 N)
  := do
  let weights := Array.repeat N field.QM31.ZERO
  let a ← Array.update weights 0#usize field.QM31.ONE
  let iter ←
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
      coordinates
  pool_v1.pair_forest_copy_terminal.Selectors.expand_loop0 iter a 1#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::at_point]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 161:4-166:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.at_point
  (point : Array field.QM31 10#usize) :
  Result pool_v1.pair_forest_copy_terminal.Selectors
  := do
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31)) point
      { «end» := 6#usize }
  let a ← pool_v1.pair_forest_copy_terminal.Selectors.expand 64#usize s
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice field.QM31)) point
      { start := 6#usize }
  let a1 ← pool_v1.pair_forest_copy_terminal.Selectors.expand 16#usize s1
  ok { high := a, low := a1 }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::boxed_at_point]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 169:4-171:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point
  (point : Array field.QM31 10#usize) :
  Result pool_v1.pair_forest_copy_terminal.Selectors
  := do
  pool_v1.pair_forest_copy_terminal.Selectors.at_point point
end AspisR1SelectedMaskProbe
