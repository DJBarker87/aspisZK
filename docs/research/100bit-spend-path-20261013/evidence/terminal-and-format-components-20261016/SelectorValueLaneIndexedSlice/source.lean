import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import SelectorSourceSlice
/- The following declaration bodies are byte-preserved slices from the
v3 generated candidate Funs source. Only the enclosing namespace is isolated
so the new indexed implementations can coexist with the old iterator-based
proof modules. Source SHA is recorded in the companion manifest. -/
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section
namespace AspisR1SelectedMaskProbeIndexed
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 171:4-174:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop
  (view : Array field.QM31 16#usize) (acc : field.QM31) (i : Std.Usize) :
  Result field.QM31
  := do
  if i > 0#usize
  then
    let i1 ← i - 1#usize
    let q ← field.QM31.add acc acc
    let q1 ← Array.index_usize view i1
    let acc1 ← field.QM31.add q q1
    pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop view acc1 i1
  else ok acc
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::reconstruct_10]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 168:0-176:1 -/
def pool_v1.pair_forest_semantic_terminal.reconstruct_10
  (view : Array field.QM31 16#usize) : Result field.QM31 := do
  let acc ← Array.index_usize view 9#usize
  pool_v1.pair_forest_semantic_terminal.reconstruct_10_loop view acc 9#usize


/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_value_lanes]: loop 3:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 509:8-512:9 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3
  (range_selector : field.QM31) (range : Array field.QM31 33#usize)
  (residual_index : Std.Usize) :
  Result (Array field.QM31 33#usize)
  := do
  if residual_index < 33#usize
  then
    let q ← Array.index_usize range residual_index
    let q1 ← field.QM31.mul range_selector q
    let a ← Array.update range residual_index q1
    let residual_index1 ← residual_index + 1#usize
    pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop3 range_selector
      a residual_index1
  else ok range
partial_fixpoint

end AspisR1SelectedMaskProbeIndexed
