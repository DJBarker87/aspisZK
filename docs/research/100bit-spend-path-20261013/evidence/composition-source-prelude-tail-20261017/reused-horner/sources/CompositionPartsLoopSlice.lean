-- Mechanical exact-source slice; declaration blocks are copied verbatim from the pinned candidate Funs.lean.
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1269:4-1271:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.composition_parts_loop0
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (semantic : Array field.QM31 24#usize)
  (prepared_theta : field.PreparedQm31Multiplier) (composition : field.QM31) :
  Result field.QM31
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok composition
  | some index =>
    let q ← field.PreparedQm31Multiplier.mul prepared_theta composition
    let q1 ← Array.index_usize semantic index
    let composition1 ← field.QM31.add q q1
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iter1
      semantic prepared_theta composition1
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::composition_parts]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1272:4-1274:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.composition_parts_loop1
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (poseidon : Array field.QM31 4#usize)
  (prepared_theta : field.PreparedQm31Multiplier) (composition : field.QM31) :
  Result field.QM31
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok composition
  | some index =>
    let q ← field.PreparedQm31Multiplier.mul prepared_theta composition
    let q1 ← Array.index_usize poseidon index
    let composition1 ← field.QM31.add q q1
    pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iter1
      poseidon prepared_theta composition1
partial_fixpoint

end AspisR1SelectedMaskProbe
