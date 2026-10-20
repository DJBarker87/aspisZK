import Aeneas
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.FunsExternal
import TerminalV4CompositionPartsCallerChunk07dV2
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1SelectedMaskProbe
abbrev TerminalPartsCompositionCaller :=
  pool_v1.pair_forest_semantic_terminal.SemanticPublic →
  Array field.QM31 84#usize → Array field.QM31 10#usize →
  field.QM31 → field.QM31 → field.QM31 →
  Result (core.result.Result
    (field.QM31 × (Array field.QM31 16#usize) ×
      (Array field.QM31 10#usize) × field.QM31 × field.QM31 × field.QM31)
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::{impl core::ops::function::Fn<(aspis_r1_mask_extraction_probe::field::QM31, aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::closure}::call]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1216:17-1219:5 -/
def
  pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
  (c : pool_v1.pair_forest_semantic_terminal.equality_value.closure)
  (tupled_args : (field.QM31 × field.QM31)) :
  Result field.QM31
  := do
  let (a, b) := tupled_args
  let ab ← field.QM31.mul a b
  let q ← field.QM31.sub field.QM31.ONE a
  let q1 ← field.QM31.sub q b
  let q2 ← field.QM31.add q1 ab
  field.QM31.add q2 ab

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1222:4-1225:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.equality_value_loop
  (left : Array field.QM31 10#usize) (right : Array field.QM31 10#usize)
  (product : field.QM31) (index : Std.Usize) :
  Result field.QM31
  := do
  let s ← lift (Array.to_slice left)
  let i := Slice.len s
  if index < i
  then
    let q ← Array.index_usize left index
    let q1 ← Array.index_usize right index
    let q2 ←
      pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
        () (q, q1)
    let product1 ← field.QM31.mul product q2
    let index1 ← index + 1#usize
    pool_v1.pair_forest_semantic_terminal.equality_value_loop left right
      product1 index1
  else ok product
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1215:0-1227:1 -/
def pool_v1.pair_forest_semantic_terminal.equality_value
  (left : Array field.QM31 10#usize) (right : Array field.QM31 10#usize) :
  Result field.QM31
  := do
  let q ← Array.index_usize left 0#usize
  let q1 ← Array.index_usize right 0#usize
  let product ←
    pool_v1.pair_forest_semantic_terminal.equality_value.closure.Insts.CoreOpsFunctionFnPairQM31QM31QM31.call
      () (q, q1)
  pool_v1.pair_forest_semantic_terminal.equality_value_loop left right product
    1#usize
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::terminal_parts]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1300:0-1325:1 -/
def pool_v1.pair_forest_semantic_terminal.terminal_parts_with_caller
  (compositionCaller : TerminalPartsCompositionCaller)
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (claims : Array field.QM31 84#usize) (point : Array field.QM31 10#usize)
  (lambda : field.QM31) (chi : field.QM31) (theta : field.QM31)
  (zerocheck_point : Array field.QM31 10#usize) (mu : field.QM31) :
  Result (core.result.Result (field.QM31 × (Array field.QM31 16#usize) ×
    (Array field.QM31 10#usize) × field.QM31)
    pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
  := do
  let r ←
    compositionCaller public1 claims point lambda chi theta
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let (composition, c1, mask_only, g, h1_z, copy_active) := val
    let q ←
      pool_v1.pair_forest_semantic_terminal.equality_value zerocheck_point
        point
    let q1 ← field.QM31.mul q composition
    let q2 ← field.QM31.mul mu h1_z
    let q3 ← field.QM31.add q1 q2
    let q4 ← field.QM31.mul mu mu
    let q5 ← field.QM31.sub field.QM31.ONE copy_active
    let q6 ← field.QM31.mul q5 h1_z
    let q7 ← field.QM31.mul q4 q6
    let original ← field.QM31.add q3 q7
    ok (core.result.Result.Ok (original, c1, mask_only, g))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (field.QM31 × (Array field.QM31 16#usize) × (Array field.QM31 10#usize)
      × field.QM31) (core.convert.FromSame
      pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1)
      residual
end AspisR1SelectedMaskProbe
