-- Generated source slice: declarations copied byte-for-byte from pinned G blocks.
import Aeneas.Std
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2071:48-2071:74 -/
@[reducible]
def pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure :=
  Array (Array field.QM31 29#usize) 3#usize
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::{impl core::ops::function::FnMut<(usize,), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::r0::Public<'a>}::terminal_qm31::closure<'a, '_1>}::call_mut]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 2071:48-2071:74 -/
def
  pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
  (c : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  (tupled_args : Std.Usize) :
  Result (field.QM31 ×
    pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure)
  := do
  let i ← tupled_args / 28#usize
  let i1 ← tupled_args % 28#usize
  let a ← Array.index_usize c i
  let q ← Array.index_usize a i1
  ok (q, c)
/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 29:0-29:65
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
  : Std.Usize :=
  16#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 31:0-32:92
    Visibility: public -/
@[global_simps, irreducible]
def
  pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
  : Result Std.Usize := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1
      + state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
  i + 2#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::selected_claim]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1185:0-1191:1 -/
def pool_v1.pair_forest_semantic_terminal.selected_claim
  (claims : Array field.QM31 84#usize) (point : Std.Usize) (column : Std.Usize)
  :
  Result field.QM31
  := do
  let i ←
    pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1
  let i1 ← point * i
  let i2 ← i1 + column
  Array.index_usize claims i2
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

end AspisR1SelectedMaskProbe
