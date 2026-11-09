-- Deterministic generated declaration slice. Selected declaration bodies below
-- are copied byte-for-byte from G; only this module header/namespace wrapper is new.
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

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::closure]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1202:17-1205:5 -/
@[reducible]
def pool_v1.pair_forest_semantic_terminal.equality_value.closure := Unit
/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::sub]:
    Source: 'src/field.rs', lines 906:4-913:5
    Visibility: public -/
def field.QM31.sub
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.sub self.c0 rhs.c0
  let c1 ← field.CM31.sub self.c1 rhs.c1
  ok { c0 := c, c1 }

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::{impl core::ops::function::Fn<(aspis_r1_mask_extraction_probe::field::QM31, aspis_r1_mask_extraction_probe::field::QM31), aspis_r1_mask_extraction_probe::field::QM31> for aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::equality_value::closure}::call]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1202:17-1205:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1208:4-1211:5 -/
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
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1201:0-1213:1 -/
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

end AspisR1SelectedMaskProbe
