import Aeneas
import Aeneas.Std
import Aeneas.Tactic.RustAttributes
import SelectorSourceSlice
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::constants::ACTIVE_ROW_MASKS]
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal_constants.rs', lines 5:0-5:438 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS
  : Array Std.U16 64#usize :=
  Array.make 64#usize [
    6144#u16, 6144#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6144#u16, 4097#u16, 2048#u16,
    6145#u16, 2049#u16, 2048#u16, 6145#u16, 2049#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16, 6145#u16,
    6145#u16, 6145#u16, 6145#u16, 6145#u16, 4097#u16, 6145#u16, 6145#u16,
    4097#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16, 26214#u16,
    1749#u16
    ]

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis::MASKS]
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 198:8-198:76 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS
  : Array Std.U16 7#usize :=
  Array.make 7#usize [
    6144#u16, 6145#u16, 4097#u16, 2048#u16, 2049#u16, 26214#u16, 1749#u16
    ]

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis]: loop body 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 201:8-215:9 -/
@[rust_loop_body]
def pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
  (self : pool_v1.pair_forest_copy_terminal.Selectors)
  (high_sums : Array field.QM31 7#usize) (block : Std.Usize) :
  Result (ControlFlow ((Array field.QM31 7#usize) × Std.Usize)
    (pool_v1.pair_forest_copy_terminal.Selectors × (Array field.QM31
    7#usize)))
  := do
  let s ←
    lift (Array.to_slice
      pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS)
  let i := Slice.len s
  if block < i
  then
    let mask ←
      Array.index_usize
        pool_v1.pair_forest_copy_terminal.constants.ACTIVE_ROW_MASKS block
    let coordinate ←
      match mask with
      | 6144#uscalar => ok 0#usize
      | 6145#uscalar => ok 1#usize
      | 4097#uscalar => ok 2#usize
      | 2048#uscalar => ok 3#usize
      | 2049#uscalar => ok 4#usize
      | 26214#uscalar => ok 5#usize
      | 1749#uscalar => ok 6#usize
      | _ => fail panic
    let q ← Array.index_usize high_sums coordinate
    let q1 ← Array.index_usize self.high block
    let q2 ← field.QM31.add q q1
    let a ← Array.update high_sums coordinate q2
    let block1 ← block + 1#usize
    ok (cont (a, block1))
  else ok (done (self, high_sums))

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 201:8-215:9 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0
  (self : pool_v1.pair_forest_copy_terminal.Selectors)
  (high_sums : Array field.QM31 7#usize) (block : Std.Usize) :
  Result (pool_v1.pair_forest_copy_terminal.Selectors × (Array field.QM31
    7#usize))
  := do
  loop
    (fun (high_sums1, block1) =>
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0.body
      self high_sums1 block1)
    (high_sums, block)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis]: loop body 1:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 218:8-233:9 -/
@[rust_loop_body]
def pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body
  (self : pool_v1.pair_forest_copy_terminal.Selectors)
  (high_sums : Array field.QM31 7#usize) (sum : field.QM31)
  (coordinate : Std.Usize) :
  Result (ControlFlow (field.QM31 × Std.Usize) field.QM31)
  := do
  let s ←
    lift (Array.to_slice
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis.MASKS)
  let i := Slice.len s
  if coordinate < i
  then
    let low_sum ←
      match coordinate.val with
      | 0 =>
        do
        let q ← Array.index_usize self.low 11#usize
        let q1 ← Array.index_usize self.low 12#usize
        field.QM31.add q q1
      | 1 =>
        do
        let q ← Array.index_usize self.low 0#usize
        let q1 ← Array.index_usize self.low 11#usize
        let q2 ← field.QM31.add q q1
        let q3 ← Array.index_usize self.low 12#usize
        field.QM31.add q2 q3
      | 2 =>
        do
        let q ← Array.index_usize self.low 0#usize
        let q1 ← Array.index_usize self.low 12#usize
        field.QM31.add q q1
      | 3 => Array.index_usize self.low 11#usize
      | 4 =>
        do
        let q ← Array.index_usize self.low 0#usize
        let q1 ← Array.index_usize self.low 11#usize
        field.QM31.add q q1
      | 5 =>
        do
        let q ← Array.index_usize self.low 1#usize
        let q1 ← Array.index_usize self.low 2#usize
        let q2 ← field.QM31.add q q1
        let q3 ← Array.index_usize self.low 5#usize
        let q4 ← field.QM31.add q2 q3
        let q5 ← Array.index_usize self.low 6#usize
        let q6 ← field.QM31.add q4 q5
        let q7 ← Array.index_usize self.low 9#usize
        let q8 ← field.QM31.add q6 q7
        let q9 ← Array.index_usize self.low 10#usize
        let q10 ← field.QM31.add q8 q9
        let q11 ← Array.index_usize self.low 13#usize
        let q12 ← field.QM31.add q10 q11
        let q13 ← Array.index_usize self.low 14#usize
        field.QM31.add q12 q13
      | 6 =>
        do
        let q ← Array.index_usize self.low 0#usize
        let q1 ← Array.index_usize self.low 2#usize
        let q2 ← field.QM31.add q q1
        let q3 ← Array.index_usize self.low 4#usize
        let q4 ← field.QM31.add q2 q3
        let q5 ← Array.index_usize self.low 6#usize
        let q6 ← field.QM31.add q4 q5
        let q7 ← Array.index_usize self.low 7#usize
        let q8 ← field.QM31.add q6 q7
        let q9 ← Array.index_usize self.low 9#usize
        let q10 ← field.QM31.add q8 q9
        let q11 ← Array.index_usize self.low 10#usize
        field.QM31.add q10 q11
      | _ => fail panic
    let q ← Array.index_usize high_sums coordinate
    let q1 ← field.QM31.mul q low_sum
    let sum1 ← field.QM31.add sum q1
    let coordinate1 ← coordinate + 1#usize
    ok (cont (sum1, coordinate1))
  else ok (done sum)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis]: loop 1:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 218:8-233:9 -/
@[rust_loop]
def pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1
  (self : pool_v1.pair_forest_copy_terminal.Selectors)
  (high_sums : Array field.QM31 7#usize) (sum : field.QM31)
  (coordinate : Std.Usize) :
  Result field.QM31
  := do
  loop
    (fun (sum1, coordinate1) =>
      pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1.body
      self high_sums sum1 coordinate1)
    (sum, coordinate)

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis]:
    Source: 'src/statement/pool_v1/pair_forest_copy_terminal.rs', lines 194:4-235:5 -/
def pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis
  (self : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result field.QM31
  := do
  let high_sums := Array.repeat 7#usize field.QM31.ZERO
  let (self1, high_sums1) ←
    pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0 self
      high_sums 0#usize
  pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1 self1
    high_sums1 field.QM31.ZERO 0#usize

#print axioms pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop0
#print axioms pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis_loop1
#print axioms pool_v1.pair_forest_copy_terminal.Selectors.active_mask_basis

end AspisR1SelectedMaskProbe
