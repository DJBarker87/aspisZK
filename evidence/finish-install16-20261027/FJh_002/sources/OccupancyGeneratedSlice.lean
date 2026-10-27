import Aeneas.Std
import ImportUnionNamedDiscriminant
import Aeneas.Tactic.RustAttributes
import Aeneas.Data.Discriminant
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.Funs
import SelectorSourceSlice
import SelectorValueLaneLoops012Slice
import PreweightedWrapperSemantic

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section
namespace AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_tree_profile::PoolV1PairLiveSnapshotV1]
    Source: 'src/statement/pool_v1/pair_tree_profile.rs', lines 397:0-404:1
    Visibility: public -/
structure pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  sequence : Std.U64
  next_pair_index : Std.U64
  current_root : Array field.M31 8#usize
  frontier : Array (Array field.M31 8#usize) 20#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_terminal::PoolV1PairVerifiedAfterstateV1]
    Source: 'src/statement/pool_v1/pair_terminal.rs', lines 116:0-120:1
    Visibility: public -/
structure pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  next_pair_index : Std.U64
  next_root : Array field.M31 8#usize
  next_frontier : Array (Array field.M31 8#usize) 20#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_tree_profile::PoolV1PairLatePublicStatementV1]
    Source: 'src/statement/pool_v1/pair_tree_profile.rs', lines 407:0-412:1
    Visibility: public -/
structure pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  live_snapshot : pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1
  candidate_afterstate : pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::CompiledVariant]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 81:0-84:1 -/
@[import_union_discriminant isize]
inductive pool_v1.pair_forest_semantic_terminal.CompiledVariant where
| PrivateTransfer : pool_v1.pair_forest_semantic_terminal.CompiledVariant
| Withdrawal : pool_v1.pair_forest_semantic_terminal.CompiledVariant

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::SemanticPublic]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 87:0-98:1 -/
structure pool_v1.pair_forest_semantic_terminal.SemanticPublic where
  variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant
  pool : Array Std.U8 32#usize
  deployment_domain : Array Std.U8 32#usize
  anchor : Array field.M31 8#usize
  nullifier : Array field.M31 8#usize
  asset_id : field.M31
  recipient : Option (Array field.M31 8#usize)
  change : Array field.M31 8#usize
  withdrawal_amount : Option Std.U32
  transition : pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1

/-- Module-split adapter: occupancy source calls the existing separately sliced add_preweighted target. -/
def pool_v1.pair_forest_semantic_terminal.add_preweighted {N : Std.Usize}
  (packed : Array field.QM31 24#usize) (start : Std.Usize)
  (values : Array field.QM31 N) : Result (Array field.QM31 24#usize) :=
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
    packed start values

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::M31}::ZERO]
    Source: 'src/field.rs', lines 55:4-55:33
    Visibility: public -/
@[global_simps, irreducible] def field.M31.ZERO : field.M31 := 0#u32

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::ZERO]
    Source: 'src/field.rs', lines 261:4-264:6
    Visibility: public -/
@[global_simps, irreducible]
def field.CM31.ZERO : field.CM31 := { a := 0#u32, b := 0#u32 }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::CM31}::from_m31]:
    Source: 'src/field.rs', lines 276:4-278:5
    Visibility: public -/
def field.CM31.from_m31 (a : field.M31) : Result field.CM31 := do
  ok { a, b := field.M31.ZERO }

/-- [aspis_r1_mask_extraction_probe::field::{aspis_r1_mask_extraction_probe::field::QM31}::from_cm31]:
    Source: 'src/field.rs', lines 891:4-893:5
    Visibility: public -/
def field.QM31.from_cm31 (c0 : field.CM31) : Result field.QM31 := do
  ok { c0, c1 := field.CM31.ZERO }

/-- [aspis_r1_mask_extraction_probe::poseidon2::DIGEST_ELEMS]
    Source: 'src/statement/poseidon2.rs', lines 58:0-58:34
    Visibility: public -/
@[global_simps, irreducible] def poseidon2.DIGEST_ELEMS : Std.Usize := 8#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::lift_m31]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 101:0-103:1 -/
def pool_v1.pair_forest_semantic_terminal.lift_m31
  (value : field.M31) : Result field.QM31 := do
  let c ← field.CM31.from_m31 value
  field.QM31.from_cm31 c

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::occupancy_lanes_literal]: loop 0:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 576:4-578:5 -/
@[rust_loop]
def pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
  (iter : core.ops.range.Range Std.Usize) (opened : Array field.QM31 16#usize)
  (one_minus : field.QM31) (occupancy : Array field.QM31 12#usize)
  (both : field.QM31) :
  Result (Array field.QM31 12#usize)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok occupancy
  | some lane =>
    let i ← 2#usize + lane
    let q ← Array.index_usize opened i
    let q1 ← field.QM31.mul one_minus q
    let q2 ← field.QM31.mul both q1
    let i1 ← 3#usize + lane
    let a ← Array.update occupancy i1 q2
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop iter1
      opened one_minus a both
partial_fixpoint

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::occupancy_lanes_literal]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 562:0-583:1 -/
def pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
  (input_occupancy : field.QM31) (output_occupancy : field.QM31)
  (expected_output : field.M31) (opened : Array field.QM31 16#usize) :
  Result (Array field.QM31 12#usize)
  := do
  let occupied ← Array.index_usize opened 0#usize
  let inverse ← Array.index_usize opened 1#usize
  let one_minus ← field.QM31.sub field.QM31.ONE occupied
  let occupancy := Array.repeat 12#usize field.QM31.ZERO
  let both ← field.QM31.add input_occupancy output_occupancy
  let q ← field.QM31.sub occupied field.QM31.ONE
  let q1 ← field.QM31.mul occupied q
  let q2 ← field.QM31.mul both q1
  let occupancy1 ← Array.update occupancy 0#usize q2
  let q3 ← Array.index_usize opened 9#usize
  let q4 ← field.QM31.mul q3 inverse
  let q5 ← field.QM31.sub q4 occupied
  let q6 ← field.QM31.mul both q5
  let occupancy2 ← Array.update occupancy1 1#usize q6
  let q7 ← field.QM31.mul one_minus inverse
  let q8 ← field.QM31.mul both q7
  let a ← Array.update occupancy2 2#usize q8
  let occupancy3 ←
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal_loop
      { start := 0#usize, «end» := poseidon2.DIGEST_ELEMS } opened one_minus
      a both
  let q9 ← Array.index_usize opened 10#usize
  let q10 ← field.QM31.mul q9 one_minus
  let q11 ← field.QM31.mul input_occupancy q10
  let q12 ← pool_v1.pair_forest_semantic_terminal.lift_m31 expected_output
  let q13 ← field.QM31.sub occupied q12
  let q14 ← field.QM31.mul output_occupancy q13
  let q15 ← field.QM31.add q11 q14
  Array.update occupancy3 11#usize q15

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::variant_expected_output]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 527:0-532:1 -/
def pool_v1.pair_forest_semantic_terminal.variant_expected_output
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
  Result field.M31
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    ok 1#u32
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    ok 0#u32

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::OUTPUT_OCCUPANCY_ROW]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 61:0-61:49 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW
  : Result Std.Usize := do
  let i ← 63#usize * 16#usize
  i + 10#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::INPUT_OCCUPANCY_ROW]
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 60:0-60:47 -/
@[global_simps, irreducible]
def pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW
  : Result Std.Usize := do
  let i ← 63#usize * 16#usize
  i + 9#usize

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::add_occupancy_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 535:0-559:1 -/
def pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes
  (packed : Array field.QM31 24#usize)
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let i ← pool_v1.pair_forest_semantic_terminal.INPUT_OCCUPANCY_ROW
  let input_occupancy ←
    pool_v1.pair_forest_copy_terminal.Selectors.row selectors i
  let i1 ← pool_v1.pair_forest_semantic_terminal.OUTPUT_OCCUPANCY_ROW
  let output_occupancy ←
    pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let expected_output ←
    pool_v1.pair_forest_semantic_terminal.variant_expected_output
      public1.variant
  let occupancy ←
    pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
      input_occupancy output_occupancy expected_output openings.z
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize
    occupancy

end AspisR1SelectedMaskProbe
end
