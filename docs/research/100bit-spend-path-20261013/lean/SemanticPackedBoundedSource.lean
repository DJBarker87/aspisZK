import SemanticPackedPrefix
import ScalarSuffixPacking
import DigestWrapperComposition

/-! Full semantic_packed caller with shared proved helper owners. The digest
callee is the explicit bounded implementation candidate; full modified-Rust
re-extraction and release correspondence remain separate. -/
open Aeneas Aeneas.Std Result
namespace AspisR1SemanticPackedBoundedCandidate
open AspisR1SelectedMaskProbe

def pool_v1.pair_forest_semantic_terminal.semantic_packed
  (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
  (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
  Result (Array field.QM31 24#usize)
  := do
  let packed := Array.repeat 24#usize field.QM31.ZERO
  let packed1 ←
    AspisR1ScheduleEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed public1
      openings selectors
  let packed2 ←
    AspisR1PathEnclosingCandidate.pool_v1.pair_forest_semantic_terminal.add_path_lanes packed1 openings
      selectors
  let packed3 ←
    AspisR1ValueLaneCandidate.pool_v1.pair_forest_semantic_terminal.add_value_lanes packed2 openings
      selectors
  let packed4 ←
    pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes packed3 public1
      openings selectors
  let a ←
    AspisR1DigestWrapperBoundedCandidate.pool_v1.pair_forest_semantic_terminal.public_digest_lanes public1 openings
      selectors
  let packed5 ←
    AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed4 84#usize a
  let q ← Array.index_usize openings.z 1#usize
  let q1 ← pool_v1.pair_forest_semantic_terminal.lift_m31 public1.asset_id
  let asset_difference ← field.QM31.sub q q1
  let i ← 2#usize * 16#usize
  let i1 ← i + 12#usize
  let q2 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i1
  let input_asset ← field.QM31.mul q2 asset_difference
  let i2 ← 31#usize * 16#usize
  let i3 ← i2 + 12#usize
  let q3 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i3
  let output_scalar ← field.QM31.mul q3 asset_difference
  let i4 ← 28#usize * 16#usize
  let i5 ← i4 + 12#usize
  let q4 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i5
  let private_transfer_term ← field.QM31.mul q4 asset_difference
  let withdrawal_amount_value ←
    lift (core.option.Option.unwrap_or public1.withdrawal_amount 0#u32)
  let i6 ←
    16#usize * pool_v1.pair_forest_semantic_terminal.VALUE_AUXILIARY_BLOCK
  let i7 ← i6 + 2#usize
  let q5 ← pool_v1.pair_forest_copy_terminal.Selectors.row selectors i7
  let q6 ← Array.index_usize openings.z 10#usize
  let q7 ←
    pool_v1.pair_forest_semantic_terminal.lift_m31 withdrawal_amount_value
  let q8 ← field.QM31.sub q6 q7
  let withdrawal_term ← field.QM31.mul q5 q8
  let b := core.option.Option.is_some public1.withdrawal_amount
  let scalars ←
    AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes public1.variant b
      input_asset output_scalar private_transfer_term withdrawal_term
  AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted packed5 92#usize
    scalars

end AspisR1SemanticPackedBoundedCandidate
