import NDO_JFy_Schedule
import RPv_JFy_ZeroArrays
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SemanticPrefix
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical)
open JFy_PublicCanonical (p)
open pool_v1.pair_forest_semantic_terminal

def tail (public1 : SemanticPublic) (openings : state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (packed : Array field.QM31 24#usize) : Result (Array field.QM31 24#usize) := do
  let packed3 ←
    pool_v1.pair_forest_semantic_terminal.add_value_lanes packed openings
      selectors
  let packed4 ←
    pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes packed3 public1
      openings selectors
  let a ←
    pool_v1.pair_forest_semantic_terminal.public_digest_lanes public1 openings
      selectors
  let packed5 ←
    pool_v1.pair_forest_semantic_terminal.add_preweighted packed4 84#usize a
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
    pool_v1.pair_forest_semantic_terminal.scalar_lanes public1.variant b
      input_asset output_scalar private_transfer_term withdrawal_term
  pool_v1.pair_forest_semantic_terminal.add_preweighted packed5 92#usize
    scalars

theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hz : canonical o.z) (hb : canonical o.succ_z) (hh : canonical s.high) (hl : canonical s.low) :
    ∃ schedule path,
    add_schedule_lanes (Array.repeat 24#usize field.QM31.ZERO) p o s=ok schedule ∧ canonical schedule ∧
    add_path_lanes schedule o s=ok path ∧ canonical path ∧
    semantic_packed p o s=tail p o s path := by
  obtain ⟨schedule,hs,hsc⟩ := WP.spec_imp_exists (JFy_Schedule.source _ o s (JFy_ZeroArrays.source _) hz hh hl)
  obtain ⟨path,hp,hpc⟩ := WP.spec_imp_exists (JFy_Path.source schedule o s hsc hz hb hh hl)
  refine ⟨schedule,path,hs,hsc,hp,hpc,?_⟩
  unfold semantic_packed
  dsimp only
  rw [hs,bind_tc_ok,hp,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFy_SemanticPrefix
end
