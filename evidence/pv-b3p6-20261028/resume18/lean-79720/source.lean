import PV_B3P_LocalClosure557227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 Result ControlFlow Error
set_option autoImplicit false
noncomputable section
attribute [local irreducible] local_bodies557
/-- Same caller control/dataflow with the fixed bound local callees substituted.
Remaining unchanged helpers and std/source coverage are separate obligations. -/
def semantic_callees557
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let packed := Array.repeat 24#usize aspis_core.field.QM31.ZERO
  let packed1 ←
    local_bodies557.body4 packed public1 openings selectors
  let packed2 ← local_bodies557.body2 packed1 openings selectors
  let packed3 ← local_bodies557.body5 packed2 openings selectors
  let packed4 ←
    reference_terminal.add_occupancy_lanes packed3 public1 openings selectors
  let a ← local_bodies557.body11 public1 openings selectors
  let packed5 ← local_bodies557.body3 packed4 84#usize a
  let q ← Array.index_usize openings.z 1#usize
  let q1 ← reference_terminal.lift_m31 public1.asset_id
  let asset_difference ← aspis_core.field.QM31.sub q q1
  let i ← lift (Std.Usize.wrapping_mul 2#usize 16#usize)
  let i1 ← lift (Std.Usize.wrapping_add i 12#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i1
  let input_asset ← aspis_core.field.QM31.mul q2 asset_difference
  let i2 ← lift (Std.Usize.wrapping_mul 31#usize 16#usize)
  let i3 ← lift (Std.Usize.wrapping_add i2 12#usize)
  let q3 ← reference_copy_terminal.Selectors.row selectors i3
  let output_scalar ← aspis_core.field.QM31.mul q3 asset_difference
  let i4 ← lift (Std.Usize.wrapping_mul 28#usize 16#usize)
  let i5 ← lift (Std.Usize.wrapping_add i4 12#usize)
  let q4 ← reference_copy_terminal.Selectors.row selectors i5
  let private_transfer_term ← aspis_core.field.QM31.mul q4 asset_difference
  let withdrawal_amount_value ←
    lift (core.option.Option.unwrap_or public1.withdrawal_amount 0#u32)
  let i6 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i7 ← lift (Std.Usize.wrapping_add i6 2#usize)
  let q5 ← reference_copy_terminal.Selectors.row selectors i7
  let q6 ← Array.index_usize openings.z 10#usize
  let q7 ← reference_terminal.lift_m31 withdrawal_amount_value
  let q8 ← aspis_core.field.QM31.sub q6 q7
  let withdrawal_term ← aspis_core.field.QM31.mul q5 q8
  let b := core.option.Option.is_some public1.withdrawal_amount
  let scalars ←
    reference_terminal.scalar_lanes public1.variant b input_asset output_scalar
      private_transfer_term withdrawal_term
  local_bodies557.body3 packed5 92#usize scalars

theorem semantic_callees_reference557 :
    semantic_callees557 = reference_terminal.semantic_packed := by
  unfold semantic_callees557 reference_terminal.semantic_packed
  rw [local_links557.link4,local_links557.link2,local_links557.link5,
    local_links557.link11,local_links557.link3]

#print axioms semantic_callees_reference557
end
end PV_B3P_Closure557227
