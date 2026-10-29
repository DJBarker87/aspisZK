import PV_B3P_P227_14
import PV_B3P_PreweightedLoop12227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false
def context12_preweighted_reference_terminal_semantic_packed (operation : {N : Usize} → Array aspis_core.field.QM31 24#usize → Usize → Array aspis_core.field.QM31 N → Result (Array aspis_core.field.QM31 24#usize))
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
  Result (Array aspis_core.field.QM31 24#usize)
  := do
  let packed := Array.repeat 24#usize aspis_core.field.QM31.ZERO
  let packed1 ←
    reference_terminal.add_schedule_lanes packed public1 openings selectors
  let packed2 ← reference_terminal.add_path_lanes packed1 openings selectors
  let packed3 ← reference_terminal.add_value_lanes packed2 openings selectors
  let packed4 ←
    reference_terminal.add_occupancy_lanes packed3 public1 openings selectors
  let a ← reference_terminal.public_digest_lanes public1 openings selectors
  let packed5 ← operation packed4 84#usize a
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
  operation packed5 92#usize scalars
theorem caller12_preweighted_reference_terminal_semantic_packed 
  (public1 : reference_terminal.SemanticPublic)
  (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
  (selectors : reference_copy_terminal.Selectors) :
    @reference_terminal.semantic_packed public1 openings selectors = @context12_preweighted_reference_terminal_semantic_packed (@source_preweighted12) public1 openings selectors :=
  congrArg (fun operation => @context12_preweighted_reference_terminal_semantic_packed operation public1 openings selectors) preweighted_operation_binding12
#print axioms caller12_preweighted_reference_terminal_semantic_packed
end PV_B3P_Binding12227
