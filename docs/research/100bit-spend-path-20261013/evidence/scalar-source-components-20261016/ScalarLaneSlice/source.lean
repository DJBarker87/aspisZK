import OccupancyGeneratedSlice

/-! Whole actual generated scalar_lanes helper, preserving both variant and
withdrawal-presence branches. Namespace/module framing only. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1ScalarCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::scalar_lanes]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 1127:0-1146:1 -/
def pool_v1.pair_forest_semantic_terminal.scalar_lanes
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant)
  (withdrawal_amount_present : Bool) (input_asset : field.QM31)
  (output_scalar : field.QM31) (private_transfer_term : field.QM31)
  (withdrawal_term : field.QM31) :
  Result (Array field.QM31 2#usize)
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    let output_scalar1 ← field.QM31.add output_scalar private_transfer_term
    ok (Array.make 2#usize [ input_asset, output_scalar1 ])
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    if withdrawal_amount_present
    then
      let output_scalar1 ← field.QM31.add output_scalar withdrawal_term
      ok (Array.make 2#usize [ input_asset, output_scalar1 ])
    else ok (Array.make 2#usize [ input_asset, output_scalar ])

end AspisR1ScalarCandidate
