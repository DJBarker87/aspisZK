import OccupancyGeneratedSlice

/-! Exact generated initial-variant selector helper, sharing the already
retained actual CompiledVariant type. Namespace/module framing only. -/
open Aeneas Aeneas.Std Result ControlFlow Error
namespace AspisR1InitialVariantCandidate
open AspisR1SelectedMaskProbe

/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_semantic_terminal::initial_variant_selectors]:
    Source: 'src/statement/pool_v1/pair_forest_semantic_terminal.rs', lines 222:0-242:1 -/
def pool_v1.pair_forest_semantic_terminal.initial_variant_selectors
  (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant)
  (high27 : field.QM31) (high28 : field.QM31) (high29 : field.QM31) :
  Result (field.QM31 × field.QM31 × field.QM31 × field.QM31)
  := do
  match variant with
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.PrivateTransfer =>
    let q ← field.QM31.add high27 high28
    ok (high27, field.QM31.ZERO, q, high29)
  | pool_v1.pair_forest_semantic_terminal.CompiledVariant.Withdrawal =>
    let q ← field.QM31.add high27 high28
    let q1 ← field.QM31.add q high29
    ok (field.QM31.ZERO, q1, field.QM31.ZERO, field.QM31.ZERO)

end AspisR1InitialVariantCandidate
