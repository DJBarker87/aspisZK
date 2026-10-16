import ScalarLaneSlice
import OccupancyExpectedBridge
import ExtractedMaskQM31Exact
import SelectorExpansionCorrectness
import R0P.Asset

/-! Actual source scalar_lanes, all variant/presence branches, with canonical
output and exact two-residual list; source arithmetic success is derived. -/
set_option autoImplicit false
namespace AspisR1.ScalarLaneExecution
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
abbrev QM := field.QM31
abbrev Canonical := CurrentCanonicalQM
abbrev CanonicalArray {N : Usize} (a : Array QM N) := AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev Variant := pool_v1.pair_forest_semantic_terminal.CompiledVariant
abbrev modelVariant := AspisR1.OccupancyExpectedBridge.modelVariant
abbrev source := AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes

private theorem make2_canonical (x y : QM) (hx : Canonical x) (hy : Canonical y) :
    CanonicalArray (Array.make 2#usize [x, y]) := by
  intro i
  have hi : i.val < 2 := by simpa using i.isLt
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  rcases hc with h0 | h1
  · simpa [Array.make, h0] using hx
  · simpa [Array.make, h1] using hy

theorem source_success (v : Variant) (present : Bool) (input output privateTerm withdrawalTerm : QM)
    (hi : Canonical input) (ho : Canonical output) (hp : Canonical privateTerm) (hw : Canonical withdrawalTerm) :
    ∃ out : Array QM 2#usize,
      source v present input output privateTerm withdrawalTerm = .ok out ∧ CanonicalArray out ∧
      out.val.map decode = R0P.assetScalarLanes (modelVariant v) present
        (decode input) (decode output) (decode privateTerm) (decode withdrawalTerm) := by
  cases v with
  | PrivateTransfer =>
    obtain ⟨sum, hsum, hcsum, hvsum⟩ := current_qm_add_exact output privateTerm ho hp
    refine ⟨Array.make 2#usize [input, sum], ?_, make2_canonical input sum hi hcsum, ?_⟩
    · simp only [source, AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes,
        hsum, bind_tc_ok]
    · simp only [Array.make, List.map_cons, List.map_nil, modelVariant,
        AspisR1.OccupancyExpectedBridge.modelVariant, R0P.assetScalarLanes, hvsum]
  | Withdrawal =>
    cases present with
    | false =>
      refine ⟨Array.make 2#usize [input, output], ?_, make2_canonical input output hi ho, ?_⟩
      · simp only [source, AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes,
          Bool.false_eq_true, if_false]
      · simp only [Array.make, List.map_cons, List.map_nil, modelVariant,
          AspisR1.OccupancyExpectedBridge.modelVariant, R0P.assetScalarLanes, Bool.false_eq_true, if_false]
    | true =>
      obtain ⟨sum, hsum, hcsum, hvsum⟩ := current_qm_add_exact output withdrawalTerm ho hw
      refine ⟨Array.make 2#usize [input, sum], ?_, make2_canonical input sum hi hcsum, ?_⟩
      · simp only [source, AspisR1ScalarCandidate.pool_v1.pair_forest_semantic_terminal.scalar_lanes,
          ↓reduceIte, if_true, hsum, bind_tc_ok]
      · simp only [Array.make, List.map_cons, List.map_nil, modelVariant,
          AspisR1.OccupancyExpectedBridge.modelVariant, R0P.assetScalarLanes, ↓reduceIte, if_true, hvsum]

#print axioms source_success
end AspisR1.ScalarLaneExecution
