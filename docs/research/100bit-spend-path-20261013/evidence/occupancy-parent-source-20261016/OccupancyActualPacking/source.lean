import OccupancyGeneratedSlice
import OccupancyEntryRows
import OccupancyLiteralExecutionAll12ExactListPublic
import PreweightedListSemantic
import ExtractedMaskSemanticBridgeConcrete
import ValueLaneSourceVector
import R0P.Occupancy

/-! The concrete occupancy parent consumes actual source rows, the generated
12-cell literal, and the retained start-zero preweighted packer. -/
set_option autoImplicit false
namespace AspisR1.OccupancyActualPacking
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedLoopModel

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Wide := AspisWideTower.WideExact
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a

private theorem map_occupancyLanesLiteral
    (input output expected : ExactQM) (opened : Fin 16 → ExactQM) :
    (R0P.occupancyLanesLiteral input output expected opened).map f =
      R0P.occupancyLanesLiteral (f input) (f output) (f expected)
        (fun i => f (opened i)) := by
  simp [R0P.occupancyLanesLiteral, List.map_ofFn, Function.comp_def,
    f, map_add, map_sub, map_mul, map_one]

private theorem map_occupancyExpected
    (variant : pool_v1.pair_forest_semantic_terminal.CompiledVariant) :
    f (R0P.occupancyExpected
        (AspisR1.OccupancyExpectedBridge.modelVariant variant)) =
      R0P.occupancyExpected
        (AspisR1.OccupancyExpectedBridge.modelVariant variant) := by
  cases variant <;>
    simp [AspisR1.OccupancyExpectedBridge.modelVariant,
      R0P.occupancyExpected, f]

theorem add_occupancy_lanes_success
    (packed : Array QM 24#usize)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (openings : Openings) (selectors : Selectors)
    (hpacked : CanonicalArray packed)
    (hhigh : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.high)
    (hlow : AspisR1.SelectorExpansionCorrectness.canonicalArray selectors.low)
    (hopened : CanonicalArray openings.z) :
    ∃ input output : QM, ∃ expected : field.M31,
    ∃ occupancy : Array QM 12#usize, ∃ out : Array QM 24#usize,
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors
        AspisR1.OccupancyEntryRows.inputRow = .ok input ∧
      pool_v1.pair_forest_copy_terminal.Selectors.row selectors
        AspisR1.OccupancyEntryRows.outputRow = .ok output ∧
      pool_v1.pair_forest_semantic_terminal.variant_expected_output
        public1.variant = .ok expected ∧
      pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal
        input output expected openings.z = .ok occupancy ∧
      CanonicalArray occupancy ∧
      AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted
        packed 0#usize occupancy = .ok out ∧
      CanonicalArray out ∧
      pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes
        packed public1 openings selectors = .ok out ∧
      ∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            AspisR1.ValueLaneResidualList.selectList 0
              (R0P.occupancyLanesLiteral
                (f (decode input)) (f (decode output))
                (R0P.occupancyExpected
                  (AspisR1.OccupancyExpectedBridge.modelVariant public1.variant))
                (fun i => f (decode
                  (openings.z.val[i.val]'
                    (by simpa [openings.z.property] using i.isLt)))))
              (4*j.val+k.val)) := by
  obtain ⟨input, output, hinput, hcanInput, _, houtput, hcanOutput, _⟩ :=
    AspisR1.OccupancyEntryRows.selector_rows_success selectors hhigh hlow
  obtain ⟨expected, occupancy, hexpected, hliteral, hcanOccupancy, hlist⟩ :=
    AspisR1.OccupancyLiteralExecutionAll12ExactListPublic.literal_success
      public1.variant input output openings.z hcanInput hcanOutput hopened
  have hmapVec :
      List.ofFn (AspisR1.ValueLaneSourceVector.arrayVector occupancy) =
        (List.ofFn (AspisR1.OccupancyLiteralExecutionAll12ExactListPublic.cellVector
          occupancy)).map f := by
    rw [List.map_ofFn]
    rfl
  have hopenVec :
      (fun i : Fin 16 => f (decode
        (AspisR1.OccupancyLiteralExecutionAll12ExactListPublic.get16 openings.z i))) =
      (fun i : Fin 16 => f (decode
        (openings.z.val[i.val]'
          (by simpa [openings.z.property] using i.isLt)))) := by
    funext i
    simp [AspisR1.OccupancyLiteralExecutionAll12ExactListPublic.get16]
  have hresiduals :
      List.ofFn (AspisR1.ValueLaneSourceVector.arrayVector occupancy) =
        R0P.occupancyLanesLiteral
          (f (decode input)) (f (decode output))
          (R0P.occupancyExpected
            (AspisR1.OccupancyExpectedBridge.modelVariant public1.variant))
          (fun i => f (decode
            (openings.z.val[i.val]'
              (by simpa [openings.z.property] using i.isLt)))) := by
    rw [hmapVec, hlist, map_occupancyLanesLiteral, map_occupancyExpected, hopenVec]
  obtain ⟨out, hpack, hcanOut, hmodel⟩ :=
    AspisR1.PreweightedListSemantic.add_preweighted_residual_list
      packed 0#usize occupancy
      (R0P.occupancyLanesLiteral
        (f (decode input)) (f (decode output))
        (R0P.occupancyExpected
          (AspisR1.OccupancyExpectedBridge.modelVariant public1.variant))
        (fun i => f (decode
          (openings.z.val[i.val]'
            (by simpa [openings.z.property] using i.isLt)))))
      (by scalar_tac) (by scalar_tac) hpacked hcanOccupancy hresiduals
  have hrowIn := AspisR1.OccupancyEntryRows.input_occupancy_row_success
  have hrowOut := AspisR1.OccupancyEntryRows.output_occupancy_row_success
  have hparent :
      pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes
        packed public1 openings selectors = .ok out := by
    unfold pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes
    simp only [hrowIn, bind_tc_ok, hinput, hrowOut, houtput,
      bind_tc_ok, hexpected, bind_tc_ok, hliteral, bind_tc_ok,
      pool_v1.pair_forest_semantic_terminal.add_preweighted, hpack]
  refine ⟨input, output, expected, occupancy, out,
    hinput, houtput, hexpected, hliteral, hcanOccupancy,
    hpack, hcanOut, hparent, ?_⟩
  intro j
  exact hmodel j

#print axioms map_occupancyLanesLiteral
#print axioms add_occupancy_lanes_success
end
end AspisR1.OccupancyActualPacking
