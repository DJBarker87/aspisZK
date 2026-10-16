import OccupancyActualPacking
import SelectorMarginalModel
import SameBoxedRowExact
import SelectorValueLanePreprocessRangeValues
import ValueFamilyFieldTransport
import R0P.Occupancy

/-! Connect the actual occupancy packer to the retained family at the same
boxed point. Row success and selector-array semantics are derived, never
supplied as premises. -/
set_option autoImplicit false
namespace AspisR1.OccupancyCompletePacking
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedLoopModel
open AspisR1.ExtractedMaskQM31Exact
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.OccupancyActualPacking

abbrev QM := field.QM31
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Wide := AspisWideTower.WideExact
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev CanonicalArray {n : Usize} (a : Array QM n) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
abbrev mapOpenings (g : ExactQM →+* Wide) (o : R0P.Openings ExactQM) :
    R0P.Openings Wide := AspisR1.ValueFamilyFieldTransport.mapOpenings g o

@[irreducible] def wideOccupancyFamily : R0P.Family Wide :=
  R0P.occupancyFamily

private theorem occupancyLiteral_is_family {K : Type} [Field K]
    (pub : R0P.Public K) (o : R0P.Openings K) (sel : R0P.Sel K) :
    R0P.occupancyLanesLiteral (sel (63*16+9)) (sel (63*16+10))
      (R0P.occupancyExpected pub.variant) o.z =
      (R0P.occupancyFamily (K := K)).residuals pub o sel := by
  rfl

theorem wideOccupancyFamily_residuals_eq (pub : R0P.Public Wide)
    (o : R0P.Openings Wide) (sel : R0P.Sel Wide) :
    wideOccupancyFamily.residuals pub o sel =
      (R0P.occupancyFamily (K := Wide)).residuals pub o sel := by
  unfold wideOccupancyFamily
  rfl

private theorem openingMap_z (openings : Openings) :
    (mapOpenings f (exactOpenings openings)).z = fun i =>
      f (decode (openings.z.val[i.val]'
        (by simpa [openings.z.property] using i.isLt))) := by
  funext i
  rfl

private theorem pointSelector_input (point : Array QM 10#usize) :
    pointSelector point ⟨1017, by norm_num⟩ =
      pointSelector point ⟨63*16+9, by omega⟩ := by
  congr 1

private theorem pointSelector_output (point : Array QM 10#usize) :
    pointSelector point ⟨1018, by norm_num⟩ =
      pointSelector point ⟨63*16+10, by omega⟩ := by
  congr 1

theorem boxed_add_occupancy_lanes_success
    (packed : Array QM 24#usize)
    (public1 : pool_v1.pair_forest_semantic_terminal.SemanticPublic)
    (openings : Openings) (point : Array QM 10#usize) (selectors : Selectors)
    (pub : R0P.Public Wide)
    (hpacked : CanonicalArray packed)
    (hopened : CanonicalArray openings.z)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hvariant : pub.variant =
      AspisR1.OccupancyExpectedBridge.modelVariant public1.variant) :
    ∃ out : Array QM 24#usize,
      pool_v1.pair_forest_semantic_terminal.add_occupancy_lanes
        packed public1 openings selectors = .ok out ∧
      CanonicalArray out ∧
      (∀ j : Fin 24,
        f (decoded out j) = f (decoded packed j) +
          R0P.pack4 PackB (fun k : Fin 4 =>
            AspisR1.ValueLaneResidualList.selectList 0
              (wideOccupancyFamily.residuals pub
                (mapOpenings f (exactOpenings openings))
                (fun i => f (pointSelector point i)))
              (4*j.val+k.val))) := by
  obtain ⟨hhigh, hlow, _, _⟩ :=
    AspisR1.SelectorMarginalModel.boxed_marginals point selectors hpoint hbox
  obtain ⟨input, output, expected, occupancy, out,
      hinput, houtput, hexpected, hliteral, hcanOcc, hpack, hcanOut, hparent, hmodel⟩ :=
    AspisR1.OccupancyActualPacking.add_occupancy_lanes_success
      packed public1 openings selectors hpacked hhigh hlow hopened
  obtain ⟨inputPoint, hinputPoint, hinputCan, hinputModel⟩ :=
    AspisR1.SameBoxedRowExact.row_success point selectors
      1017#usize (by norm_num) hpoint hbox
  obtain ⟨outputPoint, houtputPoint, houtputCan, houtputModel⟩ :=
    AspisR1.SameBoxedRowExact.row_success point selectors
      1018#usize (by norm_num) hpoint hbox
  have hinputEq : input = inputPoint := by
    have hrow : pool_v1.pair_forest_copy_terminal.Selectors.row selectors
        1017#usize = .ok input := by simpa [AspisR1.OccupancyEntryRows.inputRow] using hinput
    exact Result.ok.inj (hrow.symm.trans hinputPoint)
  have houtputEq : output = outputPoint := by
    have hrow : pool_v1.pair_forest_copy_terminal.Selectors.row selectors
        1018#usize = .ok output := by simpa [AspisR1.OccupancyEntryRows.outputRow] using houtput
    exact Result.ok.inj (hrow.symm.trans houtputPoint)
  have hdecodeInput : decode input = pointSelector point ⟨1017, by norm_num⟩ := by
    rw [hinputEq]
    exact hinputModel
  have hdecodeOutput : decode output = pointSelector point ⟨1018, by norm_num⟩ := by
    rw [houtputEq]
    exact houtputModel
  have hfamily :
      R0P.occupancyLanesLiteral
          (f (decode input)) (f (decode output))
          (R0P.occupancyExpected
            (AspisR1.OccupancyExpectedBridge.modelVariant public1.variant))
          (fun i => f (decode
            (openings.z.val[i.val]'
              (by simpa [openings.z.property] using i.isLt)))) =
        wideOccupancyFamily.residuals pub
          (mapOpenings f (exactOpenings openings))
          (fun i => f (pointSelector point i)) := by
    calc
      R0P.occupancyLanesLiteral
          (f (decode input)) (f (decode output))
          (R0P.occupancyExpected
            (AspisR1.OccupancyExpectedBridge.modelVariant public1.variant))
          (fun i => f (decode
            (openings.z.val[i.val]'
              (by simpa [openings.z.property] using i.isLt)))) =
        R0P.occupancyLanesLiteral
          (f (pointSelector point ⟨1017, by norm_num⟩))
          (f (pointSelector point ⟨1018, by norm_num⟩))
          (R0P.occupancyExpected pub.variant)
          (mapOpenings f (exactOpenings openings)).z := by
            rw [hvariant, hdecodeInput, hdecodeOutput,
              pointSelector_input, pointSelector_output, openingMap_z]
      _ = (R0P.occupancyFamily (K := Wide)).residuals pub
            (mapOpenings f (exactOpenings openings))
            (fun i => f (pointSelector point i)) :=
          occupancyLiteral_is_family pub
            (mapOpenings f (exactOpenings openings))
            (fun i => f (pointSelector point i))
      _ = wideOccupancyFamily.residuals pub
            (mapOpenings f (exactOpenings openings))
            (fun i => f (pointSelector point i)) :=
          (wideOccupancyFamily_residuals_eq pub
            (mapOpenings f (exactOpenings openings))
            (fun i => f (pointSelector point i))).symm
  refine ⟨out, hparent, hcanOut, ?_⟩
  intro j
  rw [hfamily] at hmodel
  exact hmodel j

#print axioms openingMap_z
#print axioms wideOccupancyFamily_residuals_eq
#print axioms boxed_add_occupancy_lanes_success
end
end AspisR1.OccupancyCompletePacking
