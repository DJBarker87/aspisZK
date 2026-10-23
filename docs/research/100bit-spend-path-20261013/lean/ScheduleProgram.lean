import InitialSelectorPrefix
import InitialArrayExecution
import InitialArrayWrites
import ScheduleDomainToModel
import AbsorptionSelectorSetup
import ScheduleInitialModel
import SelectorValueLanePreprocessRangeValues

/-! Complete source-order initial/absorption program. All component premises
are discharged from one actual boxed point and canonical source openings. -/
set_option autoImplicit false
namespace AspisR1.ScheduleProgram
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.AbsorptionCallback
open AspisR1.ExtractedMaskQM31Exact
abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev Public := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev CanonicalArray {N : Usize} (a : Array QM N) :=
  AspisR1.SelectorExpansionCorrectness.canonicalArray a
abbrev exactOpenings := AspisR1.SelectorValueLanePreprocessRangeValues.exactOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev modelVariant := AspisR1.InitialVariantExact.modelVariant

def run (public1 : Public) (openings : Openings) (selectors : Selectors) :
    Result (Array QM 16#usize × Array QM 16#usize) := do
  let p ← AspisR1.InitialSelectorPrefix.run public1.variant selectors
  let initial ← AspisR1.InitialArrayExecution.run p.full p.rate openings
  let (domain, length) ← AspisR1.ScheduleDomainArithmetic.run p.high0 p.high1 p.high25 p.high30 p.transfer
  let initial1 ← AspisR1.InitialArrayWrites.run initial p.low0 domain length
  let a ← AspisR1.AbsorptionSelectorSetup.run p selectors
  let absorption ← AspisR1AbsorptionCandidate.pool_v1.pair_forest_semantic_terminal.absorption_lanes_literal
    a.low a.fixed a.two a.eight a.nodes openings.z
  .ok (initial1, absorption)

attribute [local irreducible] R0P.g2High R0P.g2Low R0P.g2SumHigh R0P.scheduleNodes

theorem same_boxed_source_success (point : Array QM 10#usize) (selectors : Selectors)
    (public1 : Public) (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) :
    ∃ initial absorption,
      run public1 openings selectors = .ok (initial, absorption) ∧
      (∀ i : Fin 16, Canonical (sourceCell initial i)) ∧
      (∀ i : Fin 16, Canonical (sourceCell absorption i)) ∧
      (∀ i : Fin 16, decode (sourceCell initial i) =
        R0P.scheduleInitial (modelVariant public1.variant) (exactOpenings openings) (pointSelector point) i) ∧
      ∀ i : Fin 16, decode (sourceCell absorption i) =
        R0P.scheduleAbsorption (modelVariant public1.variant) (exactOpenings openings) (pointSelector point) i := by
  have hzCells : ∀ i : Fin 16, Canonical (sourceCell openings.z i) := by
    intro i
    exact hz ⟨i.val, by simpa using i.isLt⟩
  obtain ⟨p, hprefix, hcp, hmp⟩ :=
    AspisR1.InitialSelectorPrefix.same_boxed_success point selectors public1.variant hpoint hbox
  have hcpCopy := hcp
  rcases hcpCopy with ⟨_hc0, _hc1, _hc25, _hc30, _hcnodes, _hct, _hcfixed, _hc8, _hc2, hclow, hcfull, hcrate⟩
  let expected := AspisR1.InitialSelectorPrefix.model (modelVariant public1.variant) (pointSelector point)
  have hfull : decode p.full = expected.full := congrArg AspisR1.InitialSelectorPrefix.Registers.full hmp
  have hrate : decode p.rate = expected.rate := congrArg AspisR1.InitialSelectorPrefix.Registers.rate hmp
  have hlow : decode p.low0 = expected.low0 := congrArg AspisR1.InitialSelectorPrefix.Registers.low0 hmp
  obtain ⟨initial, hinitial, hcinitial, hvinitial⟩ :=
    AspisR1.InitialArrayExecution.source_success p.full p.rate openings hcfull hcrate hzCells
  obtain ⟨domain, length, hdomain, hcdomain, hclength, hvdomain, hvlength⟩ :=
    AspisR1.ScheduleDomainToModel.source_success p hcp
  rw [hmp] at hvdomain hvlength
  obtain ⟨initial1, hwrites, hcinitial1, hvwrites⟩ :=
    AspisR1.InitialArrayWrites.source_success initial p.low0 domain length hcinitial hclow hcdomain hclength
  obtain ⟨a, hsetup, hca, hma⟩ := AspisR1.AbsorptionSelectorSetup.source_success
    point selectors (modelVariant public1.variant) p hpoint hbox hcp hmp
  rcases hca with ⟨hcalow, hcafixed, hcatwo, hcaeight, hcanodes⟩
  obtain ⟨absorption, habsorption, hcabsorption, hvabsorption⟩ :=
    AspisR1.AbsorptionLiteralExecution.source_success a.low a.fixed a.two a.eight a.nodes
      openings.z hcalow hcafixed hcatwo hcaeight hcanodes hzCells
  let expectedA := AspisR1.AbsorptionSelectorSetup.model (modelVariant public1.variant) (pointSelector point)
  have halow : decode a.low = expectedA.low := congrArg AspisR1.AbsorptionSelectorSetup.Registers.low hma
  have hafixed : decode a.fixed = expectedA.fixed := congrArg AspisR1.AbsorptionSelectorSetup.Registers.fixed hma
  have hatwo : decode a.two = expectedA.two := congrArg AspisR1.AbsorptionSelectorSetup.Registers.two hma
  have haeight : decode a.eight = expectedA.eight := congrArg AspisR1.AbsorptionSelectorSetup.Registers.eight hma
  have hanodes : decode a.nodes = expectedA.nodes := congrArg AspisR1.AbsorptionSelectorSetup.Registers.nodes hma
  have hzModel : (fun i : Fin 16 => decode (sourceCell openings.z i)) = (exactOpenings openings).z := rfl
  have hinitialModel (i : Fin 16) : decode (sourceCell initial i) =
      AspisR1.ScheduleInitialModel.baseValue expected (exactOpenings openings).z i := by
    have hv := hvinitial i
    rw [hfull, hrate] at hv
    simpa only [AspisR1.ScheduleInitialModel.baseValue, ← hzModel] using hv
  refine ⟨initial1, absorption, ?_, hcinitial1, hcabsorption, ?_, ?_⟩
  · simp only [AspisR1.AbsorptionLiteralExecution.source] at habsorption
    simp only [run, hprefix, bind_tc_ok, hinitial, hdomain, hwrites, hsetup, habsorption]
    change ((do
      let initial1 ← AspisR1.InitialArrayWrites.run initial p.low0 domain length
      Result.ok (initial1, absorption)) : Result (Array QM 16#usize × Array QM 16#usize)) = _
    simp only [hwrites, bind_tc_ok]
  · intro i
    have hv : decode (sourceCell initial1 i) =
        AspisR1.ScheduleInitialModel.initialValue expected (exactOpenings openings).z i := by
      simpa only [AspisR1.ScheduleInitialModel.initialValue, hinitialModel i,
        hlow, hvdomain, hvlength] using hvwrites i
    exact hv.trans (AspisR1.ScheduleInitialModel.initialValue_eq_schedule
      (modelVariant public1.variant) (exactOpenings openings) (pointSelector point) i)
  · intro i
    have hv := hvabsorption i
    rw [halow, hafixed, hatwo, haeight, hanodes] at hv
    rw [hzModel] at hv
    exact hv.trans (AspisR1.ScheduleInitialModel.absorptionValue_eq_schedule
      (modelVariant public1.variant) (exactOpenings openings) (pointSelector point) i)

#print axioms same_boxed_source_success
end
end AspisR1.ScheduleProgram
