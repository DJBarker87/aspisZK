import CopyEndpointSource

/-! Actual Copy endpoint update: shared selector-row execution, existing
field arithmetic and generic checked update/frame facts are composed here.
The source slot/pattern/tag bounds are explicit generated-registry obligations. -/
set_option autoImplicit false
namespace AspisR1.CopyEndpointExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ArrayUpdateCanonicalExact
abbrev QM := field.QM31
abbrev Endpoint := AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestEndpoint
abbrev Selectors := pool_v1.pair_forest_copy_terminal.Selectors
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev decode := AspisR1.ExtractedMaskQM31Exact.decode

def decodedCells {n : Usize} (a : Array QM n) : Fin n.val → ExactQM :=
  fun i => decode (cells a i)

def modelEndpoint (e : Endpoint) (hr : e.row.val < 1024)
    (hs : e.slot.val < 2) (hp : e.pattern.val < 14) : R0P.CopyEndpoint :=
  { row := ⟨e.row.val, hr⟩, slot := ⟨e.slot.val, hs⟩,
    pattern := ⟨e.pattern.val, hp⟩ }

def modelSelectors (s : Selectors) : R0P.CopySelectors ExactQM :=
  { high := fun i => AspisR1.SelectorExpansionCorrectness.decodedArray s.high i.val,
    low := fun i => AspisR1.SelectorExpansionCorrectness.decodedArray s.low i.val }

private theorem decoded_update {n : Usize} (a b : Array QM n)
    (i : Fin n.val) (q : QM)
    (h : cells b = Function.update (cells a) i q) :
    decodedCells b = Function.update (decodedCells a) i (decode q) := by
  funext j
  change decode (cells b j) = _
  rw [h]
  by_cases he : j = i
  · subst j; simp [decodedCells]
  · simp [Function.update, he, decodedCells]

/-- Every actual endpoint read, arithmetic operation and store succeeds.
The returned arrays are canonical and equal the retained model's two updates. -/
theorem endpoint_success
    (values weights : Array QM 2#usize) (endpoint : Endpoint)
    (tag : U32) (weight : field.M31) (patterns : Array QM 14#usize)
    (selectors : Selectors)
    (hvalues : CanonicalArray values) (hweights : CanonicalArray weights)
    (hpatterns : CanonicalArray patterns)
    (hhigh : CanonicalArray selectors.high) (hlow : CanonicalArray selectors.low)
    (hrow : endpoint.row.val < 1024) (hslot : endpoint.slot.val < 2)
    (hpattern : endpoint.pattern.val < 14)
    (htag : tag.val < AspisR1.TerminalLiftM31Exact.P) :
    ∃ valuesOut weightsOut,
      AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.accumulate_endpoint
        values weights endpoint tag weight patterns selectors = .ok (valuesOut, weightsOut) ∧
      CanonicalArray valuesOut ∧ CanonicalArray weightsOut ∧
      (decodedCells valuesOut, decodedCells weightsOut) =
        R0P.copyAccumulateEndpoint (decodedCells values) (decodedCells weights)
          (modelEndpoint endpoint hrow hslot hpattern) tag.val
          (weight.val : ExactQM) (decodedCells patterns) (modelSelectors selectors) := by
  let rowIndex := core.convert.num.FromUsizeU16.from endpoint.row
  let slot := core.convert.num.FromUsizeU8.from endpoint.slot
  let patternIndex := core.convert.num.FromUsizeU8.from endpoint.pattern
  let slotFin : Fin 2 := ⟨endpoint.slot.val, hslot⟩
  let patternFin : Fin 14 := ⟨endpoint.pattern.val, hpattern⟩
  have hrowValue : rowIndex.val = endpoint.row.val := by
    exact core.convert.num.FromUsizeU16.from_val_eq endpoint.row
  have hslotValue : slot.val = endpoint.slot.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq endpoint.slot
  have hpatternValue : patternIndex.val = endpoint.pattern.val := by
    exact core.convert.num.FromUsizeU8.from_val_eq endpoint.pattern
  have hslotBound : slot.val < (2#usize).val := by simpa [hslotValue] using hslot
  have hpatternBound : patternIndex.val < (14#usize).val := by
    simpa [hpatternValue] using hpattern
  obtain ⟨selector, hrowRun, hselectorCan, hselectorValue⟩ :=
    AspisR1.SelectorRowCall.row_success_of_canonical selectors rowIndex
      (by rw [hrowValue]; exact hrow) hhigh hlow
  have hselector : decode selector =
      R0P.copySelectorRow (modelSelectors selectors)
        (modelEndpoint endpoint hrow hslot hpattern).row := by
    change decode selector =
      AspisR1.SelectorExpansionCorrectness.decodedArray selectors.high
        (endpoint.row.val / 16) *
      AspisR1.SelectorExpansionCorrectness.decodedArray selectors.low
        (endpoint.row.val % 16)
    simpa [hrowValue] using hselectorValue
  let oldWeight := cells weights slotFin
  let oldValue := cells values slotFin
  let patternValue := cells patterns patternFin
  have hreadWeight : Array.index_usize weights slot = .ok oldWeight := by
    simpa [oldWeight, cells, slotFin, hslotValue] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok weights slot hslotBound
  have hreadValue : Array.index_usize values slot = .ok oldValue := by
    simpa [oldValue, cells, slotFin, hslotValue] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok values slot hslotBound
  have hreadPattern : Array.index_usize patterns patternIndex = .ok patternValue := by
    simpa [patternValue, cells, patternFin, hpatternValue] using
      AspisR1.ExtractedMaskHornerStep.array_index_usize_ok patterns patternIndex hpatternBound
  obtain ⟨weighted, hweighted, hcweighted, hvweighted⟩ :=
    AspisR1.ExtractedMaskScalarExact.current_qm_mul_m31_exact selector weight
  change decode weighted = decode selector *
    AspisR1.ExtractedMaskScalarExact.scalarEmbedding weight at hvweighted
  rw [AspisR1.ScheduleDomainArithmetic.scalarEmbedding_nat] at hvweighted
  obtain ⟨nextWeight, hnextWeight, hcnextWeight, hvnextWeight⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact oldWeight weighted
      (hweights slotFin) hcweighted
  change decode nextWeight = decode oldWeight + decode weighted at hvnextWeight
  obtain ⟨weightsOut, hweightsOut, hcweightsOut, hweightsFrame⟩ :=
    update_success weights slot nextWeight hslotBound hweights hcnextWeight
  have hslotFin : (⟨slot.val, hslotBound⟩ : Fin (2#usize).val) = slotFin := by
    apply Fin.ext; exact hslotValue
  rw [hslotFin] at hweightsFrame
  obtain ⟨tagValue, htagRun, hctagValue, hvtagValue⟩ :=
    AspisR1.TerminalLiftM31Exact.lift_source_exact tag htag
  have hcopyLift : AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.lift_m31 tag =
      .ok tagValue := by
    change pool_v1.pair_forest_semantic_terminal.lift_m31 tag = .ok tagValue
    exact htagRun
  change decode tagValue = (tag.val : ExactQM) at hvtagValue
  obtain ⟨compressed, hcompressed, hccompressed, hvcompressed⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact tagValue patternValue
      hctagValue (hpatterns patternFin)
  change decode compressed = decode tagValue + decode patternValue at hvcompressed
  obtain ⟨selected, hselected, hcselected, hvselected⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact selector compressed
      hselectorCan hccompressed
  change decode selected = decode selector * decode compressed at hvselected
  obtain ⟨nextValue, hnextValue, hcnextValue, hvnextValue⟩ :=
    AspisR1.ExtractedMaskQM31Exact.current_qm_add_exact oldValue selected
      (hvalues slotFin) hcselected
  change decode nextValue = decode oldValue + decode selected at hvnextValue
  obtain ⟨valuesOut, hvaluesOut, hcvaluesOut, hvaluesFrame⟩ :=
    update_success values slot nextValue hslotBound hvalues hcnextValue
  rw [hslotFin] at hvaluesFrame
  refine ⟨valuesOut, weightsOut, ?_, hcvaluesOut, hcweightsOut, ?_⟩
  · dsimp only [rowIndex, slot, patternIndex] at hrowRun hreadWeight hreadValue hreadPattern hweightsOut hvaluesOut
    simp only [AspisR1CopyEndpointCandidate.pool_v1.pair_forest_copy_terminal.accumulate_endpoint,
      lift, hrowRun, hreadWeight, hweighted, hnextWeight, hweightsOut,
      hcopyLift, hreadPattern, hcompressed, hreadValue, hselected, hnextValue,
      hvaluesOut, bind_tc_ok]
  · have hvaluesDecode := decoded_update values valuesOut slotFin nextValue hvaluesFrame
    have hweightsDecode := decoded_update weights weightsOut slotFin nextWeight hweightsFrame
    rw [hvaluesDecode, hweightsDecode]
    change (Function.update (decodedCells values) slotFin (decode nextValue),
      Function.update (decodedCells weights) slotFin (decode nextWeight)) =
      (Function.update (decodedCells values) slotFin
        (decode oldValue + R0P.copySelectorRow (modelSelectors selectors)
          (modelEndpoint endpoint hrow hslot hpattern).row *
          ((tag.val : ExactQM) + decode patternValue)),
       Function.update (decodedCells weights) slotFin
        (decode oldWeight + R0P.copySelectorRow (modelSelectors selectors)
          (modelEndpoint endpoint hrow hslot hpattern).row * (weight.val : ExactQM)))
    rw [hvnextValue, hvselected, hvcompressed, hvtagValue, hvnextWeight,
      hvweighted, hselector]

#print axioms endpoint_success
end
end AspisR1.CopyEndpointExact
