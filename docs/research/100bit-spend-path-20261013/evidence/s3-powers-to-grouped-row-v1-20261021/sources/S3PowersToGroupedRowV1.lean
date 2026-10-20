import S3PairLowGroupedRowCompositionV1
import S3PowersLowTotalV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S3PowersToGroupedRow

open AspisR1PowersConcreteMul
open AspisR1S3PowersLowEntryCanonicalV1
open AspisR1S3PowersLowTotalV1
open AspisR1PairLowCallCut
open AspisR1PairLowGroupedComposition
open AspisR1FromFnP6Generated

def CurrentLowGroupedResult
    (c : weights.s2_twofold_low_array.closure)
    (bytes : Slice Std.U8) : Prop :=
  ∃ (low : Array field.WideExact 16#usize)
    (lowFinal : weights.s2_twofold_low_array.closure × Usize)
    (groupLow : Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 16#usize),
    weights.s2_twofold_low_array_model actualFieldOps c.1 c.2 = .ok (low, lowFinal) ∧
    groupLow.val = low.val.map toActualS ∧
    AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow groupLow ∧
    (∀ (out : AspisR1GroupedPairActualFieldOpsV3.field.WideExact)
      (hgroup : AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair
        AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations
        bytes groupLow = .ok out),
      GroupedSourceRowResult bytes groupLow out hgroup)

/-- For canonical bases, the checked generated `weights::powers::<4>` array
models can be carried through the explicit inverse current/power carrier maps
into the actual S3 low-array helper. The low helper uses those same two
power-output lists, and its grouped source-row composition follows. This is a
P6/cut composition: the enclosing Rust `Weights::pair` branch and the Rust
`core::array::from_fn` correspondence remain separate obligations. -/
theorem canonical_power_arrays_feed_current_low_and_grouped_row
    (x0 x1 : CallbackWide)
    (hx0 : Canonical x0)
    (hx1 : Canonical x1)
    (bytes : Slice Std.U8) :
    ∃ (powers0 : Array CallbackWide (4#usize))
      (powerFinal0 : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize) × Usize)
      (powers1 : Array CallbackWide (4#usize))
      (powerFinal1 : AspisR1S3PowersCanonicalTraceV1.PowerState (4#usize) × Usize)
      (c : weights.s2_twofold_low_array.closure),
      core.array.from_fn_model (4#usize)
        (generatedPowerCallback (4#usize))
        (AspisR1CurrentPowers.field.WideExact.ONE, x0) = .ok (powers0, powerFinal0) ∧
      core.array.from_fn_model (4#usize)
        (generatedPowerCallback (4#usize))
        (AspisR1CurrentPowers.field.WideExact.ONE, x1) = .ok (powers1, powerFinal1) ∧
      c.1.val.map generatedToPower = powers0.val ∧
      c.2.val.map generatedToPower = powers1.val ∧
      lowInputsCanonical (closureToLowInputs c) ∧
      CurrentLowGroupedResult c bytes := by
  obtain ⟨powers0, powerFinal0, hrun0⟩ :=
    generated_power_array_total (N := 4#usize) x0 hx0
  obtain ⟨powers1, powerFinal1, hrun1⟩ :=
    generated_power_array_total (N := 4#usize) x1 hx1
  have hcan0 := p6_generated_powers_array_success_canonical
    x0 powers0 powerFinal0 hx0 hrun0
  have hcan1 := p6_generated_powers_array_success_canonical
    x1 powers1 powerFinal1 hx1 hrun1
  have hlen0 : powers0.val.length = 4 := by
    have hp := powers0.property
    change powers0.val.length = (4#usize).val at hp
    have hfour : (4#usize).val = 4 := by decide
    omega
  have hlen1 : powers1.val.length = 4 := by
    have hp := powers1.property
    change powers1.val.length = (4#usize).val at hp
    have hfour : (4#usize).val = 4 := by decide
    omega
  have hlist0 : callbackCanonical powers0.val := by
    intro i hi
    have hi' : i < powers0.val.length := by omega
    let value := powers0.val[i]'hi'
    have hmem : value ∈ powers0.val :=
      List.getElem_mem (l := powers0.val) (n := i) hi'
    exact ⟨value, List.getElem?_eq_getElem hi', hcan0 value hmem⟩
  have hlist1 : callbackCanonical powers1.val := by
    intro i hi
    have hi' : i < powers1.val.length := by omega
    let value := powers1.val[i]'hi'
    have hmem : value ∈ powers1.val :=
      List.getElem_mem (l := powers1.val) (n := i) hi'
    exact ⟨value, List.getElem?_eq_getElem hi', hcan1 value hmem⟩
  let ap0 : Array field.WideExact (4#usize) :=
    ⟨powers0.val.map powerToGenerated, by
      rw [List.length_map]
      have hfour : (4#usize).val = 4 := by decide
      omega⟩
  let ap1 : Array field.WideExact (4#usize) :=
    ⟨powers1.val.map powerToGenerated, by
      rw [List.length_map]
      have hfour : (4#usize).val = 4 := by decide
      omega⟩
  let c : weights.s2_twofold_low_array.closure := (ap0, ap1)
  have hleft : c.1.val.map generatedToPower = powers0.val := by
    change (powers0.val.map powerToGenerated).map generatedToPower = powers0.val
    rw [List.map_map]
    calc
      List.map (fun z => generatedToPower (powerToGenerated z)) powers0.val =
          List.map id powers0.val := by
        exact List.map_congr_left (l := powers0.val)
          (f := fun z => generatedToPower (powerToGenerated z)) (g := id)
          (by intro z hz; exact power_generated_roundtrip z)
      _ = powers0.val := List.map_id powers0.val
  have hright : c.2.val.map generatedToPower = powers1.val := by
    change (powers1.val.map powerToGenerated).map generatedToPower = powers1.val
    rw [List.map_map]
    calc
      List.map (fun z => generatedToPower (powerToGenerated z)) powers1.val =
          List.map id powers1.val := by
        exact List.map_congr_left (l := powers1.val)
          (f := fun z => generatedToPower (powerToGenerated z)) (g := id)
          (by intro z hz; exact power_generated_roundtrip z)
      _ = powers1.val := List.map_id powers1.val
  have hinputs : lowInputsCanonical (closureToLowInputs c) := by
    change (c.1.val.map generatedToPower).length = 4 ∧
      (c.2.val.map generatedToPower).length = 4 ∧
      callbackCanonical (c.1.val.map generatedToPower) ∧
      callbackCanonical (c.2.val.map generatedToPower)
    rw [hleft, hright]
    exact ⟨hlen0, hlen1, hlist0, hlist1⟩
  have hrows := actual_low_array_feeds_grouped_source_row c hinputs bytes
  obtain ⟨scale, low, lowFinal, model, modelFinal, groupLow,
    hscale, hlow, hmodel, hmap, hclosure, hcursor, harray, hcanonical, hrow⟩ := hrows
  exact ⟨powers0, powerFinal0, powers1, powerFinal1, c,
    hrun0, hrun1, hleft, hright, hinputs, ⟨low, lowFinal, groupLow,
      hlow, harray, hcanonical, hrow⟩⟩

#print axioms canonical_power_arrays_feed_current_low_and_grouped_row

end AspisR1S3PowersToGroupedRow
