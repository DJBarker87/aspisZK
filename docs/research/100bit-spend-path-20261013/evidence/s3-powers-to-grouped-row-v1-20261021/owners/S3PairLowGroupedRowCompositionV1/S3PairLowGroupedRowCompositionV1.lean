import S3PairLowCallTotalCanonicalV1
import S3ActualGroupedPairSourceRowV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1PairLowGroupedComposition

open AspisR1PairLowCallCut
open AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete
open AspisR1GroupedPairActualFieldOpsV3.ActualGroupedPairSourceRow

/-- Public name for the existing source-row conclusion.  Keeping this as a
named proposition avoids restating implementation-private parser witnesses. -/
noncomputable def GroupedSourceRowResult
    (bytes : Slice Std.U8)
    (low : Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 16#usize)
    (out : AspisR1GroupedPairActualFieldOpsV3.field.WideExact)
    (h : AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations
      bytes low = .ok out) : Prop :=
  ∃ coefficients,
    AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair_loop0
      AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations
      { start := 0#usize, «end» := 64#usize } bytes
      (Array.repeat 12#usize AspisR1GroupedPairActualFieldOpsV3.field.WideExact.ZERO) =
        .ok coefficients ∧
    DecodedMeaning coefficients
      (PrefixMeaning
        (AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition.successfulInput
          bytes low out h)
        (fun _ => 0) 64) ∧
    AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode out =
      AspisR1.S3S9CurrentSourceModel.ungroupedPair
        (fun j =>
          AspisR1GroupedPairActualFieldOpsV3.SuccessPrefixComposition.successfulInput
            bytes low out h j.val)
        (fun s => (low.val.map
          AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.decode).getD s.val 0)
        AspisR1.S3S9CurrentSourceModel.inactiveAtSource

/-- The exact low-array callback cut returns sixteen current-field records.
Map those records fieldwise into the grouped helper's emitted WideExact owner;
the existing source-row theorem then consumes that very mapped array. The
Rust caller passes the same array directly; this theorem makes the nominal
Lean record adapter explicit. It joins the helper owners, but does not prove
the enclosing Rust `Weights::pair` control-flow or Std `from_fn` semantics. -/
theorem actual_low_array_feeds_grouped_source_row
    (c : weights.s2_twofold_low_array.closure)
    (hinputs : AspisR1S3PowersLowEntryCanonicalV1.lowInputsCanonical
      (closureToLowInputs c))
    (bytes : Slice Std.U8) :
    ∃ (scale : field.M31)
      (low : Array field.WideExact 16#usize)
      (lowFinal : weights.s2_twofold_low_array.closure × Usize)
      (model : Array ActualS (16#usize))
      (modelFinal : LowInputs × Usize)
      (groupLow : Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact 16#usize),
      actualFieldOps.m31Mul weights.QUARTER weights.QUARTER = .ok scale ∧
      weights.s2_twofold_low_array_model actualFieldOps c.1 c.2 =
        .ok (low, lowFinal) ∧
      AspisR1FromFnP6Generated.core.array.from_fn_model (16#usize)
        (AspisR1S3PowersLowActualCanonicalV1.generatedLowCallback scale)
        (closureToLowInputs c) = .ok (model, modelFinal) ∧
      low.val.map toActualS = model.val ∧
      lowFinal.1 = c ∧ lowFinal.2.val = 16 ∧
      groupLow.val = low.val.map toActualS ∧
      AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow groupLow ∧
      (∀ (out : AspisR1GroupedPairActualFieldOpsV3.field.WideExact)
        (hgroup : AspisR1GroupedPairActualFieldOpsV3.weights.s2_grouped_inactive_pair
          AspisR1GroupedPairActualFieldOpsV3.ActualFieldComplete.actualOperations
          bytes groupLow = .ok out),
        GroupedSourceRowResult bytes groupLow out hgroup) := by
  obtain ⟨scale, low, lowFinal, model, modelFinal, hscale, hlow, hmodel,
      hmap, hcan, hclosure, hcursor⟩ :=
    actual_pair_low_array_total_canonical c hinputs
  have hlen : (low.val.map toActualS).length = (16#usize).val := by
    have hp := low.property
    change low.val.length = (16#usize).val at hp
    simp [hp]
  let groupLow : Array AspisR1GroupedPairActualFieldOpsV3.field.WideExact (16#usize) :=
    ⟨low.val.map toActualS, hlen⟩
  have hcanonicalLow :
      AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow groupLow := by
    intro i
    have hi := hcan i
    simpa [groupLow,
      AspisR1GroupedPairActualFieldOpsV3.ActualLoop1.CanonicalLow] using hi
  refine ⟨scale, low, lowFinal, model, modelFinal, groupLow,
    hscale, hlow, hmodel, hmap, hclosure, hcursor, ?_, hcanonicalLow, ?_⟩
  · rfl
  · intro out hgroup
    obtain ⟨coefficients, hloop0, hmeaning, hrow⟩ :=
      actual_grouped_success_has_source_row_functional bytes groupLow out
        hcanonicalLow hgroup
    exact ⟨coefficients, hloop0, hmeaning, hrow⟩

#print axioms actual_low_array_feeds_grouped_source_row

end AspisR1PairLowGroupedComposition
