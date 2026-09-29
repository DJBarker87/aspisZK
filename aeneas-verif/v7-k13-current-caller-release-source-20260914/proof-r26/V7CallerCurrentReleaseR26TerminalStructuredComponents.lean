import V7CallerCurrentReleaseR26AcceptedWeightVectorSemantics

/-!
# Terminal dot semantics for structured components

At log length two the production dot helper uses direct four-value formulas
for multilinear and tensor components.  These theorems connect those formulas
to the same K1 component vectors used by the optimized-fold proof.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open scoped BigOperators
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TerminalStructuredComponents

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26K1QueryWeightBridge
open V7CallerCurrentReleaseR26K1StructuredWeightBridge
open AspisV5FriRelationCandidateBridge

abbrev RawQM31 := field.QM31
abbrev ModelQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def terminalValues (values : Slice RawQM31) : Fin 4 → ModelQM31 :=
  fun index => exactRaw values.val[index.val]!

def CanonicalSlice (values : Slice RawQM31) : Prop :=
  ∀ index, index < values.length →
    GeneratedCanonicalQM31 values.val[index]!

def multilinearTerminal (scale p0 p1 : RawQM31)
    (values : Slice RawQM31) : ModelQM31 :=
  exactRaw scale *
    ((1 - exactRaw p0) * (1 - exactRaw p1) * terminalValues values 0 +
     (1 - exactRaw p0) * exactRaw p1 * terminalValues values 1 +
     exactRaw p0 * (1 - exactRaw p1) * terminalValues values 2 +
     exactRaw p0 * exactRaw p1 * terminalValues values 3)

def tensorTerminal (scale f0 f1 : RawQM31)
    (values : Slice RawQM31) : ModelQM31 :=
  exactRaw scale *
    (terminalValues values 0 + exactRaw f1 * terminalValues values 1 +
     exactRaw f0 * terminalValues values 2 +
     exactRaw f0 * exactRaw f1 * terminalValues values 3)

private theorem sliceIndexRun
    (values : Slice RawQM31) (index : Std.Usize)
    (bound : index.val < values.length) :
    Slice.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (Slice.index_usize_spec values index (by simpa using bound))
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  simpa [exact, listExact] using run

private theorem vecIndexRun
    (values : alloc.vec.Vec RawQM31) (index : Std.Usize)
    (bound : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) values index =
      ok values.val[index.val]! := by
  obtain ⟨value, run, exact⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index (by simpa using bound))
  have listExact : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using bound
  rw [alloc.vec.Vec.index_slice_index]
  simpa [exact, listExact] using run

theorem dot_terminal_multilinear_corresponds
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (values : Slice RawQM31)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (pointCanonical :
      V7CallerCurrentReleaseR26MultilinearFoldSemantics.CanonicalList
        point.val)
    (pointLength : point.val.length = 2)
    (valuesCanonical : CanonicalSlice values)
    (valuesLength : values.length = 4) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.dot_terminal_component
          (.Multilinear scale point) values = ok out ∧
      GeneratedCanonicalQM31 out ∧
      sourceQm31ToModel (generatedQm31ToExact out) =
        multilinearTerminal scale point.val[0]! point.val[1]! values := by
  let v0 := values.val[0]!
  let v1 := values.val[1]!
  let v2 := values.val[2]!
  let v3 := values.val[3]!
  let p0 := point.val[0]!
  let p1 := point.val[1]!
  have readV0 : Slice.index_usize values 0#usize = ok v0 := by
    simpa [v0] using sliceIndexRun values 0#usize (by simpa [valuesLength])
  have readV1 : Slice.index_usize values 1#usize = ok v1 := by
    simpa [v1] using sliceIndexRun values 1#usize (by simpa [valuesLength])
  have readV2 : Slice.index_usize values 2#usize = ok v2 := by
    simpa [v2] using sliceIndexRun values 2#usize (by simpa [valuesLength])
  have readV3 : Slice.index_usize values 3#usize = ok v3 := by
    simpa [v3] using sliceIndexRun values 3#usize (by simpa [valuesLength])
  have readP0 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice RawQM31) point 0#usize = ok p0 := by
    simpa [p0] using vecIndexRun point 0#usize (by simpa [pointLength])
  have readP1 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice RawQM31) point 1#usize = ok p1 := by
    simpa [p1] using vecIndexRun point 1#usize (by simpa [pointLength])
  have cv0 : GeneratedCanonicalQM31 v0 :=
    valuesCanonical 0 (by simpa [valuesLength])
  have cv1 : GeneratedCanonicalQM31 v1 :=
    valuesCanonical 1 (by simpa [valuesLength])
  have cv2 : GeneratedCanonicalQM31 v2 :=
    valuesCanonical 2 (by simpa [valuesLength])
  have cv3 : GeneratedCanonicalQM31 v3 :=
    valuesCanonical 3 (by simpa [valuesLength])
  have p0Bound : 0 < point.val.length := by omega
  have p1Bound : 1 < point.val.length := by omega
  have p0Exact : point.val[0] = p0 := by
    symm
    apply List.getElem!_of_getElem?
    simpa using p0Bound
  have p1Exact : point.val[1] = p1 := by
    symm
    apply List.getElem!_of_getElem?
    simpa using p1Bound
  have cp0 : GeneratedCanonicalQM31 p0 := by
    rw [← p0Exact]
    exact pointCanonical point.val[0] (List.getElem_mem p0Bound)
  have cp1 : GeneratedCanonicalQM31 p1 := by
    rw [← p1Exact]
    exact pointCanonical point.val[1] (List.getElem_mem p1Bound)
  obtain ⟨d10, hd10, cd10, ed10⟩ :=
    generated_qm31_sub_corresponds v1 v0 cv1 cv0
  obtain ⟨p1d10, hp1d10, cp1d10, ep1d10⟩ :=
    generated_qm31_mul_corresponds p1 d10 cp1 cd10
  obtain ⟨low, hlow, clow, elow⟩ :=
    generated_qm31_add_corresponds v0 p1d10 cv0 cp1d10
  obtain ⟨d32, hd32, cd32, ed32⟩ :=
    generated_qm31_sub_corresponds v3 v2 cv3 cv2
  obtain ⟨p1d32, hp1d32, cp1d32, ep1d32⟩ :=
    generated_qm31_mul_corresponds p1 d32 cp1 cd32
  obtain ⟨high, hhigh, chigh, ehigh⟩ :=
    generated_qm31_add_corresponds v2 p1d32 cv2 cp1d32
  obtain ⟨dh, hdh, cdh, edh⟩ :=
    generated_qm31_sub_corresponds high low chigh clow
  obtain ⟨p0dh, hp0dh, cp0dh, ep0dh⟩ :=
    generated_qm31_mul_corresponds p0 dh cp0 cdh
  obtain ⟨interpolated, hinterpolated, cinterpolated, einterpolated⟩ :=
    generated_qm31_add_corresponds low p0dh clow cp0dh
  obtain ⟨out, hout, cout, eout⟩ :=
    generated_qm31_mul_corresponds scale interpolated scaleCanonical
      cinterpolated
  refine ⟨out, ?_, cout, ?_⟩
  · simp [sumcheck.WeightAccumulator.impl.dot_terminal_component,
      readV0, readV1, readV2, readV3, readP0, readP1, hd10, hp1d10, hlow,
      hd32, hp1d32, hhigh, hdh, hp0dh, hinterpolated, hout]
  · rw [eout, einterpolated, ep0dh, edh, ehigh, ep1d32, ed32,
      elow, ep1d10, ed10]
    simp only [sourceQm31ToModel_mul, sourceQm31ToModel_add,
      sourceQm31ToModel_sub]
    unfold multilinearTerminal
    change _ = exactRaw scale *
      ((1 - exactRaw p0) * (1 - exactRaw p1) * exactRaw v0 +
       (1 - exactRaw p0) * exactRaw p1 * exactRaw v1 +
       exactRaw p0 * (1 - exactRaw p1) * exactRaw v2 +
       exactRaw p0 * exactRaw p1 * exactRaw v3)
    unfold exactRaw
    ring

theorem dot_terminal_tensor_corresponds
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (values : Slice RawQM31)
    (scaleCanonical : GeneratedCanonicalQM31 scale)
    (factorsCanonical :
      V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList factors.val)
    (factorsLength : factors.val.length = 2)
    (valuesCanonical : CanonicalSlice values)
    (valuesLength : values.length = 4) :
    ∃ out,
      sumcheck.WeightAccumulator.impl.dot_terminal_component
          (.Tensor scale factors) values = ok out ∧
      GeneratedCanonicalQM31 out ∧
      sourceQm31ToModel (generatedQm31ToExact out) =
        tensorTerminal scale factors.val[0]! factors.val[1]! values := by
  let v0 := values.val[0]!
  let v1 := values.val[1]!
  let v2 := values.val[2]!
  let v3 := values.val[3]!
  let f0 := factors.val[0]!
  let f1 := factors.val[1]!
  have readV0 : Slice.index_usize values 0#usize = ok v0 := by
    simpa [v0] using sliceIndexRun values 0#usize (by simpa [valuesLength])
  have readV1 : Slice.index_usize values 1#usize = ok v1 := by
    simpa [v1] using sliceIndexRun values 1#usize (by simpa [valuesLength])
  have readV2 : Slice.index_usize values 2#usize = ok v2 := by
    simpa [v2] using sliceIndexRun values 2#usize (by simpa [valuesLength])
  have readV3 : Slice.index_usize values 3#usize = ok v3 := by
    simpa [v3] using sliceIndexRun values 3#usize (by simpa [valuesLength])
  have readF0 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice RawQM31) factors 0#usize = ok f0 := by
    simpa [f0] using vecIndexRun factors 0#usize (by simpa [factorsLength])
  have readF1 : alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice RawQM31) factors 1#usize = ok f1 := by
    simpa [f1] using vecIndexRun factors 1#usize (by simpa [factorsLength])
  have cv0 : GeneratedCanonicalQM31 v0 :=
    valuesCanonical 0 (by simpa [valuesLength])
  have cv1 : GeneratedCanonicalQM31 v1 :=
    valuesCanonical 1 (by simpa [valuesLength])
  have cv2 : GeneratedCanonicalQM31 v2 :=
    valuesCanonical 2 (by simpa [valuesLength])
  have cv3 : GeneratedCanonicalQM31 v3 :=
    valuesCanonical 3 (by simpa [valuesLength])
  have f0Bound : 0 < factors.val.length := by omega
  have f1Bound : 1 < factors.val.length := by omega
  have f0Exact : factors.val[0] = f0 := by
    symm
    apply List.getElem!_of_getElem?
    simpa using f0Bound
  have f1Exact : factors.val[1] = f1 := by
    symm
    apply List.getElem!_of_getElem?
    simpa using f1Bound
  have cf0 : GeneratedCanonicalQM31 f0 := by
    rw [← f0Exact]
    exact factorsCanonical factors.val[0] (List.getElem_mem f0Bound)
  have cf1 : GeneratedCanonicalQM31 f1 := by
    rw [← f1Exact]
    exact factorsCanonical factors.val[1] (List.getElem_mem f1Bound)
  obtain ⟨f1v1, hf1v1, cf1v1, ef1v1⟩ :=
    generated_qm31_mul_corresponds f1 v1 cf1 cv1
  obtain ⟨low, hlow, clow, elow⟩ :=
    generated_qm31_add_corresponds v0 f1v1 cv0 cf1v1
  obtain ⟨f1v3, hf1v3, cf1v3, ef1v3⟩ :=
    generated_qm31_mul_corresponds f1 v3 cf1 cv3
  obtain ⟨high, hhigh, chigh, ehigh⟩ :=
    generated_qm31_add_corresponds v2 f1v3 cv2 cf1v3
  obtain ⟨f0high, hf0high, cf0high, ef0high⟩ :=
    generated_qm31_mul_corresponds f0 high cf0 chigh
  obtain ⟨combined, hcombined, ccombined, ecombined⟩ :=
    generated_qm31_add_corresponds low f0high clow cf0high
  obtain ⟨out, hout, cout, eout⟩ :=
    generated_qm31_mul_corresponds scale combined scaleCanonical ccombined
  refine ⟨out, ?_, cout, ?_⟩
  · simp [sumcheck.WeightAccumulator.impl.dot_terminal_component,
      readV0, readV1, readV2, readV3, readF0, readF1, hf1v1, hlow,
      hf1v3, hhigh, hf0high, hcombined, hout]
  · rw [eout, ecombined, ef0high, ehigh, ef1v3, elow, ef1v1]
    simp only [sourceQm31ToModel_mul, sourceQm31ToModel_add]
    unfold tensorTerminal
    change _ = exactRaw scale *
      (exactRaw v0 + exactRaw f1 * exactRaw v1 +
       exactRaw f0 * exactRaw v2 + exactRaw f0 * exactRaw f1 * exactRaw v3)
    unfold exactRaw
    ring

#print axioms dot_terminal_multilinear_corresponds
#print axioms dot_terminal_tensor_corresponds

end V7CallerCurrentReleaseR26TerminalStructuredComponents
