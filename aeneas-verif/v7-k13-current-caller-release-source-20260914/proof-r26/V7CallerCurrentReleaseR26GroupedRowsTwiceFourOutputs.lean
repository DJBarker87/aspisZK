import V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalBasis
import V7CallerCurrentReleaseR26GroupedRowsSemantics

/-! # Exact four outputs of the fused grouped fold

The four source loop steps are matched to the symbolic chunk evaluations.
This is the final operational layer before the result is related to the K1
two-fold semantics.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26GroupedRowsTwiceFourOutputs

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26GroupedRows
open V7CallerCurrentReleaseR26GroupedRowsSemantics
open V7CallerCurrentReleaseR26GroupedRowsTwiceTrace
open V7CallerCurrentReleaseR26GroupedRowsTwiceFourTrace
open V7CallerCurrentReleaseR26GroupedRowsTwiceChunkOutput
open V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalOps
open V7CallerCurrentReleaseR26GroupedRowsTwiceCanonicalBasis

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

structure FourOutputs
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31)
    (source : GroupedRowsTwiceSourceTrace
      (alloc.vec.Vec.deref releasedRowGroups64)
      (alloc.vec.Vec.deref
        (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
      alpha1 alpha2 foldedGroups foldedValues) : Type where
  basis : CanonicalBasis source
  out0 : CanonicalRaw
  out1 : CanonicalRaw
  out2 : CanonicalRaw
  out3 : CanonicalRaw
  valuesExact : foldedValues.val = [out0.raw, out1.raw, out2.raw, out3.raw]
  out0Exact : 16 * exact out0 =
    generatedQm31ToExact value0 * (exact basis.b0 + exact basis.b1) +
    generatedQm31ToExact value1 *
      (exact basis.b2 + exact basis.b3 + exact basis.b4 + exact basis.b5 +
       exact basis.b6 + exact basis.b7 + exact basis.b8 + exact basis.b9 +
       exact basis.b10 + exact basis.b11 + exact basis.b12 + exact basis.b13 +
       exact basis.b14 + exact basis.b15)
  out1Exact : 16 * exact out1 =
    generatedQm31ToExact value1 *
      (exact basis.b0 + exact basis.b1 + exact basis.b2 + exact basis.b3 +
       exact basis.b4 + exact basis.b5 + exact basis.b6 + exact basis.b8 +
       exact basis.b9 + exact basis.b10 + exact basis.b11 + exact basis.b12 +
       exact basis.b13 + exact basis.b14 + exact basis.b15) +
    generatedQm31ToExact value2 * exact basis.b7
  out2Exact : 16 * exact out2 =
    generatedQm31ToExact value1 *
      (exact basis.b0 + exact basis.b1 + exact basis.b2 + exact basis.b3 +
       exact basis.b4 + exact basis.b5 + exact basis.b6 + exact basis.b7 +
       exact basis.b8 + exact basis.b9 + exact basis.b10 + exact basis.b15) +
    generatedQm31ToExact value2 *
      (exact basis.b11 + exact basis.b13) +
    generatedQm31ToExact value0 *
      (exact basis.b12 + exact basis.b14)
  out3Exact : 16 * exact out3 =
    generatedQm31ToExact value1 +
    generatedQm31ToExact value3 *
      (exact basis.b1 + exact basis.b2 + exact basis.b3 + exact basis.b4) +
    generatedQm31ToExact value4 * exact basis.b5 +
    generatedQm31ToExact value5 * exact basis.b6 +
    generatedQm31ToExact value6 *
      (exact basis.b7 + exact basis.b8 + exact basis.b9 + exact basis.b10 +
       exact basis.b11 + exact basis.b12 + exact basis.b13 + exact basis.b14 +
       exact basis.b15)

private theorem usizeMaxPositive (n : Nat) (hn : n ≤ 4) : n < Std.Usize.max := by
  rcases Usize.cMax_bound_concrete with ⟨hmax, _⟩
  omega

theorem source_exposes_four_outputs
    (value0 value1 value2 value3 value4 value5 value6 : RawQM31)
    (alpha1 alpha2 : RawQM31)
    (foldedGroups : alloc.vec.Vec Std.U8)
    (foldedValues : alloc.vec.Vec RawQM31)
    (valuesCanonical : CanonicalSeven value0 value1 value2 value3 value4 value5 value6)
    (alpha1Canonical : GeneratedCanonicalQM31 alpha1)
    (alpha2Canonical : GeneratedCanonicalQM31 alpha2)
    (source : GroupedRowsTwiceSourceTrace
      (alloc.vec.Vec.deref releasedRowGroups64)
      (alloc.vec.Vec.deref
        (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
      alpha1 alpha2 foldedGroups foldedValues) :
    Nonempty (FourOutputs value0 value1 value2 value3 value4 value5 value6
      alpha1 alpha2 foldedGroups foldedValues source) := by
  rcases valuesCanonical with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨basis⟩ := source_basis_is_canonical_tensor source
    alpha1Canonical alpha2Canonical
  obtain ⟨four⟩ := released_outer_trace_exposes_four_chunks
    (alloc.vec.Vec.deref
      (releasedSevenValues value0 value1 value2 value3 value4 value5 value6))
    alpha1 alpha2 foldedGroups foldedValues source
  let groupValues := alloc.vec.Vec.deref
    (releasedSevenValues value0 value1 value2 value3 value4 value5 value6)
  let g0 : CanonicalRaw := ⟨value0, h0⟩
  let g1 : CanonicalRaw := ⟨value1, h1⟩
  let g2 : CanonicalRaw := ⟨value2, h2⟩
  let g3 : CanonicalRaw := ⟨value3, h3⟩
  let g4 : CanonicalRaw := ⟨value4, h4⟩
  let g5 : CanonicalRaw := ⟨value5, h5⟩
  let g6 : CanonicalRaw := ⟨value6, h6⟩
  have read0 : Slice.index_usize groupValues 0#usize = ok value0 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  have read1 : Slice.index_usize groupValues 1#usize = ok value1 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  have read2 : Slice.index_usize groupValues 2#usize = ok value2 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  have read3 : Slice.index_usize groupValues 3#usize = ok value3 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  have read4 : Slice.index_usize groupValues 4#usize = ok value4 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  have read5 : Slice.index_usize groupValues 5#usize = ok value5 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  have read6 : Slice.index_usize groupValues 6#usize = ok value6 := by
    simp [groupValues, releasedSevenValues,
      V7CallerCurrentReleaseR26GroupedRowsStaged.releasedSevenValuesStaged,
      alloc.vec.Vec.deref, Slice.index_usize]
  let eval0 := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0Evaluation.evaluation
    groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
    basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
    basis.b13 basis.b14 basis.b15 g0 g1 read0 read1
  let eval1 := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1Evaluation.evaluation
    groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
    basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
    basis.b13 basis.b14 basis.b15 g1 g2 read1 read2
  let eval2 := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2Evaluation.evaluation
    groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
    basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
    basis.b13 basis.b14 basis.b15 g0 g1 g2 read0 read1 read2
  let eval3 := V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3Evaluation.evaluation
    groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
    basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
    basis.b13 basis.b14 basis.b15 g1 g3 g4 g5 g6
    read1 read3 read4 read5 read6
  have match0 := optimized_chunk_output_exact
    groupValues source.basis
    (iter0, emptyValues) (iter1, four.values1) four.step0
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groupsAB
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficientsAB
      eval0.coefficientTrace.a0 eval0.coefficientTrace.c15)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.countsAB 2#u8 14#u8)
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.slotsAB 2#usize
    eval0.contributionTrace.sum1 eval0.half1.raw eval0.half2.raw
    eval0.half3.raw eval0.half4.raw (by
      simp [emptyValues]
      exact usizeMaxPositive 0 (by omega))
    (by simpa [basis.basisExact, four.chunk0Exact,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groups0,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficients0] using
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.chunk0_aggregation_exact
        basis.b0.raw basis.b1.raw basis.b2.raw basis.b3.raw basis.b4.raw
        basis.b5.raw basis.b6.raw basis.b7.raw basis.b8.raw basis.b9.raw
        basis.b10.raw basis.b11.raw basis.b12.raw basis.b13.raw
        basis.b14.raw basis.b15.raw eval0.coefficientTrace))
    (V7CallerCurrentReleaseR26GroupedRowsTwiceContributions.chunk0_contribution_exact
      groupValues eval0.coefficientTrace.a0 eval0.coefficientTrace.c15
      eval0.contributionTrace)
    eval0.half1Run eval0.half2Run eval0.half3Run eval0.half4Run
  have values1Exact : four.values1.val = [eval0.half4.raw] := by
    have same := congrArg (fun state => state.2) four.step0.successorExact
    calc
      four.values1.val = four.step0.nextValues.val := congrArg Subtype.val same
      _ = emptyValues.val ++ [eval0.half4.raw] := match0.nextValuesExact
      _ = [eval0.half4.raw] := by rfl
  have match1 := optimized_chunk_output_exact
    groupValues source.basis
    (iter1, four.values1) (iter2, four.values2) four.step1
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.uniqueAB
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.coefficients
      eval1.coefficientTrace.c15 basis.b7.raw)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.counts 15#u8 1#u8)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.firstSlots 0#u8 7#u8)
    2#usize eval1.contributionTrace.sum1 eval1.half1.raw eval1.half2.raw
    eval1.half3.raw eval1.half4.raw (by
      rw [values1Exact]
      exact usizeMaxPositive 1 (by omega))
    (by simpa [basis.basisExact, four.chunk1Exact,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groups0,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficients0] using
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1.chunk1_aggregation_exact
        basis.b0.raw basis.b1.raw basis.b2.raw basis.b3.raw basis.b4.raw
        basis.b5.raw basis.b6.raw basis.b7.raw basis.b8.raw basis.b9.raw
        basis.b10.raw basis.b11.raw basis.b12.raw basis.b13.raw
        basis.b14.raw basis.b15.raw eval1.coefficientTrace))
    (V7CallerCurrentReleaseR26GroupedRowsTwiceContributions.chunk1_contribution_exact
      groupValues eval1.coefficientTrace.c15 basis.b7.raw
      eval1.contributionTrace)
    eval1.half1Run eval1.half2Run eval1.half3Run eval1.half4Run
  have values2Exact : four.values2.val =
      [eval0.half4.raw, eval1.half4.raw] := by
    have same := congrArg (fun state => state.2) four.step1.successorExact
    calc
      four.values2.val = four.step1.nextValues.val := congrArg Subtype.val same
      _ = four.values1.val ++ [eval1.half4.raw] := match1.nextValuesExact
      _ = [eval0.half4.raw, eval1.half4.raw] := by
        simp [values1Exact]
  have match2 := optimized_chunk_output_exact
    groupValues source.basis
    (iter2, four.values2) (iter3, four.values3) four.step2
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.uniqueABC
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.coefficients
      eval2.coefficientTrace.c15 eval2.coefficientTrace.d13
      eval2.coefficientTrace.e14)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.counts 12#u8 2#u8 2#u8)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.firstSlots
      0#u8 11#u8 12#u8) 3#usize eval2.contributionTrace.sum2
    eval2.half1.raw eval2.half2.raw eval2.half3.raw eval2.half4.raw (by
      rw [values2Exact]
      exact usizeMaxPositive 2 (by omega))
    (by simpa [basis.basisExact, four.chunk2Exact,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groups0,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficients0] using
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2.chunk2_aggregation_exact
        basis.b0.raw basis.b1.raw basis.b2.raw basis.b3.raw basis.b4.raw
        basis.b5.raw basis.b6.raw basis.b7.raw basis.b8.raw basis.b9.raw
        basis.b10.raw basis.b11.raw basis.b12.raw basis.b13.raw
        basis.b14.raw basis.b15.raw eval2.coefficientTrace))
    (V7CallerCurrentReleaseR26GroupedRowsTwiceContributions.chunk2_contribution_exact
      groupValues eval2.coefficientTrace.c15 eval2.coefficientTrace.d13
      eval2.coefficientTrace.e14 eval2.contributionTrace)
    eval2.half1Run eval2.half2Run eval2.half3Run eval2.half4Run
  have values3Exact : four.values3.val =
      [eval0.half4.raw, eval1.half4.raw, eval2.half4.raw] := by
    have same := congrArg (fun state => state.2) four.step2.successorExact
    calc
      four.values3.val = four.step2.nextValues.val := congrArg Subtype.val same
      _ = four.values2.val ++ [eval2.half4.raw] := match2.nextValuesExact
      _ = [eval0.half4.raw, eval1.half4.raw, eval2.half4.raw] := by
        simp [values2Exact]
  have match3 := optimized_chunk_output_exact
    groupValues source.basis
    (iter3, four.values3) (iter4, four.values4) four.step3
    V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.unique13456
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.coefficients
      basis.b0.raw eval3.coefficientTrace.c4 basis.b5.raw basis.b6.raw
      eval3.coefficientTrace.d15)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.counts
      1#u8 4#u8 1#u8 1#u8 9#u8)
    (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.firstSlots
      0#u8 1#u8 5#u8 6#u8 7#u8) 5#usize eval3.contributionTrace.sum4
    eval3.half1.raw eval3.half2.raw eval3.half3.raw eval3.half4.raw (by
      rw [values3Exact]
      exact usizeMaxPositive 3 (by omega))
    (by simpa [basis.basisExact, four.chunk3Exact,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.groups0,
        V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0.coefficients0] using
      (V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3.chunk3_aggregation_exact
        basis.b0.raw basis.b1.raw basis.b2.raw basis.b3.raw basis.b4.raw
        basis.b5.raw basis.b6.raw basis.b7.raw basis.b8.raw basis.b9.raw
        basis.b10.raw basis.b11.raw basis.b12.raw basis.b13.raw
        basis.b14.raw basis.b15.raw eval3.coefficientTrace))
    (V7CallerCurrentReleaseR26GroupedRowsTwiceContributions.chunk3_contribution_exact
      groupValues basis.b0.raw eval3.coefficientTrace.c4 basis.b5.raw
      basis.b6.raw eval3.coefficientTrace.d15 eval3.contributionTrace)
    eval3.half1Run eval3.half2Run eval3.half3Run eval3.half4Run
  have values4Exact : four.values4.val =
      [eval0.half4.raw, eval1.half4.raw, eval2.half4.raw,
       eval3.half4.raw] := by
    have same := congrArg (fun state => state.2) four.step3.successorExact
    calc
      four.values4.val = four.step3.nextValues.val := congrArg Subtype.val same
      _ = four.values3.val ++ [eval3.half4.raw] := match3.nextValuesExact
      _ = [eval0.half4.raw, eval1.half4.raw, eval2.half4.raw,
          eval3.half4.raw] := by simp [values3Exact]
  refine ⟨{
    basis := basis
    out0 := eval0.half4, out1 := eval1.half4
    out2 := eval2.half4, out3 := eval3.half4
    valuesExact := by
      calc
        foldedValues.val = four.values4.val := congrArg Subtype.val four.outputExact
        _ = _ := values4Exact
    out0Exact := ?_
    out1Exact := ?_
    out2Exact := ?_
    out3Exact := ?_ }⟩
  · simpa only [eval0, g0, g1, exact] using
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk0Evaluation.output_exact
        groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
        basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
        basis.b13 basis.b14 basis.b15 g0 g1 read0 read1
  · simpa only [eval1, g1, g2, exact] using
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk1Evaluation.output_exact
        groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
        basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
        basis.b13 basis.b14 basis.b15 g1 g2 read1 read2
  · simpa only [eval2, g0, g1, g2, exact] using
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk2Evaluation.output_exact
        groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
        basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
        basis.b13 basis.b14 basis.b15 g0 g1 g2 read0 read1 read2
  · simpa only [eval3, g1, g3, g4, g5, g6, exact] using
      V7CallerCurrentReleaseR26GroupedRowsTwiceChunk3Evaluation.output_exact
        groupValues basis.b0 basis.b1 basis.b2 basis.b3 basis.b4 basis.b5
        basis.b6 basis.b7 basis.b8 basis.b9 basis.b10 basis.b11 basis.b12
        basis.b13 basis.b14 basis.b15 g1 g3 g4 g5 g6
        read1 read3 read4 read5 read6

#print axioms source_exposes_four_outputs

end V7CallerCurrentReleaseR26GroupedRowsTwiceFourOutputs
