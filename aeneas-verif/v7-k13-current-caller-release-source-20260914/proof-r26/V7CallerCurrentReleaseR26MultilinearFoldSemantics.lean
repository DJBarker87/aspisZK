import V7CallerCurrentReleaseR26HalfBridge

/-!
# Exact semantics of the current multilinear arity-four fold

The optimized relation-tail traversal repeatedly calls the generated
multilinear helper.  This file proves that helper consumes the final two point
coordinates and multiplies the component scale by the exact dual fold of the
four multilinear basis weights.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26MultilinearFoldSemantics

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26HalfBridge

abbrev RawQM31 := field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawQM31 := ⟨field.QM31.ZERO⟩

def CanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, GeneratedCanonicalQM31 value

def multilinearFibreWeights
    (z0 z1 : ExactQM31) : Fin 4 → ExactQM31 :=
  ![(1 - z0) * (1 - z1),
    (1 - z0) * z1,
    z0 * (1 - z1),
    z0 * z1]

def sourceDualWeightFoldNumerator
    (alpha : ExactQM31) (weights : Fin 4 → ExactQM31) : ExactQM31 :=
  weights 0 + alpha ^ 3 * weights 1 + alpha ^ 2 * weights 2 +
    alpha * weights 3

def multilinearDualNumerator
    (alpha z0 z1 : ExactQM31) : ExactQM31 :=
  sourceDualWeightFoldNumerator alpha (multilinearFibreWeights z0 z1)

private theorem vecIndexRun
    (values : alloc.vec.Vec RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) values index =
      ok values.val[index.val] := by
  obtain ⟨value, run, valueEq⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values index hindex)
  simpa [valueEq] using run

private theorem wrappingSubTwoExact
    (length : Std.Usize) (m : Nat)
    (hlength : length.val = m + 2) (hm : m ≤ 8) :
    (Std.Usize.wrapping_sub length 2#usize).val = m := by
  rw [Std.Usize.wrapping_sub_val_eq]
  norm_num
  rw [hlength]
  have hsize : 10 < Std.Usize.size := by
    have literalBound := (11#usize).hSize
    scalar_tac
  have rearrange : m + 2 + (Std.Usize.size - 2) =
      m + Std.Usize.size := by omega
  rw [rearrange, Nat.add_mod_right, Nat.mod_eq_of_lt]
  omega

private theorem wrappingAddOneExact
    (index : Std.Usize) (m : Nat)
    (hindex : index.val = m) (hm : m ≤ 8) :
    (Std.Usize.wrapping_add index 1#usize).val = m + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  norm_num
  rw [Nat.mod_eq_of_lt, hindex]
  have hsize : 10 < Std.Usize.size := by
    have literalBound := (11#usize).hSize
    scalar_tac
  omega

private theorem oneCanonical : GeneratedCanonicalQM31 field.QM31.ONE := by
  simp only [GeneratedCanonicalQM31, GeneratedCanonicalCM31, field.QM31.ONE]
  repeat' constructor <;> norm_num

private theorem oneExact : generatedQm31ToExact field.QM31.ONE = 1 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      norm_num [generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ONE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply QuadraticAlgebra.ext <;>
      norm_num [generatedQm31ToExact, generatedCm31ToExact,
        field.QM31.ONE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem takeCanonical
    (values : List RawQM31) (m : Nat)
    (canonical : CanonicalList values) :
    CanonicalList (values.take m) := by
  intro value member
  exact canonical value (List.mem_of_mem_take member)

/-- The current generated multilinear fold has the exact maintained-field
meaning of an arity-four dual fold. -/
theorem fold_multilinear_arity4_exact
    (scale : RawQM31) (point : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31) (m : Nat)
    (hpointLength : point.val.length = m + 2)
    (hm : m ≤ 8)
    (hscale : GeneratedCanonicalQM31 scale)
    (hpoint : CanonicalList point.val)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (halpha2Exact : generatedQm31ToExact alpha2 =
      generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 =
      generatedQm31ToExact alpha ^ 3) :
    ∃ scaleOut pointOut factorExact,
      sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
          scale point alpha alpha2 alpha3 = ok (scaleOut, pointOut) ∧
      GeneratedCanonicalQM31 scaleOut ∧
      CanonicalList pointOut.val ∧
      pointOut.val = point.val.take m ∧
      generatedQm31ToExact scaleOut =
        generatedQm31ToExact scale * factorExact ∧
      factorExact * (4 : ExactQM31) =
        multilinearDualNumerator (generatedQm31ToExact alpha)
          (generatedQm31ToExact point.val[m]!)
          (generatedQm31ToExact point.val[m + 1]!) := by
  let split := Std.Usize.wrapping_sub (alloc.vec.Vec.len point) 2#usize
  have hlen : (alloc.vec.Vec.len point).val = m + 2 := by
    rw [alloc.vec.Vec.len_val]
    exact hpointLength
  have hsplit : split.val = m := by
    unfold split
    exact wrappingSubTwoExact (alloc.vec.Vec.len point) m hlen hm
  let next := Std.Usize.wrapping_add split 1#usize
  have hnext : next.val = m + 1 := by
    unfold next
    exact wrappingAddOneExact split m hsplit hm
  have hsplitBound : split.val < point.val.length := by omega
  have hnextBound : next.val < point.val.length := by omega
  have read0 := vecIndexRun point split hsplitBound
  have read1 := vecIndexRun point next hnextBound
  have z0Canonical := hpoint point.val[split.val]
    (List.getElem_mem hsplitBound)
  have z1Canonical := hpoint point.val[next.val]
    (List.getElem_mem hnextBound)
  let one := field.QM31.ONE
  obtain ⟨q, qRun, qCanonical, qExact⟩ :=
    generated_qm31_sub_corresponds alpha3 one halpha3 oneCanonical
  obtain ⟨q1, q1Run, q1Canonical, q1Exact⟩ :=
    generated_qm31_mul_corresponds q point.val[next.val]
      qCanonical z1Canonical
  obtain ⟨low, lowRun, lowCanonical, lowExact⟩ :=
    generated_qm31_add_corresponds one q1 oneCanonical q1Canonical
  obtain ⟨q2, q2Run, q2Canonical, q2Exact⟩ :=
    generated_qm31_sub_corresponds alpha alpha2 halpha halpha2
  obtain ⟨q3, q3Run, q3Canonical, q3Exact⟩ :=
    generated_qm31_mul_corresponds q2 point.val[next.val]
      q2Canonical z1Canonical
  obtain ⟨high, highRun, highCanonical, highExact⟩ :=
    generated_qm31_add_corresponds alpha2 q3 halpha2 q3Canonical
  obtain ⟨q4, q4Run, q4Canonical, q4Exact⟩ :=
    generated_qm31_sub_corresponds high low highCanonical lowCanonical
  obtain ⟨q5, q5Run, q5Canonical, q5Exact⟩ :=
    generated_qm31_mul_corresponds point.val[split.val] q4
      z0Canonical q4Canonical
  obtain ⟨q6, q6Run, q6Canonical, q6Exact⟩ :=
    generated_qm31_add_corresponds low q5 lowCanonical q5Canonical
  obtain ⟨q7, q7Run, q7Canonical, q7Exact⟩ :=
    generated_qm31_half_corresponds q6 q6Canonical
  obtain ⟨factor, factorRun, factorCanonical, factorExact⟩ :=
    generated_qm31_half_corresponds q7 q7Canonical
  obtain ⟨scaleOut, scaleRun, scaleCanonical, scaleExact⟩ :=
    generated_qm31_mul_corresponds scale factor hscale factorCanonical
  let pointOut : alloc.vec.Vec RawQM31 :=
    ⟨point.val.take split.val,
      Nat.le_trans (List.length_take_le' ..) point.property⟩
  refine ⟨scaleOut, pointOut, generatedQm31ToExact factor,
    ?_, scaleCanonical, ?_, ?_, scaleExact, ?_⟩
  · unfold sumcheck.WeightAccumulator.impl.fold_multilinear_arity4
    simp only [Std.lift, bind_tc_ok]
    change (do
      let z0 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) point split
      let z1 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) point next
      let q ← field.QM31.sub alpha3 one
      let q1 ← field.QM31.mul q z1
      let low ← field.QM31.add one q1
      let q2 ← field.QM31.sub alpha alpha2
      let q3 ← field.QM31.mul q2 z1
      let high ← field.QM31.add alpha2 q3
      let q4 ← field.QM31.sub high low
      let q5 ← field.QM31.mul z0 q4
      let q6 ← field.QM31.add low q5
      let q7 ← field.QM31.half q6
      let factor ← field.QM31.half q7
      let scale1 ← field.QM31.mul scale factor
      let point1 ← alloc.vec.Vec.truncate Global point split
      ok (scale1, point1)) = ok (scaleOut, pointOut)
    rw [read0, read1]
    simp only [bind_tc_ok]
    rw [qRun]
    simp only [bind_tc_ok]
    rw [q1Run]
    simp only [bind_tc_ok]
    rw [lowRun]
    simp only [bind_tc_ok]
    rw [q2Run]
    simp only [bind_tc_ok]
    rw [q3Run]
    simp only [bind_tc_ok]
    rw [highRun]
    simp only [bind_tc_ok]
    rw [q4Run]
    simp only [bind_tc_ok]
    rw [q5Run]
    simp only [bind_tc_ok]
    rw [q6Run]
    simp only [bind_tc_ok]
    rw [q7Run]
    simp only [bind_tc_ok]
    rw [factorRun]
    simp only [bind_tc_ok]
    rw [scaleRun]
    rfl
  · unfold pointOut
    apply takeCanonical point.val split.val hpoint
  · simp [pointOut, hsplit]
  · simp [multilinearDualNumerator, sourceDualWeightFoldNumerator,
      multilinearFibreWeights]
    calc
      generatedQm31ToExact factor * 4 =
          (generatedQm31ToExact factor + generatedQm31ToExact factor) +
            (generatedQm31ToExact factor + generatedQm31ToExact factor) := by
              ring
      _ = generatedQm31ToExact q7 + generatedQm31ToExact q7 := by
        rw [factorExact]
      _ = generatedQm31ToExact q6 := q7Exact
      _ = generatedQm31ToExact low + generatedQm31ToExact q5 := q6Exact
      _ = generatedQm31ToExact low +
          generatedQm31ToExact point.val[split.val] *
            generatedQm31ToExact q4 := by rw [q5Exact]
      _ = generatedQm31ToExact low +
          generatedQm31ToExact point.val[split.val] *
            (generatedQm31ToExact high - generatedQm31ToExact low) := by
              rw [q4Exact]
      _ = (1 + (generatedQm31ToExact alpha ^ 3 - 1) *
              generatedQm31ToExact point.val[next.val]) +
          generatedQm31ToExact point.val[split.val] *
            ((generatedQm31ToExact alpha ^ 2 +
                (generatedQm31ToExact alpha - generatedQm31ToExact alpha ^ 2) *
                  generatedQm31ToExact point.val[next.val]) -
              (1 + (generatedQm31ToExact alpha ^ 3 - 1) *
                generatedQm31ToExact point.val[next.val])) := by
        rw [lowExact, q1Exact, qExact, highExact, q3Exact, q2Exact,
          oneExact, halpha2Exact, halpha3Exact]
      _ =
          (1 - generatedQm31ToExact ((point.val[m]?).getD default)) *
              (1 - generatedQm31ToExact ((point.val[m + 1]?).getD default)) +
            generatedQm31ToExact alpha ^ 3 *
              ((1 - generatedQm31ToExact ((point.val[m]?).getD default)) *
                generatedQm31ToExact ((point.val[m + 1]?).getD default)) +
            generatedQm31ToExact alpha ^ 2 *
              (generatedQm31ToExact ((point.val[m]?).getD default) *
                (1 - generatedQm31ToExact ((point.val[m + 1]?).getD default))) +
            generatedQm31ToExact alpha *
              (generatedQm31ToExact ((point.val[m]?).getD default) *
                generatedQm31ToExact ((point.val[m + 1]?).getD default)) := by
        have hmBound : m < point.val.length := by omega
        have hm1Bound : m + 1 < point.val.length := by omega
        have splitGetD : (point.val[m]?).getD default =
            point.val[split.val] := by
          rw [List.getElem?_eq_getElem hmBound, Option.getD_some]
          simp only [hsplit]
        have nextGetD : (point.val[m + 1]?).getD default =
            point.val[next.val] := by
          rw [List.getElem?_eq_getElem hm1Bound, Option.getD_some]
          simp only [hnext]
        rw [splitGetD, nextGetD]
        ring

#print axioms fold_multilinear_arity4_exact

end V7CallerCurrentReleaseR26MultilinearFoldSemantics
