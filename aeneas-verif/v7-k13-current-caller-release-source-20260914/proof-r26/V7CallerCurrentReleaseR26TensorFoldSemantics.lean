import V7CallerCurrentReleaseR26PreparedSumSemantics
import V7CallerCurrentReleaseR26HalfBridge

/-!
# Exact tensor fold for the linked V5 relation verifier

This file connects the extracted compact tensor branch to the maintained
four-point dual weight fold.  In particular, the proof passes through the
actual prepared-multiplier cache and the actual fused two-product helper.
-/

namespace V7CallerCurrentReleaseR26TensorFoldSemantics

open Aeneas Aeneas.Std Result
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26HalfBridge
open V7CallerCurrentReleaseR26PreparedSumSemantics

abbrev RawQM31 := V7CallerCurrentReleaseR26.field.QM31
abbrev RawPrepared :=
  V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier
abbrev ExactQM31 := V7CallerCurrentReleaseR26FieldBridge.ExactQM31

local instance : Inhabited RawQM31 :=
  ⟨V7CallerCurrentReleaseR26.field.QM31.ZERO⟩
local instance : Inhabited RawPrepared :=
  ⟨⟨Array.repeat 3#usize (Array.repeat 3#usize 0#u32)⟩⟩

def CanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, GeneratedCanonicalQM31 value

def listCell (values : List RawQM31) (index : Nat) : RawQM31 :=
  (values[index]?).getD default

/-- The four tensor weights in the production bit order. -/
def tensorFibreWeights
    (high low : ExactQM31) : Fin 4 → ExactQM31 :=
  ![1, low, high, high * low]

def tensorDualNumerator
    (alpha high low : ExactQM31) : ExactQM31 :=
  let weights := tensorFibreWeights high low
  weights 0 + alpha ^ 3 * weights 1 + alpha ^ 2 * weights 2 +
    alpha * weights 3

private theorem vecIndexRun
    (values : alloc.vec.Vec RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) values index =
      ok values.val[index.val] := by
  rw [alloc.vec.Vec.index_slice_index]
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
    have h := (11#usize).hSize
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
    have h := (11#usize).hSize
    scalar_tac
  omega

private theorem oneCanonical :
    GeneratedCanonicalQM31 V7CallerCurrentReleaseR26.field.QM31.ONE := by
  norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
    AspisAeneasCM31Multiplicative.CanonicalRawM31,
    V7CallerCurrentReleaseR26.field.QM31.ONE,
    AspisAeneasCM31Multiplicative.m31Modulus]

private theorem oneExact :
    generatedQm31ToExact
        V7CallerCurrentReleaseR26.field.QM31.ONE = 1 := by
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;>
      norm_num [generatedQm31ToExact, generatedCm31ToExact,
        V7CallerCurrentReleaseR26.field.QM31.ONE,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · apply QuadraticAlgebra.ext <;>
      norm_num [generatedQm31ToExact, generatedCm31ToExact,
        V7CallerCurrentReleaseR26.field.QM31.ONE,
        QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem takeCanonical
    (values : List RawQM31) (m : Nat)
    (canonical : CanonicalList values) :
    CanonicalList (values.take m) := by
  intro value member
  exact canonical value (List.mem_of_mem_take member)

private theorem representsPreparedNewRun
    (prepared : RawPrepared) (value : RawQM31)
    (hprepared : RepresentsPrepared prepared value) :
    V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.impl.new value =
      ok prepared := by
  obtain ⟨valueSum, row0, row1, row2, valueSumRun, _valueSumCanonical,
    row0Represents, row1Represents, row2Represents, componentsExact⟩ :=
    hprepared
  obtain ⟨sum0, sum0Run, _sum0Canonical, row0Exact⟩ := row0Represents
  obtain ⟨sum1, sum1Run, _sum1Canonical, row1Exact⟩ := row1Represents
  obtain ⟨sum2, sum2Run, _sum2Canonical, row2Exact⟩ := row2Represents
  unfold V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.impl.new
  simp only [V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
    sum0Run, sum1Run, valueSumRun, sum2Run, bind_tc_ok]
  cases prepared with
  | mk components =>
    have row0Eq : row0 = Array.make 3#usize
        [value.c0.a, value.c0.b, sum0] := by
      apply Subtype.ext
      exact row0Exact
    have row1Eq : row1 = Array.make 3#usize
        [value.c1.a, value.c1.b, sum1] := by
      apply Subtype.ext
      exact row1Exact
    have row2Eq : row2 = Array.make 3#usize
        [valueSum.a, valueSum.b, sum2] := by
      apply Subtype.ext
      exact row2Exact
    subst row0
    subst row1
    subst row2
    have componentsEq : components = Array.make 3#usize
        [Array.make 3#usize [value.c0.a, value.c0.b, sum0],
         Array.make 3#usize [value.c1.a, value.c1.b, sum1],
         Array.make 3#usize [valueSum.a, valueSum.b, sum2]] := by
      apply Subtype.ext
      exact componentsExact
    subst components
    rfl

/-- Exact generated tensor component fold.  The last two factors are consumed
as `high` then `low`, the prefix is retained, and the scale is multiplied by
the maintained dual fold of `[1, low, high, high * low]`. -/
theorem fold_tensor_arity4_exact
    (scale : RawQM31) (factors : alloc.vec.Vec RawQM31)
    (alpha alpha2 alpha3 : RawQM31)
    (preparedAlpha preparedAlpha2 : RawPrepared) (m : Nat)
    (hfactorsLength : factors.val.length = m + 2)
    (hm : m ≤ 8)
    (hscale : GeneratedCanonicalQM31 scale)
    (hfactors : CanonicalList factors.val)
    (halpha : GeneratedCanonicalQM31 alpha)
    (halpha2 : GeneratedCanonicalQM31 alpha2)
    (halpha3 : GeneratedCanonicalQM31 alpha3)
    (hpreparedAlpha : RepresentsPrepared preparedAlpha alpha)
    (hpreparedAlpha2 : RepresentsPrepared preparedAlpha2 alpha2)
    (halpha2Exact : generatedQm31ToExact alpha2 = generatedQm31ToExact alpha ^ 2)
    (halpha3Exact : generatedQm31ToExact alpha3 = generatedQm31ToExact alpha ^ 3) :
    ∃ scaleOut factorsOut factorExact,
      V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.fold_tensor_arity4
          scale factors alpha3 preparedAlpha preparedAlpha2 =
        ok (scaleOut, factorsOut) ∧
      GeneratedCanonicalQM31 scaleOut ∧
      CanonicalList factorsOut.val ∧
      factorsOut.val = factors.val.take m ∧
      generatedQm31ToExact scaleOut =
        generatedQm31ToExact scale * factorExact ∧
      factorExact * (4 : ExactQM31) =
        tensorDualNumerator (generatedQm31ToExact alpha)
          (generatedQm31ToExact factors.val[m]!)
          (generatedQm31ToExact factors.val[m + 1]!) := by
  let split := Std.Usize.wrapping_sub (alloc.vec.Vec.len factors) 2#usize
  have hlen : (alloc.vec.Vec.len factors).val = m + 2 := by
    rw [alloc.vec.Vec.len_val]
    exact hfactorsLength
  have hsplit : split.val = m := by
    unfold split
    exact wrappingSubTwoExact (alloc.vec.Vec.len factors) m hlen hm
  let next := Std.Usize.wrapping_add split 1#usize
  have hnext : next.val = m + 1 := by
    unfold next
    exact wrappingAddOneExact split m hsplit hm
  have hsplitBound : split.val < factors.val.length := by omega
  have hnextBound : next.val < factors.val.length := by omega
  have highRead := vecIndexRun factors split hsplitBound
  have lowRead := vecIndexRun factors next hnextBound
  let high := factors.val[split.val]
  let low := factors.val[next.val]
  have highCanonical : GeneratedCanonicalQM31 high :=
    hfactors high (List.getElem_mem hsplitBound)
  have lowCanonical : GeneratedCanonicalQM31 low :=
    hfactors low (List.getElem_mem hnextBound)
  have hmBound : m < factors.val.length := by omega
  have hm1Bound : m + 1 < factors.val.length := by omega
  have highBang : high = listCell factors.val m := by
    simp only [high, listCell, hsplit,
      List.getElem?_eq_getElem hmBound, Option.getD_some]
  have lowBang : low = listCell factors.val (m + 1) := by
    simp only [low, listCell, hnext,
      List.getElem?_eq_getElem hm1Bound, Option.getD_some]
  obtain ⟨pqm, pqmRun, pqmRepresents⟩ :=
    generated_prepared_new_establishes low lowCanonical
  have preparedAlphaRun :=
    representsPreparedNewRun preparedAlpha alpha hpreparedAlpha
  obtain ⟨qPrepared, q, qPreparedRun, qRun, qCanonical, qExact⟩ :=
    generated_prepared_qm31_mul_corresponds alpha high halpha highCanonical
  have qPreparedExact : qPrepared = preparedAlpha := by
    exact Result.ok.inj (qPreparedRun.symm.trans preparedAlphaRun)
  subst qPrepared
  obtain ⟨q1, q1Run, q1Canonical, q1Exact⟩ :=
    generated_qm31_add_corresponds alpha3 q halpha3 qCanonical
  let preparedPair : Array RawPrepared 2#usize :=
    Array.make 2#usize [preparedAlpha2, pqm]
  let leftPair : Array RawQM31 2#usize :=
    Array.make 2#usize [alpha2, low]
  let rightPair : Array RawQM31 2#usize :=
    Array.make 2#usize [high, q1]
  have preparedPairFor : PreparedArrayFor preparedPair leftPair := by
    intro index hindex
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with rfl | rfl
    · change PreparedFor preparedAlpha2 alpha2
      exact representsPrepared_implies_preparedFor preparedAlpha2 alpha2
        hpreparedAlpha2 halpha2
    · change PreparedFor pqm low
      exact representsPrepared_implies_preparedFor pqm low pqmRepresents
        lowCanonical
  have rightPairCanonical : GeneratedCanonicalQM31Array2 rightPair := by
    intro index hindex
    have hi : index = 0 ∨ index = 1 := by omega
    rcases hi with rfl | rfl
    · change GeneratedCanonicalQM31 high
      exact highCanonical
    · change GeneratedCanonicalQM31 q1
      exact q1Canonical
  obtain ⟨products, productsRun, productsCanonical, productsExact⟩ :=
    generated_sum_products2_prepared_corresponds preparedPair leftPair
      rightPair preparedPairFor rightPairCanonical
  let one := V7CallerCurrentReleaseR26.field.QM31.ONE
  obtain ⟨q2, q2Run, q2Canonical, q2Exact⟩ :=
    generated_qm31_add_corresponds one products oneCanonical
      productsCanonical
  obtain ⟨q3, q3Run, q3Canonical, q3Exact⟩ :=
    generated_qm31_half_corresponds q2 q2Canonical
  obtain ⟨factor, factorRun, factorCanonical, factorExact⟩ :=
    generated_qm31_half_corresponds q3 q3Canonical
  obtain ⟨scaleOut, scaleRun, scaleCanonical, scaleExact⟩ :=
    generated_qm31_mul_corresponds scale factor hscale factorCanonical
  let factorsOut : alloc.vec.Vec RawQM31 :=
    ⟨factors.val.take split.val,
      Nat.le_trans (List.length_take_le' ..) factors.property⟩
  refine ⟨scaleOut, factorsOut, generatedQm31ToExact factor,
    ?_, scaleCanonical, ?_, ?_, scaleExact, ?_⟩
  · unfold
      V7CallerCurrentReleaseR26.sumcheck.WeightAccumulator.impl.fold_tensor_arity4
    simp only [Std.lift, bind_tc_ok]
    change (do
      let high1 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) factors split
      let low1 ← alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice RawQM31) factors next
      let pqm1 ←
        V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.impl.new
          low1
      let q1a ←
        V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.impl.mul
          preparedAlpha high1
      let q1b ←
        V7CallerCurrentReleaseR26.field.QM31.add alpha3 q1a
      let products1 ←
        V7CallerCurrentReleaseR26.field.qm31_sum_products2_prepared
          (Array.make 2#usize [preparedAlpha2, pqm1])
          (Array.make 2#usize [high1, q1b])
      let q2a ← V7CallerCurrentReleaseR26.field.QM31.add one products1
      let q3a ← V7CallerCurrentReleaseR26.field.QM31.half q2a
      let factor1 ← V7CallerCurrentReleaseR26.field.QM31.half q3a
      let scale1 ←
        V7CallerCurrentReleaseR26.field.QM31.mul scale factor1
      let factors1 ← alloc.vec.Vec.truncate Global factors split
      ok (scale1, factors1)) = ok (scaleOut, factorsOut)
    rw [highRead, lowRead]
    simp only [bind_tc_ok]
    change (do
      let pqm1 ←
        V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.impl.new
          low
      let q1a ←
        V7CallerCurrentReleaseR26.field.PreparedQm31Multiplier.impl.mul
          preparedAlpha high
      let q1b ←
        V7CallerCurrentReleaseR26.field.QM31.add alpha3 q1a
      let products1 ←
        V7CallerCurrentReleaseR26.field.qm31_sum_products2_prepared
          (Array.make 2#usize [preparedAlpha2, pqm1])
          (Array.make 2#usize [high, q1b])
      let q2a ← V7CallerCurrentReleaseR26.field.QM31.add one products1
      let q3a ← V7CallerCurrentReleaseR26.field.QM31.half q2a
      let factor1 ← V7CallerCurrentReleaseR26.field.QM31.half q3a
      let scale1 ←
        V7CallerCurrentReleaseR26.field.QM31.mul scale factor1
      let factors1 ← alloc.vec.Vec.truncate Global factors split
      ok (scale1, factors1)) = ok (scaleOut, factorsOut)
    rw [pqmRun]
    simp only [bind_tc_ok]
    rw [qRun]
    simp only [bind_tc_ok]
    rw [q1Run]
    simp only [bind_tc_ok]
    change (do
      let products1 ←
        V7CallerCurrentReleaseR26.field.qm31_sum_products2_prepared
          preparedPair rightPair
      let q2a ← V7CallerCurrentReleaseR26.field.QM31.add one products1
      let q3a ← V7CallerCurrentReleaseR26.field.QM31.half q2a
      let factor1 ← V7CallerCurrentReleaseR26.field.QM31.half q3a
      let scale1 ←
        V7CallerCurrentReleaseR26.field.QM31.mul scale factor1
      let factors1 ← alloc.vec.Vec.truncate Global factors split
      ok (scale1, factors1)) = ok (scaleOut, factorsOut)
    rw [productsRun]
    simp only [bind_tc_ok]
    rw [q2Run]
    simp only [bind_tc_ok]
    rw [q3Run]
    simp only [bind_tc_ok]
    rw [factorRun]
    simp only [bind_tc_ok]
    rw [scaleRun]
    rfl
  · unfold factorsOut
    apply takeCanonical factors.val split.val hfactors
  · simp [factorsOut, hsplit]
  · have leftPairVal : leftPair.val = [alpha2, low] := by rfl
    have rightPairVal : rightPair.val = [high, q1] := by rfl
    have productFormula :
        generatedQm31ToExact products =
          generatedQm31ToExact alpha2 * generatedQm31ToExact high +
            generatedQm31ToExact low * generatedQm31ToExact q1 := by
      rw [productsExact]
      unfold exactProductDot
      rw [leftPairVal, rightPairVal]
      simp [Finset.sum_range_succ]
    simp [tensorDualNumerator, tensorFibreWeights]
    calc
      generatedQm31ToExact factor * 4 =
          (generatedQm31ToExact factor + generatedQm31ToExact factor) +
            (generatedQm31ToExact factor + generatedQm31ToExact factor) := by ring
      _ = generatedQm31ToExact q3 + generatedQm31ToExact q3 := by
        rw [factorExact]
      _ = generatedQm31ToExact q2 := q3Exact
      _ = 1 + generatedQm31ToExact products := by
        rw [q2Exact, oneExact]
      _ = 1 +
          (generatedQm31ToExact alpha2 * generatedQm31ToExact high +
            generatedQm31ToExact low * generatedQm31ToExact q1) := by
        rw [productFormula]
      _ = 1 +
          (generatedQm31ToExact alpha ^ 2 * generatedQm31ToExact high +
            generatedQm31ToExact low *
              (generatedQm31ToExact alpha ^ 3 +
                generatedQm31ToExact alpha * generatedQm31ToExact high)) := by
        rw [q1Exact, qExact, halpha2Exact, halpha3Exact]
      _ = 1 + generatedQm31ToExact alpha ^ 3 * generatedQm31ToExact low +
          generatedQm31ToExact alpha ^ 2 * generatedQm31ToExact high +
          generatedQm31ToExact alpha *
            (generatedQm31ToExact high * generatedQm31ToExact low) := by ring
      _ = 1 + generatedQm31ToExact alpha ^ 3 *
              generatedQm31ToExact (listCell factors.val (m + 1)) +
            generatedQm31ToExact alpha ^ 2 *
              generatedQm31ToExact (listCell factors.val m) +
            generatedQm31ToExact alpha *
              (generatedQm31ToExact (listCell factors.val m) *
                generatedQm31ToExact (listCell factors.val (m + 1))) := by
        rw [highBang, lowBang]

#print axioms fold_tensor_arity4_exact

end V7CallerCurrentReleaseR26TensorFoldSemantics
