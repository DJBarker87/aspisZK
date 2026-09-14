import V7CallerCurrentReleaseLiveAccumulator

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace V7CallerCurrentReleasePrequeryDot256Source

open V7CallerCurrentReleaseFieldBridge

abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseFieldBridge.ExactQM31
abbrev Accumulator := V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator

instance : Inhabited QM31 := ⟨V7CallerCurrentReleaseR20.field.QM31.ZERO⟩

def dotPrefix (coefficient weight : Nat → ExactQM31)
    (processed : Nat) : ExactQM31 :=
  ∑ i ∈ Finset.range processed, coefficient i * weight i

def DotInvariant (coefficient weight : Nat → ExactQM31)
    (sum : QM31) (processed : Nat) : Prop :=
  GeneratedCanonicalQM31 sum ∧
    generatedQm31ToExact sum = dotPrefix coefficient weight processed

private theorem array_index_run {T : Type} [Inhabited T] {n : Std.Usize}
    (values : Array T n) (index : Std.Usize) (hIndex : index.val < n.val) :
    Array.index_usize values index = ok values.val[index.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (Array.index_usize_spec values index (by
      simpa [Array.length_eq] using hIndex))
  have hActual : index.val < values.val.length := by
    simpa [Array.length_eq] using hIndex
  have hList : values.val[index.val] = values.val[index.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using hActual
  simpa [hvalue, hList] using hrun

private theorem cast_usize_u32_val (value : Std.Usize)
    (hValue : value.val < 2 ^ 32) :
    (UScalar.cast .U32 value).val = value.val := by
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
  simpa using hValue

private theorem body_done (weights : Accumulator)
    (coefficients : Array QM31 256#usize) (sum : QM31)
    (position : Std.Usize) (hDone : ¬ position.val < 256) :
    V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256_loop.body
        weights coefficients sum position = ok (done sum) := by
  unfold V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256_loop.body
  unfold V7CallerCurrentReleaseR20.v6_onefold.V6_FINAL_QM31_VALUES
  rw [if_neg]
  simpa using hDone

private theorem body_active
    (weights : Accumulator) (coefficients : Array QM31 256#usize)
    (coefficient weight : Nat → ExactQM31) (sum : QM31)
    (position : Std.Usize) (hActive : position.val < 256)
    (hCoefficientCanonical : ∀ i, i < 256 →
      GeneratedCanonicalQM31 coefficients.val[i]!)
    (hCoefficientExact : ∀ i, i < 256 →
      generatedQm31ToExact coefficients.val[i]! = coefficient i)
    (hWeight : ∀ i : Std.U32, i.val < 256 → ∃ raw,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at weights i = ok raw ∧
      GeneratedCanonicalQM31 raw ∧ generatedQm31ToExact raw = weight i.val)
    (hInvariant : DotInvariant coefficient weight sum position.val) :
    ∃ nextSum nextPosition,
      V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256_loop.body
          weights coefficients sum position = ok (cont (nextSum, nextPosition)) ∧
      nextPosition.val = position.val + 1 ∧
      DotInvariant coefficient weight nextSum nextPosition.val := by
  have hRead := array_index_run coefficients position (by simpa using hActive)
  let position32 := UScalar.cast .U32 position
  have hPosition32 : position32.val = position.val := by
    apply cast_usize_u32_val
    omega
  obtain ⟨weightRaw, hWeightRun, hWeightCanonical, hWeightExact⟩ :=
    hWeight position32 (by rw [hPosition32]; exact hActive)
  obtain ⟨product, hProductRun, hProductCanonical, hProductExact⟩ :=
    generated_qm31_mul_corresponds coefficients.val[position.val]!
      weightRaw (hCoefficientCanonical position.val hActive) hWeightCanonical
  obtain ⟨nextSum, hAddRun, hNextCanonical, hNextExact⟩ :=
    generated_qm31_add_corresponds sum product hInvariant.1 hProductCanonical
  let nextPosition := Std.Usize.wrapping_add position 1#usize
  have hNextVal : nextPosition.val = position.val + 1 := by
    dsimp only [nextPosition]
    rw [Std.Usize.wrapping_add_val_eq]
    norm_num
    apply Nat.mod_eq_of_lt
    have hSmall : position.val + 1 < 257 := by omega
    apply lt_trans hSmall
    rw [Usize.size, Usize.numBits, UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> norm_num
  refine ⟨nextSum, nextPosition, ?_, hNextVal, hNextCanonical, ?_⟩
  · unfold V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256_loop.body
    unfold V7CallerCurrentReleaseR20.v6_onefold.V6_FINAL_QM31_VALUES
    rw [if_pos (by simpa using hActive), hRead]
    simp only [bind_tc_ok, Std.lift]
    change
      (V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at weights position32 >>= _)
        = _
    rw [hWeightRun]
    simp only [bind_tc_ok]
    rw [hProductRun]
    simp only [bind_tc_ok]
    rw [hAddRun]
    simp only [bind_tc_ok, Std.lift]
    rfl
  · rw [hNextExact, hInvariant.2, hProductExact,
      hCoefficientExact position.val hActive, hWeightExact, hPosition32,
      hNextVal]
    simp [dotPrefix, Finset.sum_range_succ]

/-- The literal current-source 256-entry loop computes the exact finite dot
    product once its current `weight_at` consumer and coefficient decoding are
    supplied.  The proof is symbolic in the prefix length and never unfolds
    256 copies of the field-expression graph. -/
theorem generated_prequery_dot_256_corresponds
    (weights : Accumulator) (coefficients : Array QM31 256#usize)
    (coefficient weight : Nat → ExactQM31)
    (hCoefficientCanonical : ∀ i, i < 256 →
      GeneratedCanonicalQM31 coefficients.val[i]!)
    (hCoefficientExact : ∀ i, i < 256 →
      generatedQm31ToExact coefficients.val[i]! = coefficient i)
    (hWeight : ∀ i : Std.U32, i.val < 256 → ∃ raw,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at weights i = ok raw ∧
      GeneratedCanonicalQM31 raw ∧ generatedQm31ToExact raw = weight i.val) :
    V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256 weights coefficients
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out = dotPrefix coefficient weight 256 ⦄ := by
  simp only [V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256,
    V7CallerCurrentReleaseR20.v6_transcript.prequery_dot_256_loop]
  apply loop.spec_decr_nat
    (fun state : QM31 × Std.Usize => 256 - state.2.val)
    (fun state => state.2.val ≤ 256 ∧
      DotInvariant coefficient weight state.1 state.2.val)
    (fun out => GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = dotPrefix coefficient weight 256)
  · rintro ⟨sum, position⟩ ⟨hLe, hInvariant⟩
    dsimp only at hLe hInvariant ⊢
    by_cases hActive : position.val < 256
    · obtain ⟨nextSum, nextPosition, hBody, hNext, hNextInvariant⟩ :=
        body_active weights coefficients coefficient weight sum position hActive
          hCoefficientCanonical hCoefficientExact hWeight hInvariant
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, hNextInvariant⟩, ?_⟩ <;> rw [hNext] <;> omega
    · have hEnd : position.val = 256 := by omega
      rw [body_done weights coefficients sum position hActive]
      simpa [hEnd, DotInvariant] using hInvariant
  · constructor
    · norm_num
    · constructor
      · norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
          AspisAeneasCM31Multiplicative.CanonicalRawM31,
          V7CallerCurrentReleaseR20.field.QM31.ZERO]
      · apply QuadraticAlgebra.ext
        · apply QuadraticAlgebra.ext <;>
            simp [dotPrefix, generatedQm31ToExact, generatedCm31ToExact,
              V7CallerCurrentReleaseR20.field.QM31.ZERO]
        · apply QuadraticAlgebra.ext <;>
            simp [dotPrefix, generatedQm31ToExact, generatedCm31ToExact,
              V7CallerCurrentReleaseR20.field.QM31.ZERO]

#print axioms generated_prequery_dot_256_corresponds

end V7CallerCurrentReleasePrequeryDot256Source
