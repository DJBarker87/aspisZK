import V7CallerCurrentReleaseLiveComponents

open Aeneas Aeneas.Std Result ControlFlow Error
open scoped BigOperators

namespace V7CallerCurrentReleaseAccumulatorLoop

open V7CallerCurrentReleaseFieldBridge

abbrev QM31 := V7CallerCurrentReleaseR20.field.QM31
abbrev ExactQM31 := V7CallerCurrentReleaseFieldBridge.ExactQM31
abbrev Component := V7CallerCurrentReleaseR20.sumcheck.WeightComponent
abbrev Accumulator := V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator

instance : Inhabited Component :=
  ⟨V7CallerCurrentReleaseR20.sumcheck.WeightComponent.Geometric
    V7CallerCurrentReleaseR20.field.QM31.ZERO V7CallerCurrentReleaseR20.field.QM31.ZERO⟩

def exactPrefix (semantic : Nat → ExactQM31) (processed : Nat) : ExactQM31 :=
  ∑ componentIndex ∈ Finset.range processed, semantic componentIndex

def ComponentRun (logLen : Std.U32) (index : Std.U32)
    (component : Component) (semantic : ExactQM31) : Prop :=
  ∃ raw,
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed
        logLen component index = ok raw ∧
    GeneratedCanonicalQM31 raw ∧ generatedQm31ToExact raw = semantic

def AccumulatorInvariant (semantic : Nat → ExactQM31)
    (total : QM31) (processed : Nat) : Prop :=
  GeneratedCanonicalQM31 total ∧
    generatedQm31ToExact total = exactPrefix semantic processed

private theorem vec_index_run {T : Type} [Inhabited T]
    (values : alloc.vec.Vec T) (position : Std.Usize)
    (hPosition : position.val < values.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice T)
        values position = ok values.val[position.val]! := by
  obtain ⟨value, hrun, hvalue⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec values position (by simpa using hPosition))
  have hList : values.val[position.val] = values.val[position.val]! := by
    symm
    apply List.getElem!_of_getElem?
    simpa using hPosition
  rw [alloc.vec.Vec.index_slice_index]
  simpa [hvalue, hList] using hrun

private theorem body_done (self : Accumulator) (index : Std.U32)
    (total : QM31) (position : Std.Usize)
    (hDone : ¬ position.val < self.components.length) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_loop.body
        self index total position = ok (done total) := by
  unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_loop.body
  simp only [alloc.vec.Vec.len_val]
  rw [if_neg]
  simpa using hDone

private theorem body_active
    (self : Accumulator) (index : Std.U32) (semantic : Nat → ExactQM31)
    (total : QM31) (position : Std.Usize)
    (hActive : position.val < self.components.length)
    (hComponents : ∀ componentIndex,
      componentIndex < self.components.length →
      ComponentRun self.log_len index self.components.val[componentIndex]!
        (semantic componentIndex))
    (hInvariant : AccumulatorInvariant semantic total position.val) :
    ∃ nextTotal nextPosition,
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_loop.body
          self index total position = ok (cont (nextTotal, nextPosition)) ∧
      nextPosition.val = position.val + 1 ∧
      AccumulatorInvariant semantic nextTotal nextPosition.val := by
  let component := self.components.val[position.val]!
  have hComponentRead :
      alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice Component)
          self.components position = ok component := by
    simpa [component] using vec_index_run self.components position hActive
  obtain ⟨raw, hRawRun, hRawCanonical, hRawExact⟩ :=
    hComponents position.val hActive
  have hRawRun' :
      V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_component_at_indexed
          self.log_len component index = ok raw := by
    simpa [component] using hRawRun
  obtain ⟨nextTotal, hAddRun, hNextCanonical, hNextExact⟩ :=
    generated_qm31_add_corresponds total raw hInvariant.1 hRawCanonical
  let nextPosition := Std.Usize.wrapping_add position 1#usize
  have hPositionBound : position.val + 1 < Usize.size := by
    have hBound := self.components.property
    have hActiveList : position.val < self.components.val.length := by
      simpa using hActive
    simp only [Usize.max, Usize.size, Usize.numBits] at hBound ⊢
    omega
  have hNextVal : nextPosition.val = position.val + 1 := by
    dsimp only [nextPosition]
    rw [Std.Usize.wrapping_add_val_eq]
    norm_num
    exact Nat.mod_eq_of_lt hPositionBound
  refine ⟨nextTotal, nextPosition, ?_, hNextVal, hNextCanonical, ?_⟩
  · unfold V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_loop.body
    simp only [alloc.vec.Vec.len_val]
    rw [if_pos (by simpa using hActive), hComponentRead]
    simp only [bind_tc_ok]
    rw [hRawRun']
    simp only [bind_tc_ok]
    rw [hAddRun]
    simp only [Std.lift, bind_tc_ok]
    rfl
  · rw [hNextExact, hInvariant.2, hRawExact, hNextVal]
    simp [exactPrefix, Finset.sum_range_succ]

/-- Given source-authentic component evaluations, the complete current
    generated `weight_at` loop succeeds, remains canonical, and returns their
    exact ordered sum.  Immediate live-component consumers discharge every
    `ComponentRun` premise from the generated dispatch paths above. -/
theorem generated_accumulator_loop_corresponds
    (self : Accumulator) (index : Std.U32) (semantic : Nat → ExactQM31)
    (hComponents : ∀ componentIndex,
      componentIndex < self.components.length →
      ComponentRun self.log_len index self.components.val[componentIndex]!
        (semantic componentIndex)) :
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at self index
      ⦃ out => GeneratedCanonicalQM31 out ∧
        generatedQm31ToExact out =
          exactPrefix semantic self.components.length ⦄ := by
  simp only [V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at,
    V7CallerCurrentReleaseR20.sumcheck.WeightAccumulator.weight_at_loop]
  apply loop.spec_decr_nat
    (fun state : QM31 × Std.Usize => self.components.length - state.2.val)
    (fun state => state.2.val ≤ self.components.length ∧
      AccumulatorInvariant semantic state.1 state.2.val)
    (fun out => GeneratedCanonicalQM31 out ∧
      generatedQm31ToExact out = exactPrefix semantic self.components.length)
  · rintro ⟨total, position⟩ ⟨hLe, hInvariant⟩
    dsimp only at hLe hInvariant ⊢
    by_cases hActive : position.val < self.components.length
    · obtain ⟨nextTotal, nextPosition, hBody, hNext, hNextInvariant⟩ :=
        body_active self index semantic total position hActive hComponents
          hInvariant
      rw [hBody]
      simp only [Aeneas.Std.WP.spec_ok]
      refine ⟨⟨?_, hNextInvariant⟩, ?_⟩ <;> rw [hNext] <;> omega
    · have hEnd : position.val = self.components.length := by omega
      rw [body_done self index total position hActive]
      simpa [hEnd, AccumulatorInvariant] using hInvariant
  · constructor
    · norm_num
    · constructor
      · norm_num [GeneratedCanonicalQM31, GeneratedCanonicalCM31,
          AspisAeneasCM31Multiplicative.CanonicalRawM31,
          V7CallerCurrentReleaseR20.field.QM31.ZERO]
      · apply QuadraticAlgebra.ext
        · apply QuadraticAlgebra.ext <;>
            simp [exactPrefix, generatedQm31ToExact, generatedCm31ToExact,
              V7CallerCurrentReleaseR20.field.QM31.ZERO]
        · apply QuadraticAlgebra.ext <;>
            simp [exactPrefix, generatedQm31ToExact, generatedCm31ToExact,
              V7CallerCurrentReleaseR20.field.QM31.ZERO]

#print axioms generated_accumulator_loop_corresponds

end V7CallerCurrentReleaseAccumulatorLoop
