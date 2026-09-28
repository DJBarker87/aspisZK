import V7CallerCurrentReleaseR26AcceptedTailSemantics
import V7CallerCurrentReleaseR26PreparedSumSemantics

/-!
# Exact call trace of the optimized Tag-73 relation-tail weight fold

The production helper performs the first deferred fold, merges equal
multilinear components, prepares the next two challenges, and traverses every
remaining component with the fused two-round loop.  This file inverts a
successful `true` result into those literal source calls so the component
semantics can be proved without unfolding the public wrapper again.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26TailWeightFoldTrace

open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26PreparedSumSemantics

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev RawComponents := alloc.vec.Vec sumcheck.WeightComponent

/-- Every intermediate source value in one accepted optimized tail fold. -/
structure AcceptedTailWeightFoldTrace
    (input : RawWeights) (alphas : Array RawQM31 3#usize)
    (output : RawWeights) : Type where
  alpha0 : RawQM31
  afterFirst : RawWeights
  afterMerge : RawWeights
  alpha1 : RawQM31
  alpha1Squared : RawQM31
  alpha2 : RawQM31
  alpha2Squared : RawQM31
  preparedAlpha1 : RawPrepared
  preparedAlpha2 : RawPrepared
  preparedAlpha1Squared : RawPrepared
  preparedAlpha2Squared : RawPrepared
  alpha1Cubed : RawQM31
  alpha2Cubed : RawQM31
  finalLogLen : Std.U32
  finalComponents : RawComponents
  inputLogLen : input.log_len = 8#u32
  alpha0Read : alphas.index_usize 0#usize = ok alpha0
  firstFoldRun :
    sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4
      input alpha0 = ok afterFirst
  mergeRun :
    sumcheck.WeightAccumulator.impl.merge_equal_multilinear_components
      afterFirst 0#usize 2#usize = ok (true, afterMerge)
  alpha1Read : alphas.index_usize 1#usize = ok alpha1
  alpha1SquareRun : field.QM31.square alpha1 = ok alpha1Squared
  alpha2Read : alphas.index_usize 2#usize = ok alpha2
  alpha2SquareRun : field.QM31.square alpha2 = ok alpha2Squared
  prepareAlpha1Run :
    field.PreparedQm31Multiplier.impl.new alpha1 = ok preparedAlpha1
  prepareAlpha2Run :
    field.PreparedQm31Multiplier.impl.new alpha2 = ok preparedAlpha2
  prepareAlpha1SquaredRun :
    field.PreparedQm31Multiplier.impl.new alpha1Squared =
      ok preparedAlpha1Squared
  prepareAlpha2SquaredRun :
    field.PreparedQm31Multiplier.impl.new alpha2Squared =
      ok preparedAlpha2Squared
  alpha1CubedRun :
    field.PreparedQm31Multiplier.impl.mul preparedAlpha1 alpha1Squared =
      ok alpha1Cubed
  alpha2CubedRun :
    field.PreparedQm31Multiplier.impl.mul preparedAlpha2 alpha2Squared =
      ok alpha2Cubed
  traversalRun :
    sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop
      afterMerge alphas
      (Array.make 2#usize [alpha1Squared, alpha2Squared])
      (Array.make 2#usize [preparedAlpha1, preparedAlpha2])
      (Array.make 2#usize [preparedAlpha1Squared, preparedAlpha2Squared])
      (Array.make 2#usize [alpha1Cubed, alpha2Cubed]) 0#usize =
        ok (finalLogLen, finalComponents, true)
  outputExact : output = {
    log_len := finalLogLen
    components := finalComponents }

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- Inversion of a successful public optimized tail-fold call.  In
particular, `true` rules out the wrong-log, failed-merge, and unsupported
component branches. -/
theorem accepted_tail_weight_fold_exposes_trace
    (input : RawWeights) (alphas : Array RawQM31 3#usize)
    (output : RawWeights)
    (run :
      sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4
        input alphas = ok (true, output)) :
    Nonempty (AcceptedTailWeightFoldTrace input alphas output) := by
  unfold sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4 at run
  by_cases wrongLog : input.log_len != 8#u32
  · rw [if_pos wrongLog] at run
    cases Result.ok.inj run
  · rw [if_neg wrongLog] at run
    have inputLog : input.log_len = 8#u32 := by
      apply UScalar.val_eq_imp
      simpa using wrongLog
    rw [bind_eq_ok_iff] at run
    obtain ⟨alpha0, alpha0Read, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨afterFirst, firstFoldRun, run⟩ := run
    rw [bind_eq_ok_iff] at run
    obtain ⟨mergePair, mergeCall, run⟩ := run
    rcases mergePair with ⟨merged, afterMerge⟩
    cases merged with
    | false =>
        simp at run
    | true =>
        simp only [↓reduceIte] at run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha1, alpha1Read, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha1Squared, alpha1SquareRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha2, alpha2Read, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha2Squared, alpha2SquareRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨preparedAlpha1, prepareAlpha1Run, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨preparedAlpha2, prepareAlpha2Run, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha1SquaredRead, alpha1SquaredReadRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨preparedAlpha1Squared, prepareAlpha1SquaredRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha2SquaredRead, alpha2SquaredReadRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨preparedAlpha2Squared, prepareAlpha2SquaredRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨preparedAlpha1Read, preparedAlpha1ReadRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha1Cubed, alpha1CubedRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨preparedAlpha2Read, preparedAlpha2ReadRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨alpha2Cubed, alpha2CubedRun, run⟩ := run
        rw [bind_eq_ok_iff] at run
        obtain ⟨traversalOutput, traversalRun, run⟩ := run
        rcases traversalOutput with ⟨finalLogLen, finalComponents, accepted⟩
        simp only [Aeneas.Std.Result.ok.injEq, Prod.mk.injEq] at run
        rcases run with ⟨acceptedExact, outputEq⟩
        have acceptedTrue : accepted = true := acceptedExact
        subst accepted
        have alpha1SquaredReadExact : alpha1SquaredRead = alpha1Squared := by
          simpa [Array.index_usize] using
            (Result.ok.inj alpha1SquaredReadRun).symm
        subst alpha1SquaredRead
        have alpha2SquaredReadExact : alpha2SquaredRead = alpha2Squared := by
          simpa [Array.index_usize] using
            (Result.ok.inj alpha2SquaredReadRun).symm
        subst alpha2SquaredRead
        have preparedAlpha1ReadExact : preparedAlpha1Read = preparedAlpha1 := by
          simpa [Array.index_usize] using
            (Result.ok.inj preparedAlpha1ReadRun).symm
        subst preparedAlpha1Read
        have preparedAlpha2ReadExact : preparedAlpha2Read = preparedAlpha2 := by
          simpa [Array.index_usize] using
            (Result.ok.inj preparedAlpha2ReadRun).symm
        subst preparedAlpha2Read
        exact ⟨{
          alpha0 := alpha0
          afterFirst := afterFirst
          afterMerge := afterMerge
          alpha1 := alpha1
          alpha1Squared := alpha1Squared
          alpha2 := alpha2
          alpha2Squared := alpha2Squared
          preparedAlpha1 := preparedAlpha1
          preparedAlpha2 := preparedAlpha2
          preparedAlpha1Squared := preparedAlpha1Squared
          preparedAlpha2Squared := preparedAlpha2Squared
          alpha1Cubed := alpha1Cubed
          alpha2Cubed := alpha2Cubed
          finalLogLen := finalLogLen
          finalComponents := finalComponents
          inputLogLen := inputLog
          alpha0Read := alpha0Read
          firstFoldRun := firstFoldRun
          mergeRun := mergeCall
          alpha1Read := alpha1Read
          alpha1SquareRun := alpha1SquareRun
          alpha2Read := alpha2Read
          alpha2SquareRun := alpha2SquareRun
          prepareAlpha1Run := prepareAlpha1Run
          prepareAlpha2Run := prepareAlpha2Run
          prepareAlpha1SquaredRun := prepareAlpha1SquaredRun
          prepareAlpha2SquaredRun := prepareAlpha2SquaredRun
          alpha1CubedRun := alpha1CubedRun
          alpha2CubedRun := alpha2CubedRun
          traversalRun := traversalRun
          outputExact := outputEq.symm }⟩

/-- Canonicality, exact powers, and cache meanings supplied to the fused
two-round traversal by an accepted public call. -/
structure TailWeightFoldPowerFacts
    {input : RawWeights} {alphas : Array RawQM31 3#usize}
    {output : RawWeights}
    (trace : AcceptedTailWeightFoldTrace input alphas output) : Prop where
  alpha1SquaredCanonical : GeneratedCanonicalQM31 trace.alpha1Squared
  alpha2SquaredCanonical : GeneratedCanonicalQM31 trace.alpha2Squared
  alpha1CubedCanonical : GeneratedCanonicalQM31 trace.alpha1Cubed
  alpha2CubedCanonical : GeneratedCanonicalQM31 trace.alpha2Cubed
  alpha1SquaredExact :
    generatedQm31ToExact trace.alpha1Squared =
      generatedQm31ToExact trace.alpha1 ^ 2
  alpha2SquaredExact :
    generatedQm31ToExact trace.alpha2Squared =
      generatedQm31ToExact trace.alpha2 ^ 2
  alpha1CubedExact :
    generatedQm31ToExact trace.alpha1Cubed =
      generatedQm31ToExact trace.alpha1 ^ 3
  alpha2CubedExact :
    generatedQm31ToExact trace.alpha2Cubed =
      generatedQm31ToExact trace.alpha2 ^ 3
  preparedAlpha1Represents :
    RepresentsPrepared trace.preparedAlpha1 trace.alpha1
  preparedAlpha2Represents :
    RepresentsPrepared trace.preparedAlpha2 trace.alpha2
  preparedAlpha1SquaredRepresents :
    RepresentsPrepared trace.preparedAlpha1Squared trace.alpha1Squared
  preparedAlpha2SquaredRepresents :
    RepresentsPrepared trace.preparedAlpha2Squared trace.alpha2Squared

/-- The wrapper's literal square/cache/multiply calls have their exact field
meaning; no arithmetic fact is left as a premise of the component traversal. -/
theorem AcceptedTailWeightFoldTrace.power_facts
    {input : RawWeights} {alphas : Array RawQM31 3#usize}
    {output : RawWeights}
    (trace : AcceptedTailWeightFoldTrace input alphas output)
    (halpha1 : GeneratedCanonicalQM31 trace.alpha1)
    (halpha2 : GeneratedCanonicalQM31 trace.alpha2) :
    TailWeightFoldPowerFacts trace := by
  obtain ⟨alpha1SquaredExpected, alpha1SquareExpected,
      alpha1SquaredCanonical, alpha1SquaredExact⟩ :=
    generated_qm31_square_corresponds trace.alpha1 halpha1
  have alpha1SquaredEq : trace.alpha1Squared = alpha1SquaredExpected :=
    Result.ok.inj
      (trace.alpha1SquareRun.symm.trans alpha1SquareExpected)
  subst alpha1SquaredExpected
  obtain ⟨alpha2SquaredExpected, alpha2SquareExpected,
      alpha2SquaredCanonical, alpha2SquaredExact⟩ :=
    generated_qm31_square_corresponds trace.alpha2 halpha2
  have alpha2SquaredEq : trace.alpha2Squared = alpha2SquaredExpected :=
    Result.ok.inj
      (trace.alpha2SquareRun.symm.trans alpha2SquareExpected)
  subst alpha2SquaredExpected
  obtain ⟨preparedAlpha1Expected, preparedAlpha1Run,
      preparedAlpha1Represents⟩ :=
    generated_prepared_new_establishes trace.alpha1 halpha1
  have preparedAlpha1Eq : trace.preparedAlpha1 = preparedAlpha1Expected :=
    Result.ok.inj (trace.prepareAlpha1Run.symm.trans preparedAlpha1Run)
  subst preparedAlpha1Expected
  obtain ⟨preparedAlpha2Expected, preparedAlpha2Run,
      preparedAlpha2Represents⟩ :=
    generated_prepared_new_establishes trace.alpha2 halpha2
  have preparedAlpha2Eq : trace.preparedAlpha2 = preparedAlpha2Expected :=
    Result.ok.inj (trace.prepareAlpha2Run.symm.trans preparedAlpha2Run)
  subst preparedAlpha2Expected
  obtain ⟨preparedAlpha1SquaredExpected, preparedAlpha1SquaredRun,
      preparedAlpha1SquaredRepresents⟩ :=
    generated_prepared_new_establishes trace.alpha1Squared
      alpha1SquaredCanonical
  have preparedAlpha1SquaredEq :
      trace.preparedAlpha1Squared = preparedAlpha1SquaredExpected :=
    Result.ok.inj
      (trace.prepareAlpha1SquaredRun.symm.trans preparedAlpha1SquaredRun)
  subst preparedAlpha1SquaredExpected
  obtain ⟨preparedAlpha2SquaredExpected, preparedAlpha2SquaredRun,
      preparedAlpha2SquaredRepresents⟩ :=
    generated_prepared_new_establishes trace.alpha2Squared
      alpha2SquaredCanonical
  have preparedAlpha2SquaredEq :
      trace.preparedAlpha2Squared = preparedAlpha2SquaredExpected :=
    Result.ok.inj
      (trace.prepareAlpha2SquaredRun.symm.trans preparedAlpha2SquaredRun)
  subst preparedAlpha2SquaredExpected
  obtain ⟨alpha1CubedCanonical, alpha1CubedMulExact⟩ :=
    generated_prepared_qm31_mul_exact trace.alpha1 trace.alpha1Squared
      trace.alpha1Cubed trace.preparedAlpha1 halpha1 alpha1SquaredCanonical
      trace.prepareAlpha1Run trace.alpha1CubedRun
  obtain ⟨alpha2CubedCanonical, alpha2CubedMulExact⟩ :=
    generated_prepared_qm31_mul_exact trace.alpha2 trace.alpha2Squared
      trace.alpha2Cubed trace.preparedAlpha2 halpha2 alpha2SquaredCanonical
      trace.prepareAlpha2Run trace.alpha2CubedRun
  have alpha1CubedExact : generatedQm31ToExact trace.alpha1Cubed =
      generatedQm31ToExact trace.alpha1 ^ 3 := by
    rw [alpha1CubedMulExact, alpha1SquaredExact]
    ring
  have alpha2CubedExact : generatedQm31ToExact trace.alpha2Cubed =
      generatedQm31ToExact trace.alpha2 ^ 3 := by
    rw [alpha2CubedMulExact, alpha2SquaredExact]
    ring
  exact {
    alpha1SquaredCanonical := alpha1SquaredCanonical
    alpha2SquaredCanonical := alpha2SquaredCanonical
    alpha1CubedCanonical := alpha1CubedCanonical
    alpha2CubedCanonical := alpha2CubedCanonical
    alpha1SquaredExact := alpha1SquaredExact
    alpha2SquaredExact := alpha2SquaredExact
    alpha1CubedExact := alpha1CubedExact
    alpha2CubedExact := alpha2CubedExact
    preparedAlpha1Represents := preparedAlpha1Represents
    preparedAlpha2Represents := preparedAlpha2Represents
    preparedAlpha1SquaredRepresents := preparedAlpha1SquaredRepresents
    preparedAlpha2SquaredRepresents := preparedAlpha2SquaredRepresents }

#print axioms accepted_tail_weight_fold_exposes_trace
#print axioms AcceptedTailWeightFoldTrace.power_facts

end V7CallerCurrentReleaseR26TailWeightFoldTrace
