import V7CallerCurrentReleaseR26TailWeightFoldTrace
import V7CallerCurrentReleaseR26K1LineBatchFoldBridge

/-!
# Exact finite traces for the current weight-fold loops

The accepted public tail trace retains the first fold and final traversal as
opaque successful calls.  These lemmas invert those two Aeneas fixpoints into
finite chains of literal body equations for component-by-component proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR26WeightFoldLoopTrace

open V7CallerCurrentReleaseR26AcceptedTailTrace
open V7CallerCurrentReleaseR26TailWeightFoldTrace
open V7CallerCurrentReleaseR26FieldBridge
open V7CallerCurrentReleaseR26PreparedSumSemantics

abbrev RawQM31 := field.QM31
abbrev RawPrepared := field.PreparedQm31Multiplier
abbrev RawWeights := sumcheck.WeightAccumulator
abbrev RawComponents := alloc.vec.Vec sumcheck.WeightComponent
abbrev DeferredState := RawComponents × Std.Usize
abbrev TailState := RawWeights × Std.Usize

private theorem bind_eq_ok_iff {Input Output : Type}
    (input : Result Input) (next : Input → Result Output) (output : Output) :
    (do
      let value ← input
      next value) = ok output ↔
      ∃ value, input = ok value ∧ next value = ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- Exact arithmetic setup and finite component trace of the first
log-eight-to-log-six fold. -/
structure FirstDeferredFoldTrace
    (input : RawWeights) (alpha : RawQM31) (output : RawWeights) : Type where
  alphaSquared : RawQM31
  preparedAlpha : RawPrepared
  preparedAlphaSquared : RawPrepared
  alphaCubed : RawQM31
  foldedComponents : RawComponents
  alphaSquareRun : field.QM31.square alpha = ok alphaSquared
  prepareAlphaRun :
    field.PreparedQm31Multiplier.impl.new alpha = ok preparedAlpha
  prepareAlphaSquaredRun :
    field.PreparedQm31Multiplier.impl.new alphaSquared =
      ok preparedAlphaSquared
  alphaCubedRun :
    field.PreparedQm31Multiplier.impl.mul preparedAlpha alphaSquared =
      ok alphaCubed
  componentTrace : ExactLoopTrace
    (fun state : DeferredState =>
      sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
        input.log_len alpha alphaSquared preparedAlpha preparedAlphaSquared
        alphaCubed state.1 state.2)
    (input.components, 0#usize) foldedComponents
  outputLogLen :
    output.log_len = Std.U32.wrapping_sub input.log_len 2#u32
  outputComponents : output.components = foldedComponents

theorem first_deferred_fold_exposes_exact_trace
    {input output : RawWeights} {alpha : RawQM31}
    (run :
      sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4
        input alpha = ok output) :
    Nonempty (FirstDeferredFoldTrace input alpha output) := by
  unfold sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4 at run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alphaSquared, alphaSquareRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨preparedAlpha, prepareAlphaRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨preparedAlphaSquared, prepareAlphaSquaredRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨alphaCubed, alphaCubedRun, run⟩ := run
  rw [bind_eq_ok_iff] at run
  obtain ⟨foldedComponents, componentLoopRun, run⟩ := run
  have outputExact : output = {
      log_len := Std.U32.wrapping_sub input.log_len 2#u32
      components := foldedComponents } := by
    simpa [Std.lift] using Result.ok.inj run.symm
  have trace := loop_success_yields_exact_trace
    (fun state : DeferredState =>
      sumcheck.WeightAccumulator.impl.fold_deferred_relation_arity4_loop.body
        input.log_len alpha alphaSquared preparedAlpha preparedAlphaSquared
        alphaCubed state.1 state.2)
    (input.components, 0#usize) foldedComponents componentLoopRun
  exact ⟨{
    alphaSquared := alphaSquared
    preparedAlpha := preparedAlpha
    preparedAlphaSquared := preparedAlphaSquared
    alphaCubed := alphaCubed
    foldedComponents := foldedComponents
    alphaSquareRun := alphaSquareRun
    prepareAlphaRun := prepareAlphaRun
    prepareAlphaSquaredRun := prepareAlphaSquaredRun
    alphaCubedRun := alphaCubedRun
    componentTrace := Classical.choice trace
    outputLogLen := congrArg (fun value : RawWeights => value.log_len)
      outputExact
    outputComponents := congrArg
      (fun value : RawWeights => value.components) outputExact }⟩

structure FirstDeferredFoldPowerFacts
    {input output : RawWeights} {alpha : RawQM31}
    (trace : FirstDeferredFoldTrace input alpha output) : Prop where
  alphaSquaredCanonical : GeneratedCanonicalQM31 trace.alphaSquared
  alphaCubedCanonical : GeneratedCanonicalQM31 trace.alphaCubed
  alphaSquaredExact : generatedQm31ToExact trace.alphaSquared =
    generatedQm31ToExact alpha ^ 2
  alphaCubedExact : generatedQm31ToExact trace.alphaCubed =
    generatedQm31ToExact alpha ^ 3
  preparedAlphaRepresents : RepresentsPrepared trace.preparedAlpha alpha
  preparedAlphaSquaredRepresents :
    RepresentsPrepared trace.preparedAlphaSquared trace.alphaSquared

/-- The literal setup calls of the first fold prove all square, cube, and
prepared-cache facts used by its component cases. -/
theorem FirstDeferredFoldTrace.power_facts
    {input output : RawWeights} {alpha : RawQM31}
    (trace : FirstDeferredFoldTrace input alpha output)
    (halpha : GeneratedCanonicalQM31 alpha) :
    FirstDeferredFoldPowerFacts trace := by
  obtain ⟨alphaSquaredExpected, alphaSquareExpected,
      alphaSquaredCanonical, alphaSquaredExact⟩ :=
    generated_qm31_square_corresponds alpha halpha
  have alphaSquaredEq : trace.alphaSquared = alphaSquaredExpected :=
    Result.ok.inj (trace.alphaSquareRun.symm.trans alphaSquareExpected)
  subst alphaSquaredExpected
  obtain ⟨preparedAlphaExpected, preparedAlphaRun,
      preparedAlphaRepresents⟩ :=
    generated_prepared_new_establishes alpha halpha
  have preparedAlphaEq : trace.preparedAlpha = preparedAlphaExpected :=
    Result.ok.inj (trace.prepareAlphaRun.symm.trans preparedAlphaRun)
  subst preparedAlphaExpected
  obtain ⟨preparedAlphaSquaredExpected, preparedAlphaSquaredRun,
      preparedAlphaSquaredRepresents⟩ :=
    generated_prepared_new_establishes trace.alphaSquared
      alphaSquaredCanonical
  have preparedAlphaSquaredEq :
      trace.preparedAlphaSquared = preparedAlphaSquaredExpected :=
    Result.ok.inj
      (trace.prepareAlphaSquaredRun.symm.trans preparedAlphaSquaredRun)
  subst preparedAlphaSquaredExpected
  obtain ⟨alphaCubedCanonical, alphaCubedMulExact⟩ :=
    generated_prepared_qm31_mul_exact alpha trace.alphaSquared
      trace.alphaCubed trace.preparedAlpha halpha alphaSquaredCanonical
      trace.prepareAlphaRun trace.alphaCubedRun
  have alphaCubedExact : generatedQm31ToExact trace.alphaCubed =
      generatedQm31ToExact alpha ^ 3 := by
    rw [alphaCubedMulExact, alphaSquaredExact]
    ring
  exact {
    alphaSquaredCanonical := alphaSquaredCanonical
    alphaCubedCanonical := alphaCubedCanonical
    alphaSquaredExact := alphaSquaredExact
    alphaCubedExact := alphaCubedExact
    preparedAlphaRepresents := preparedAlphaRepresents
    preparedAlphaSquaredRepresents := preparedAlphaSquaredRepresents }

/-- The accepted fused traversal is likewise a finite chain from the exact
post-merge accumulator to its returned component vector. -/
theorem accepted_tail_traversal_exposes_exact_trace
    {input : RawWeights} {alphas : Array RawQM31 3#usize}
    {output : RawWeights}
    (trace : AcceptedTailWeightFoldTrace input alphas output) :
    Nonempty (ExactLoopTrace
      (fun state : TailState =>
        sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
          alphas
          (Array.make 2#usize [trace.alpha1Squared, trace.alpha2Squared])
          (Array.make 2#usize [trace.preparedAlpha1, trace.preparedAlpha2])
          (Array.make 2#usize
            [trace.preparedAlpha1Squared, trace.preparedAlpha2Squared])
          (Array.make 2#usize [trace.alpha1Cubed, trace.alpha2Cubed])
          state.1 state.2)
      (trace.afterMerge, 0#usize)
      (trace.finalLogLen, trace.finalComponents, true)) := by
  have traversalRun := trace.traversalRun
  unfold sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop
    at traversalRun
  exact loop_success_yields_exact_trace
    (fun state : TailState =>
      sumcheck.WeightAccumulator.impl.fold_tag73_relation_tail_arity4_loop.body
        alphas
        (Array.make 2#usize [trace.alpha1Squared, trace.alpha2Squared])
        (Array.make 2#usize [trace.preparedAlpha1, trace.preparedAlpha2])
        (Array.make 2#usize
          [trace.preparedAlpha1Squared, trace.preparedAlpha2Squared])
        (Array.make 2#usize [trace.alpha1Cubed, trace.alpha2Cubed])
        state.1 state.2)
    (trace.afterMerge, 0#usize)
    (trace.finalLogLen, trace.finalComponents, true) traversalRun

#print axioms first_deferred_fold_exposes_exact_trace
#print axioms FirstDeferredFoldTrace.power_facts
#print axioms accepted_tail_traversal_exposes_exact_trace

end V7CallerCurrentReleaseR26WeightFoldLoopTrace
